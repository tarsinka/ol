type clause = int list
type cnf_formula = { clauses : clause list; amount_vars : int; amount_clauses : int }

type 'a min_formula =
  | MLit of bool
  | MVar of 'a * int * bool
  | MAnd of 'a * 'a min_formula list * bool
[@@deriving show]

type aig_formula =
  | AIGLit of bool
  | AIGVar of int
  | AIGAnd of int * aig_formula * aig_formula
  | AIGNot of aig_formula

type formula =
  | Lit of bool
  | Var of int * int
  | Not of int * formula
  | And of int * formula list
  | Or of int * formula list

let incr x =
  x := !x + 1;
  !x

let formula_uid = ref 0
let fresh_formula_uid () = incr formula_uid
let reset () = formula_uid := 0

let formula_uid = function
  | Lit true -> -1
  | Lit false -> -2
  | Var (uid, _) | Not (uid, _) | And (uid, _) | Or (uid, _) -> uid

let rec show_min_formula = function
  | MLit true -> "t"
  | MLit false -> "f"
  | MVar (_, vn, pol) ->
      let neg = if pol then "" else "~" in
      neg ^ string_of_int vn
  | MAnd (_, ch, pol) ->
      let sep = if pol then " & " else " | " in
      "(" ^ String.concat sep (List.map show_min_formula ch) ^ ")"

let rec show_aig_formula = function
  | AIGLit true -> "t"
  | AIGLit false -> "f"
  | AIGVar v -> string_of_int v
  | AIGNot s -> "~" ^ show_aig_formula s
  | AIGAnd (_, u, v) -> "(" ^ show_aig_formula u ^ " & " ^ show_aig_formula v ^ ")"

let rec show_formula = function
  | Lit true -> "1"
  | Lit false -> "0"
  | Var (_, vn) -> string_of_int vn
  | Not (_, s) -> "~" ^ show_formula s
  | And (_, ch) -> "(" ^ String.concat " & " (List.map show_formula ch) ^ ")"
  | Or (_, ch) -> "(" ^ String.concat " | " (List.map show_formula ch) ^ ")"

let formula_size s =
  let mem = Hashtbl.create 8 in
  let rec go s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some _ -> 0
    | None ->
        let size =
          match s with
          | Lit _ | Var _ -> 1
          | Not (_, t) -> go t
          | And (_, ch) | Or (_, ch) -> 1 + List.fold_left (fun sum c -> sum + go c) 0 ch
        in
        Hashtbl.replace mem uid size;
        size
  in
  go s

(*
  Returns a list of the identifiers of variable occuring in
  the formula [s].
*)

module Vars = Set.Make (Int)

let vars s =
  let mem = Hashtbl.create 8 in
  let rec go s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some vrs -> vrs
    | None ->
        let vrs =
          match s with
          | Lit _ -> Vars.empty
          | Var (_, vn) -> Vars.singleton vn
          | Not (_, t) -> go t
          | And (_, ch) | Or (_, ch) ->
              List.fold_left (fun acc c -> Vars.union acc (go c)) Vars.empty ch
        in
        Hashtbl.replace mem uid vrs;
        vrs
  in
  go s

(*
  Simplifies the formula [s] by rewriting it according to boolean
  algebra rules.
*)

let simpl s =
  let rec part vars ops = function
    | [] -> vars, ops
    | (Var _ as hd) :: tl | (Not _ as hd) :: tl -> part (hd :: vars) ops tl
    | Or (_, ch) :: tl -> part (ch @ vars) ops tl
    | (And _ as hd) :: tl -> part vars (hd :: ops) tl
    | _ :: tl -> part vars ops tl
  in
  let or_dist v and_s =
    List.fold_left (fun acc x -> Or (fresh_formula_uid (), x :: v) :: acc) [] and_s
  in
  match s with
  | Or (_, ch) ->
      let vars, ops = part [] [] ch in
      if List.length ops = 0 then Or (fresh_formula_uid (), vars)
      else
        let y =
          List.fold_left
            (fun acc op ->
              match op with And (_, ch) -> or_dist vars ch @ acc | _ -> acc)
            [] ops
        in
        And (fresh_formula_uid (), y)
  | _ -> s

let flatten_and ch =
  List.fold_left
    (fun acc c -> match c with And (_, c_ch) -> c_ch @ acc | _ -> c :: acc)
    [] ch

(*
  Negates the formula [s]
*)

let negate ?(mem = Hashtbl.create 8) s =
  let rec transform s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some t -> t
    | None ->
        let r =
          match s with
          | Lit b -> Lit (not b)
          | Var _ as s -> Not (fresh_formula_uid (), s)
          | Not (_, t) -> t
          | And (_, ch) -> Or (fresh_formula_uid (), List.map transform ch)
          | Or (_, ch) -> And (fresh_formula_uid (), List.map transform ch)
        in
        Hashtbl.replace mem uid r;
        r
  in
  transform s

(*
  Computes the negative normal form of formula [s].
*)

let negative_normal_form s =
  let mem = Hashtbl.create 8 in
  let rec transform pol s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some nnf -> nnf
    | None ->
        let r =
          match s with
          | Lit b -> Lit (b = pol)
          | Var _ -> s
          | Not (_, Var _) -> s
          | Not (_, t) -> transform (not pol) t
          | And (_, ch) when pol -> And (fresh_formula_uid (), List.map (transform pol) ch)
          | And (_, ch) -> Or (fresh_formula_uid (), List.map (transform pol) ch)
          | Or (_, ch) when pol -> Or (fresh_formula_uid (), List.map (transform pol) ch)
          | Or (_, ch) -> And (fresh_formula_uid (), List.map (transform pol) ch)
        in
        Hashtbl.replace mem uid r;
        r
  in
  transform true s

(*
  Unfolds the formula, building a formula whose operators
  And and Or admit at most 2 sub formulas.
*)

let unfold_formula s =
  let mem = Hashtbl.create 8 in
  let rec transform s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some t -> t
    | None ->
        let r =
          match s with
          | Lit _ | Var _ -> s
          | Not (_, t) -> Not (fresh_formula_uid (), transform t)
          | And (_, hd :: tl) when List.length tl > 1 ->
              let unfold_tl = transform (And (fresh_formula_uid (), tl)) in
              And (fresh_formula_uid (), [ transform hd; unfold_tl ])
          | Or (_, hd :: tl) when List.length tl > 1 ->
              let unfold_tl = transform (Or (fresh_formula_uid (), tl)) in
              Or (fresh_formula_uid (), [ transform hd; unfold_tl ])
          | And (_, ch) -> And (fresh_formula_uid (), List.map transform ch)
          | Or (_, ch) -> Or (fresh_formula_uid (), List.map transform ch)
        in
        Hashtbl.replace mem uid r;
        r
  in
  transform s

(*
  Transformation to conjunctive normal form (CNF)
  using the Tseitin transformation.
*)

let key_binding = ref 0

let cnf s =
  let binding = Hashtbl.create 8 in
  let formula_keys = Hashtbl.create 8 in

  (*
    Sets the lower bound for the newly generated variables.
  *)
  let vrs = vars s in
  if Vars.cardinal vrs = 0 then s
  else
    let sup_var = Vars.max_elt vrs in
    key_binding := sup_var;

    Printf.printf "sup %d\n%!" !key_binding;

    let rec bind s =
      let uid = formula_uid s in
      match Hashtbl.find_opt formula_keys uid with
      | Some k -> k
      | None ->
          let k =
            match s with
            | Lit _ | Var _ -> s
            | Not (_, t) ->
                let new_t = bind t in
                let key = incr key_binding in
                Hashtbl.replace binding key (Not (fresh_formula_uid (), new_t));
                Var (fresh_formula_uid (), key)
            | And (_, ch) ->
                let new_ch = List.map bind ch in
                let key = incr key_binding in
                Hashtbl.replace binding key (And (fresh_formula_uid (), new_ch));
                Var (fresh_formula_uid (), key)
            | Or (_, ch) ->
                let new_ch = List.map bind ch in
                let key = incr key_binding in
                Hashtbl.replace binding key (Or (fresh_formula_uid (), new_ch));
                Var (fresh_formula_uid (), key)
          in
          Hashtbl.replace formula_keys uid k;
          k
    in
    let root = bind s in
    let and_ch =
      Hashtbl.fold
        (fun k v acc ->
          let var_k = Var (fresh_formula_uid (), k) in
          let left_imp = Or (fresh_formula_uid (), [ negate var_k; v ]) in
          let left_imp_simpl = simpl left_imp in
          left_imp_simpl :: acc)
        binding [ root ]
    in
    And (fresh_formula_uid (), flatten_and and_ch)

(*
  Converts the CNF formula [s] to the clause type.
*)

let cnf_formula_to_clauses s : cnf_formula =
  let to_clause acc c =
    match c with
    | Var (_, vn) -> [ vn ] :: acc
    | Not (_, Var (_, vn)) -> [ vn * -1 ] :: acc
    | Or (_, ch) ->
        if List.exists (( = ) (Lit true)) ch then acc
        else
          List.fold_left
            (fun acc s ->
              match s with
              | Var (_, vn) -> vn :: acc
              | Not (_, Var (_, vn)) -> (-1 * vn) :: acc
              | _ -> failwith "A variable was expected!")
            [] ch
          :: acc
    | _ -> failwith "[error] a disjunction was expected"
  in
  let clauses =
    match s with
    | Lit false -> [ [] ]
    | Lit true -> [ [ 1 ] ]
    | Var (_, vn) -> [ [ vn ] ]
    | And (_, ch) -> List.fold_left (fun acc c -> to_clause acc c) [] ch
    | _ -> failwith "[error] the formula is not in CNF"
  in
  { clauses; amount_vars = !key_binding; amount_clauses = List.length clauses }

(*
  Converts AIG formula to formula.
*)

let aig_formula_to_formula s =
  let mem = Hashtbl.create 8 in
  let rec transform s =
    match Hashtbl.find_opt mem s with
    | Some t -> t
    | None ->
        let res =
          match s with
          | AIGLit b -> Lit b
          | AIGVar v -> Var (fresh_formula_uid (), v)
          | AIGNot t -> Not (fresh_formula_uid (), transform t)
          | AIGAnd (_, u, v) -> And (fresh_formula_uid (), [ transform u; transform v ])
        in
        Hashtbl.replace mem s res;
        res
  in
  transform s

(*
  Converts formula to AIG formula. First ensures
  that [s] is in NNF and that the operators
  contain at most 2 children.
*)

let formula_to_aig_formula s =
  let s = unfold_formula s in

  let mem = Hashtbl.create 8 in
  let neg = Hashtbl.create 8 in

  (*
    [var_index] is the index of variable names
    [int_index] is the index of intermediate varable names
  *)
  let vars = vars s in

  let var_index = ref 0 in
  let int_index = ref (Vars.cardinal vars) in

  let var_map = Hashtbl.create 8 in

  let rec transform s =
    let uid = formula_uid s in
    match Hashtbl.find_opt mem uid with
    | Some t -> t
    | None ->
        let r =
          match s with
          | Lit b -> AIGLit b
          | Var (_, v) ->
              if Hashtbl.mem var_map v then Hashtbl.find mem (Hashtbl.find var_map v)
              else (
                Hashtbl.replace var_map v uid;
                AIGVar (incr var_index))
          | Not (_, t) -> ( match transform t with AIGNot t -> t | tr -> AIGNot tr)
          | And (_, [ u ]) -> transform u
          | And (_, [ u; v ]) -> AIGAnd (incr int_index, transform u, transform v)
          | Or _ -> AIGNot (transform (negate ~mem:neg s))
          | _ -> failwith "the formula cannot be translated to an AIG formula"
        in
        Hashtbl.replace mem uid r;
        r
  in
  transform s
