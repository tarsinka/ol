open Logic

(*
  We here implement a generator of hard non-clausal SAT-problems
*)

type shape_formula =
  | SLit of bool * int
  | SVar of int
  | SAnd of shape_formula list
  | SOr of shape_formula list

type shape = int list

let shape_str sh = "[" ^ String.concat ", " (List.map string_of_int sh) ^ "]"

let rec shape_formula_str = function
  | SLit (false, i) -> "~" ^ string_of_int i
  | SLit (true, i) | SVar i -> string_of_int i
  | SAnd sli -> "(" ^ String.concat " ∧ " (List.map shape_formula_str sli) ^ ")"
  | SOr sli -> "(" ^ String.concat " v " (List.map shape_formula_str sli) ^ ")"

let uid = ref 1

let reset () = uid := 1

let fresh_uid () =
  uid := !uid + 1;
  !uid

let generate_shape d max_k =
  let rec help = function 0 -> [] | d -> (Random.int max_k + 2) :: help (d - 1) in
  help d

let rec build_shape kd sh =
  let rec aux n kd sh acc =
    match n with 0 -> acc | _ -> aux (n - 1) kd sh (build_shape kd sh :: acc)
  in
  match sh with
  | [] ->
      let i = fresh_uid () in
      SVar i
  | k :: sh ->
      let li = aux k (not kd) sh [] in
      if kd then SAnd li else SOr li

let rec vars = function
  | SLit (_, i) | SVar i -> Vars.singleton i
  | SAnd li | SOr li ->
      List.fold_right (fun s acc -> Vars.union (vars s) acc) li Vars.empty

let or_dist_over_and a b =
  let sli =
    List.fold_right
      (fun s acc -> List.fold_right (fun t acc -> SOr [ s; t ] :: acc) b acc)
      a []
  in
  SAnd sli

(*
  Simplifies the given formula [s] according to de Morgan's rules.
*)

let rec simpl = function
  | SAnd [ x ] | SOr [ x ] -> x
  | SOr sli as fo ->
      let sli = List.map simpl sli in
      let nm, and_fm =
        List.fold_right
          (fun s (acc, acc') ->
            match s with
            | SAnd sli -> acc, sli :: acc'
            | SOr sli -> sli @ acc, acc'
            | _ -> s :: acc, acc')
          sli ([], [])
      in
      if and_fm = [] then SOr nm
      else if nm = [] then fo
      else
        let new_or = simpl (SOr nm) in
        let and_sli =
          List.fold_right (fun s acc -> or_dist_over_and [ new_or ] s :: acc) and_fm []
        in
        simpl (SAnd and_sli)
  | SAnd sli ->
      let sli = List.map simpl sli in
      let res =
        List.fold_right
          (fun s acc -> match s with SAnd sli -> sli @ acc | _ -> s :: acc)
          sli []
      in
      SAnd res
  | f -> f

(*
    Generates a formula on the given shape with random assignements
*)

let generate_instance sh_fm density =
  let vs = vars sh_fm in
  (* let r = Vars.cardinal vs / 50 in *)
  let r = int_of_float (float_of_int (Vars.cardinal vs) *. density +. 1.) in

  let rec help = function
    | SVar _ -> SLit (Random.bool (), Random.int r + 1)
    | SAnd li -> SAnd (List.map help li)
    | SOr li -> SOr (List.map help li)
    | f -> f
  in
  simpl (help sh_fm)

(*
  Negate the formula [s].
*)

let rec negate = function
  | SLit (pol, i) -> SLit (not pol, i)
  | SAnd sli -> SOr (List.map negate sli)
  | SOr sli -> SAnd (List.map negate sli)
  | f -> f

(*
  Checks whether [cl] is a clause.
*)

let rec is_clause = function
  | SLit _ -> true
  | SOr sli -> List.for_all is_clause sli
  | _ -> false

(*
  Checks whether [s] is a CNF.
*)

let is_cnf = function
  | SLit _ -> true
  | SAnd sli | SOr sli -> List.for_all is_clause sli
  | _ -> false

(*
    Converts a shape formula to a conjunctive normal form using Tseitin's transformation.
*)

let to_cnf sfm =
  if is_cnf sfm then sfm
  else
    let equiv = Hashtbl.create 5 in
    let rec subst_li sli =
      List.fold_right
        (fun s acc ->
          let subst = bind s in
          subst :: acc)
        sli []
    and bind = function
      | SAnd sli ->
          let fu = fresh_uid () in
          Hashtbl.replace equiv fu (SAnd (subst_li sli));
          SLit (true, fu)
      | SOr sli ->
          let fu = fresh_uid () in
          Hashtbl.replace equiv fu (SOr (subst_li sli));
          SLit (true, fu)
      | sfm -> sfm
    in
    let mn = bind sfm in
    let conj =
      Hashtbl.fold
        (fun k v acc ->
          SOr [ SLit (false, k); v ] :: SOr [ negate v; SLit (true, k) ] :: acc)
        equiv [ mn ]
    in
    let res = simpl (SAnd conj) in
    res

let cnf_n_clauses = function SAnd sli -> List.length sli | SOr _ | SLit _ -> 1 | _ -> 0
let fmt_lit (pol, id) = (if pol then "" else "-") ^ string_of_int id

let rec fmt_clause scl =
  match scl with
  | SLit (pol, i) -> fmt_lit (pol, i)
  | SOr dis ->
      String.concat " " (List.fold_right (fun s acc -> fmt_clause s :: acc) dis [])
  | _ -> ""

let translate cnf =
  if not (is_cnf cnf) then failwith "Not a CNF formula!"
  else
    let str =
      match cnf with
      | SLit (pol, id) -> fmt_lit (pol, id) ^ " 0\n"
      | SAnd sli ->
          String.concat " 0\n"
            (List.fold_right (fun cl acc -> fmt_clause cl :: acc) sli [])
          ^ " 0\n"
      | SOr _ -> fmt_clause cnf ^ " 0\n"
      | _ -> ""
    in
    Printf.sprintf "p cnf %d %d\n%s" (Vars.cardinal (vars cnf)) (cnf_n_clauses cnf) str

let rec pow f = function 0 -> 1. | p -> f *. pow f (p - 1)

(*
    If the shape [sh] is of the first kind [pol] (ie conjunction first) then
    we return the probability for 1 :: sh, else we return the probability
    for sh.
*)

let sat_proba pol sh =
  let rec help = function [] -> 0.5 | k :: sh -> 1. -. pow (help sh) k in
  if pol then help (1 :: sh) else help sh

let shf_to_fm sfm =
  let mem = Hashtbl.create 5 in
  let rec aux = function
    | SLit (pol, i) ->
        let var =
          match Hashtbl.find_opt mem i with
          | None ->
              let v = init (Var i) in
              Hashtbl.replace mem i v;
              v
          | Some v -> v
        in
        if pol then var else init (Neg var)
    | SAnd sli -> init (And (List.map aux sli))
    | SOr sli -> init (Or (List.map aux sli))
    | SVar _ -> failwith "This is not an instance!"
  in
  aux sfm

let rec rfm_to_shf (_, rm) =
  let res =
    match rm with
    | RLit true -> SOr [ SLit (true, 1); SLit (false, 1) ]
    | RLit false -> SAnd [ SLit (true, 1); SLit (false, 1) ]
    | RVar (i, pol) -> SLit (pol, i)
    | RAnd (li, true) -> SAnd (List.map rfm_to_shf li)
    | RAnd (li, false) -> SOr (List.map rfm_to_shf li)
  in
  simpl res
