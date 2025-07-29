type formula =
  | Lit of fingerprint * bool
  | Var of fingerprint * bool * int
  | Not of fingerprint * formula
  | And of fingerprint * formula list
  | Or of fingerprint * formula list

and fingerprint = {
  uid : int; (* mutable sym : formula option;
  mutable sfs : formula list; *)
}

type lab_formula = Left of formula | Right of formula
type sequent = lab_formula * lab_formula

module Vars = Set.Make (Int)

let get_fp = function
  | Lit (fp, _) | Var (fp, _, _) | Not (fp, _) | And (fp, _) | Or (fp, _) -> fp

let get_uid s =
  let fp = get_fp s in
  fp.uid

let rec str_fm verbose s =
  let uid = get_uid s in
  let prefix = if verbose then string_of_int uid ^ "@" else "" in
  let str =
    match s with
    | Lit (_, true) -> "1"
    | Lit (_, false) -> "0"
    | Var (_, pure, v) -> if pure then string_of_int v ^ "'" else string_of_int v
    | And (_, ss) -> "(" ^ String.concat " ^ " (List.map (str_fm verbose) ss) ^ ")"
    | Or (_, ss) -> "(" ^ String.concat " v " (List.map (str_fm verbose) ss) ^ ")"
    | Not (_, s) -> "~" ^ str_fm verbose s
  in
  prefix ^ str

let str_annot = function
  | Left s -> Printf.sprintf "L#%s" (str_fm false s)
  | Right s -> Printf.sprintf "R#%s" (str_fm false s)

let fm_uid = ref 1
let var_counter = ref 1000

let fresh_counter c =
  c := !c + 1;
  !c

let fresh_fingerprint () = { uid = fresh_counter fm_uid }
let make_lit b = Lit (fresh_fingerprint (), b)

let make_var pure v =
  if v > !var_counter then var_counter := v;
  Var (fresh_fingerprint (), pure, v)

let make_not s = Not (fresh_fingerprint (), s)
let make_and ss = And (fresh_fingerprint (), ss)
let make_or ss = Or (fresh_fingerprint (), ss)
let make_imp s t = make_or [ make_not s; t ]
let make_equiv s t = make_and [ make_imp s t; make_imp t s ]

type statement = { goal : sequent; axioms : sequent list }

let str_seq seq =
  let l, r = seq in
  Printf.sprintf "%s, %s" (str_annot l) (str_annot r)

let str_stm stm =
  Printf.sprintf "%d axiom(s)\n" (List.length stm.axioms)
  ^ String.concat "\n" (List.map str_seq stm.axioms)
  ^ "\n====================\n" ^ str_seq stm.goal ^ "\n"

let sequent_to_formula seq =
  match seq with
  | Left s, Right t | Right t, Left s -> make_imp s t
  | Left s, Left t -> make_or [ make_not s; make_not t ]
  | Right s, Right t -> make_or [ s; t ]

let stm_to_formula stm =
  let axioms = make_and (List.map sequent_to_formula stm.axioms) in
  make_imp axioms (sequent_to_formula stm.goal)

module FormulaSet = Set.Make (struct
  type t = formula

  let compare s t = Stdlib.compare (get_uid s) (get_uid t)
end)

module FmUidSet = Set.Make (Int)

let subformulas f =
  let rec go acc s =
    let acc = FormulaSet.add s acc in
    match s with
    | Lit _ | Var _ -> acc
    | Not (_, t) -> go acc t
    | And (_, ss) | Or (_, ss) -> List.fold_left go acc ss
  in
  go FormulaSet.empty f

let label_formula s = Left s, Right s

let rec aig2fm af_fm_map equivs pol af =
  match Hashtbl.find_opt af_fm_map (pol, af) with
  | Some s -> s
  | None ->
      let s =
        match af with
        | Aiger.Lit b -> make_lit (b && pol)
        | Aiger.Var v when pol -> make_var (not (Hashtbl.mem equivs v)) v
        | Aiger.Var _ -> make_not (aig2fm af_fm_map equivs true af)
        | Aiger.Not s -> aig2fm af_fm_map equivs (not pol) s
        | Aiger.And (_, ss) ->
            let bd = fresh_counter var_counter in
            (* Printf.printf "%d\n" bd; *)
            let var = make_var false bd in
            let ss = List.map (aig2fm af_fm_map equivs pol) ss in
            let ts = if pol then make_and ss else make_or ss in
            Hashtbl.replace equivs bd (var, ts);
            var
      in
      Hashtbl.replace af_fm_map (pol, af) s;
      s

let rec subst_fm name_map f =
  let help ss =
    List.fold_right
      (fun s (b, acc) ->
        match subst_fm name_map s with None -> b, s :: acc | Some t -> true, t :: acc)
      ss (false, [])
  in
  match f with
  | Var (_, false, v) when Hashtbl.mem name_map v ->
      let _, var = Hashtbl.find name_map v in
      Some var
  | Lit _ | Var _ -> None
  | Not (_, s) -> (
      match subst_fm name_map s with None -> None | Some t -> Some (make_not t))
  | And (_, ss) ->
      let b, ss = help ss in
      if b then Some (make_and ss) else None
  | Or (_, ss) ->
      let b, ss = help ss in
      if b then Some (make_or ss) else None

(* Forward proof mode *)

type label_uid = int * int
type sequent_uid = label_uid * label_uid

module UidSet = Set.Make (struct
  type t = sequent_uid

  let compare = Stdlib.compare
end)

type hp_vertice = int * int

module HypergraphSet = Set.Make (struct
  type t = hp_vertice

  (*
    The pair is commutative: (a, b) = (b, a)
  *)

  let compare = Stdlib.compare
end)

(*
  An hyperedge is the data of two sets of vertices,
  the source [src] and the destination [dst], an arity 
  [aty] that is the cardinal of [src] and a proven 
  coefficient [cfc].
*)

(* type hp_edge = { mutable src : HypergraphSet.t; dst : hp_vertice }
type hp_node = { uid : hp_vertice; seq : sequent; mutable child : hp_edge list }
type hypergraph = { nodes : (hp_vertice, hp_node) Hashtbl.t }

(*
  String utils for hypergraphs
*)

let str_hyperedge he =
  let str_uid hs =
    String.concat ", "
      (List.map (fun (x, y) -> string_of_int x ^ "_" ^ string_of_int y) hs)
  in
  Printf.sprintf "({%s}, {%s})"
    (str_uid (HypergraphSet.elements he.src))
    (str_uid [ he.dst ])

let str_hypernode hn =
  let a, b = hn.uid in
  Printf.sprintf "[%d_%d : %s]" a b (str_seq hn.seq)

let str_hypergraph hg =
  "Hypernodes::\n"
  ^ Hashtbl.fold (fun _ v acc -> str_hypernode v ^ "\n" ^ acc) hg.nodes "" *)

(*
  Crafts the unique identifier for sequents taking the unique
  identifier of each annotated formula and making the ordered
  pair.
*)

let label_uid = function Left s -> 0, get_uid s | Right s -> 1, get_uid s

let seq_uid seq =
  let l, r = seq in
  let luid, ruid = label_uid l, label_uid r in
  if luid < ruid then luid, ruid else ruid, luid

let forget_label = function Left s | Right s -> s

type alpha = (int, FmUidSet.t) Hashtbl.t
type beta = (int, (int, FmUidSet.t) Hashtbl.t) Hashtbl.t

type forward_ds = {
  proven : (int * int, bool) Hashtbl.t;
  subs_map : (int, FmUidSet.t) Hashtbl.t;
  ax_subs : (int, bool) Hashtbl.t;
  non_proven_left : alpha;
  non_proven_right : alpha;
  p : alpha;
  co_p : alpha;
  a : alpha; (* A structure for disjunction *)
  co_a : alpha; (* A structure for conjunction *)
  b : beta; (* B structure for disjunction *)
  co_b : beta; (* B structure for conjunction *)
  c : beta;
  d : beta;
}

let hash_map h key =
  match Hashtbl.find_opt h key with None -> Hashtbl.create 8 | Some h -> h

let hash_map_set h key =
  match Hashtbl.find_opt h key with None -> FmUidSet.empty | Some s -> s

let double_hash_set h key_a key_b = hash_map_set (hash_map h key_a) key_b
let print_fm_uid_set s = FmUidSet.iter (fun x -> Printf.printf "%d\n" x) s

let str_fuset s =
  "{"
  ^ String.concat ", " (FmUidSet.fold (fun x acc -> string_of_int x :: acc) s [])
  ^ "}"

let print_beta x =
  Hashtbl.iter
    (fun k v ->
      Printf.printf "%d ->\n" k;
      Hashtbl.iter (fun k' v' -> Printf.printf "%d -> %s\n" k' (str_fuset v')) v)
    x

let rec add fm_map qu goal_uid ds =
  let update ref h x =
    Hashtbl.iter
      (fun k v ->
        let px = hash_map h x in
        let ps = hash_map_set px k in
        let un = FmUidSet.union ps v in
        Hashtbl.replace px k un;
        Hashtbl.replace h x px)
      ref
  in

  match qu with
  | [] -> false
  | seq :: tl when Hashtbl.mem ds.proven seq -> add fm_map tl goal_uid ds
  | seq :: tl ->
      Hashtbl.replace ds.proven seq true;
      let a, b = seq in

      if goal_uid = seq then (
        Printf.printf "Proves (%s, %s)!\n%!"
          (str_fm false (Hashtbl.find fm_map a))
          (str_fm false (Hashtbl.find fm_map b));
        true)
      else (

        (*
          Update for the cut rule
        *)
        Hashtbl.replace ds.p a (FmUidSet.add b (hash_map_set ds.p a));
        Hashtbl.replace ds.co_p b (FmUidSet.add a (hash_map_set ds.co_p b));

        (*
          Update for the other two-premisse rules
        *)
        update (hash_map ds.b a) ds.d b;
        update (hash_map ds.co_b b) ds.c a;

        (*
          Deduces the new sequents from (a, b)
        *)
        let pair = fun f -> a, f in
        let co_pair = fun f -> f, b in

        let set_li =
          [
            "A2", hash_map_set ds.co_p, a, co_pair;
            "B2", hash_map_set ds.p, b, pair;
            "A3", double_hash_set ds.d b, a, co_pair;
            "B3", double_hash_set ds.c a, b, pair;
            "A1", hash_map_set ds.co_a, a, co_pair;
            "B1", hash_map_set ds.a, b, pair;
          ]
        in
        (*
          Adding the deduced sequent for the other rules, according to [set_li]
        *)
        let tl =
          List.fold_right
            (fun (_tag, set_fn, x, fn_pair) acc ->
              FmUidSet.fold
                (fun s acc ->
                  (*Queue.push (fn_pair s) qu*)
                  fn_pair s :: acc)
                (set_fn x) acc)
            set_li tl
        in
        add fm_map tl goal_uid ds)

(*
  Conversion to shape formula in order to order conjunctive normalization
  and DIMACS writings.
*)

let rec fm_to_sfm pol f =
  match f with
  | Lit (_, b) -> Gen.new_lit (-1) (b && pol)
  | Var (_, _, v) -> Gen.new_lit v pol
  | Not (_, f) -> fm_to_sfm (not pol) f
  | Or (_, ss) when pol -> Gen.new_or (List.map (fm_to_sfm pol) ss)
  | And (_, ss) when pol -> Gen.new_and (List.map (fm_to_sfm pol) ss)
  | And (_, ss) -> Gen.new_or (List.map (fm_to_sfm pol) ss)
  | Or (_, ss) -> Gen.new_and (List.map (fm_to_sfm pol) ss)

let start afm =
  Printf.printf "OLSC\n%!";
  let _top, af = afm in

  let equivs = Hashtbl.create 8 in
  let af_fm_map = Hashtbl.create 8 in

  let fm = aig2fm af_fm_map equivs true af in
  let fm_uid = get_uid fm in

  let rename = Hashtbl.create 8 in
  Hashtbl.iter
    (fun k _ ->
      let fresh_vn = fresh_counter var_counter in
      (* Printf.printf "%d -> %d\n" k fresh_vn; *)
      Hashtbl.replace rename k (fresh_vn, make_var false fresh_vn))
    equivs;

  let equivs' = Hashtbl.create 8 in

  let gm =
    Hashtbl.fold
      (fun k (xv, v) acc ->
        Hashtbl.replace equivs' k (xv, v);
        let k', var = Hashtbl.find rename k in
        (* Printf.printf "%s\n" (str_fm true var); *)
        (match subst_fm rename v with
        | None -> Hashtbl.replace equivs' k' (var, v)
        | Some s -> Hashtbl.replace equivs' k' (var, s));
        if xv = fm then var else acc)
      equivs fm
  in
  let gm_uid = get_uid gm in

  let ax_subs = Hashtbl.create 8 in

  let axioms, subs =
    Hashtbl.fold
      (fun _ (var, v) (acc, subs) ->
        let lvar, rvar = label_formula var in
        let lval, rval = label_formula v in

        Hashtbl.replace ax_subs (get_uid var) true;
        Hashtbl.replace ax_subs (get_uid v) true;

        (*
          To refine in order to handle right disjunction as well
        *)
        let sfs = subformulas v in
        let subs = FormulaSet.union subs sfs in
        let subs = FormulaSet.add var subs in

        (lvar, rval) :: (lval, rvar) :: acc, subs)
      equivs' ([], FormulaSet.empty)
  in

  let axioms = FormulaSet.fold (fun s acc -> (Left s, Right s) :: acc) subs axioms in

  let stm = { axioms; goal = Left fm, Right gm } in

  (*
    Conjunctive normal form transformation for the SAT solver
  *)
  let fm = stm_to_formula stm in

  (* Negation of the formula to be declared UNSAT by the SAT solver *)
  let sfm = fm_to_sfm false fm in
  let cnf = Gen.cnf sfm in

  Printf.printf "Writing the CNF\n%!";
  let cnf_file = open_out "aig.cnf" in
  Printf.fprintf cnf_file "%s\n" (Translator.write_dimacs cnf);

  let a, co_a = Hashtbl.create 8, Hashtbl.create 8 in
  let b, co_b = Hashtbl.create 8, Hashtbl.create 8 in

  (*
    The following [partition] function does a partition of the subformula set
    of the given problem.
  *)
  let partition h uid ss =
    List.iter
      (fun s ->
        let s_uid = get_uid s in
        let m = hash_map_set h s_uid in
        Hashtbl.replace h s_uid (FmUidSet.add uid m))
      ss
  in

  let proven = Hashtbl.create 8 in
  let p = Hashtbl.create 8 in
  let co_p = Hashtbl.create 8 in

  let formula_map = Hashtbl.create 8 in

  (*
    Fills in the [proven], [p], [co_p], [a], [co_a], [b] and [co_b] maps
  *)
  let help uid bh ss =
    if List.length ss = 2 then (
      let x = get_uid (List.nth ss 0) in
      let y = get_uid (List.nth ss 1) in
      let hy = hash_map bh x in
      let hx = hash_map bh y in

      let hys = hash_map_set hy y in
      let hxs = hash_map_set hx x in

      Hashtbl.replace hy y (FmUidSet.add uid hys);
      Hashtbl.replace hx x (FmUidSet.add uid hxs);
      Hashtbl.replace bh x hy;
      Hashtbl.replace bh y hx)
  in

  let non_proven_left = Hashtbl.create 8 in
  let non_proven_right = Hashtbl.create 8 in

  FormulaSet.iter
    (fun s ->
      let uid = get_uid s in

      Hashtbl.replace formula_map uid s;

      match s with
      | And (_, ss) ->
          partition co_a uid ss;
          help uid co_b ss
      | Or (_, ss) ->
          partition a uid ss;
          help uid b ss
      | _ -> ())
    subs;

  let subs_map = Hashtbl.create 8 in
  let subs_uid =
    FormulaSet.fold
      (fun s acc ->
        let uid = get_uid s in
        FmUidSet.add uid acc)
      subs FmUidSet.empty
  in

  FmUidSet.iter (fun uid -> Hashtbl.replace subs_map uid subs_uid) subs_uid;

  let ds =
    {
      proven;
      non_proven_left;
      non_proven_right;
      p;
      co_p;
      subs_map;
      ax_subs;
      a;
      co_a;
      b;
      co_b;
      c = Hashtbl.create 8;
      d = Hashtbl.create 8;
    }
  in

  (* Printf.printf "Formula --\n%s\n" (str_fm false fm); *)
  (* Printf.printf "Subaxioms --\n";
  Hashtbl.iter (fun _ v -> Printf.printf "%s\n" (str_fm false v)) ax_subs; *)
  Printf.printf "Subformulas --\n";
  FormulaSet.iter (fun s -> Printf.printf "%s\n" (str_fm true s)) subs;
  Printf.printf "Axioms --\n";
  List.iter (fun s -> Printf.printf "%s\n" (str_seq s)) axioms;
  Printf.printf "Proving (%s, %s)\n%!"
    (str_fm false (Hashtbl.find formula_map fm_uid))
    (str_fm false (Hashtbl.find formula_map gm_uid));

  List.exists
    (fun ax ->
      let a, b = ax in
      let a, b = forget_label a, forget_label b in
      let ax_seq = get_uid a, get_uid b in

      add formula_map [ ax_seq ] (fm_uid, gm_uid) ds)
    axioms

