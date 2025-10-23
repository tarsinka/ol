open Logic

type olsc_formula =
  | Lit of fingerprint * bool
  | Var of fingerprint * bool * int
  | Not of fingerprint * olsc_formula
  | And of fingerprint * olsc_formula list
  | Or of fingerprint * olsc_formula list

and fingerprint = { mutable uid : int; mutable neg : olsc_formula option }

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

let fm_uid = ref 1
let var_counter = ref 1

let reset () =
  fm_uid := 1;
  var_counter := 1

let fresh_counter c =
  c := !c + 1;
  !c

let fresh_fingerprint () = { uid = fresh_counter fm_uid; neg = None }
let make_lit b = Lit (fresh_fingerprint (), b)

let make_var pure v =
  if v > !var_counter then var_counter := v;
  Var (fresh_fingerprint (), pure, v)

let make_not s = Not (fresh_fingerprint (), s)
let make_and ss = And (fresh_fingerprint (), ss)
let make_or ss = Or (fresh_fingerprint (), ss)
let make_imp s t = make_or [ make_not s; t ]
let make_equiv s t = make_and [ make_imp s t; make_imp t s ]

module FormulaSet = Set.Make (struct
  type t = olsc_formula

  let compare s t = Stdlib.compare (get_uid s) (get_uid t)
end)

module FmUidSet = Set.Make (Int)

let rec fm_eq s t =
  match s, t with
  | Lit (_, b), Lit (_, b') -> b = b'
  | Var (_, p, v), Var (_, p', v') -> p = p' && v = v'
  | Not (_, s'), Not (_, t') -> fm_eq s' t'
  | And (_, ss), And (_, tt) | Or (_, ss), Or (_, tt) -> List.for_all2 fm_eq ss tt
  | _ -> false

let subformulas f =
  let rec go acc s =
    let acc = FormulaSet.add s acc in
    match s with
    | Lit _ | Var _ -> acc
    | Not (_, t) -> go acc t
    | And (_, ss) | Or (_, ss) -> List.fold_left go acc ss
  in
  go FormulaSet.empty f

let rec aig_formula_to_olsc_formula af_fm_map equivs pol af =
  match Hashtbl.find_opt af_fm_map (pol, af) with
  | Some s -> s
  | None ->
      let s =
        match af with
        | AIGLit b -> make_lit (b && pol)
        | AIGVar v when pol ->
            make_var (not (Hashtbl.mem equivs v)) (fresh_counter var_counter)
        | AIGVar _ ->
            let v = aig_formula_to_olsc_formula af_fm_map equivs true af in
            let neg_v = make_not v in
            let fp = get_fp v in
            let neg_fp = get_fp neg_v in
            fp.neg <- Some neg_v;
            neg_fp.neg <- Some v;
            neg_v
        | AIGNot t ->
            let z = aig_formula_to_olsc_formula af_fm_map equivs pol t in
            let neg_z = aig_formula_to_olsc_formula af_fm_map equivs (not pol) t in

            let fp = get_fp z in
            let neg_fp = get_fp neg_z in
            fp.neg <- Some neg_z;
            neg_fp.neg <- Some z;
            neg_z
        | AIGAnd (_, u, v) ->
            let bd = fresh_counter var_counter in
            let var = make_var false bd in
            let ss =
              List.map (aig_formula_to_olsc_formula af_fm_map equivs pol) [ u; v ]
            in
            let ts = if pol then make_and ss else make_or ss in
            Hashtbl.replace equivs bd (var, ts);
            var
      in
      Hashtbl.replace af_fm_map (pol, af) s;
      s

let rec subst_fm name_map f =
  let help ss =
    List.fold_left
      (fun (b, acc) s ->
        match subst_fm name_map s with None -> b, s :: acc | Some t -> true, t :: acc)
      (false, []) ss
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

let hash_map h key =
  match Hashtbl.find_opt h key with None -> Hashtbl.create 8 | Some h -> h

let hash_map_set h key =
  match Hashtbl.find_opt h key with None -> FmUidSet.empty | Some s -> s

let double_hash_set h key_a key_b = hash_map_set (hash_map h key_a) key_b

let nnf s =
  let mem = Hashtbl.create 8 in
  let rec transform pol s =
    let uid = get_uid s in
    let fp = get_fp s in
    match Hashtbl.find_opt mem (uid, pol), fp.neg with
    | Some nnf, _ when pol -> nnf
    | _, Some neg when not pol -> neg
    | _ ->
        let nnf =
          match s with
          | Lit (_, b) -> make_lit (b = pol)
          | Var _ when not pol -> make_not s
          | Var _ -> s
          | Not (_, t) -> transform (not pol) t
          | And (_, ss) when pol -> make_and (List.map (transform pol) ss)
          | And (_, ss) -> make_or (List.map (transform pol) ss)
          | Or (_, ss) when pol -> make_or (List.map (transform pol) ss)
          | Or (_, ss) -> make_and (List.map (transform pol) ss)
        in
        (if not pol then
           let fp = get_fp s in
           fp.neg <- Some nnf);
        Hashtbl.replace mem (uid, pol) nnf;
        nnf
  in
  transform true s

let negate s =
  let fp = get_fp s in
  match fp.neg with
  | Some n -> n
  | None ->
      let neg = nnf (make_not s) in
      fp.neg <- Some neg;
      let neg_fp = get_fp neg in
      neg_fp.neg <- Some s;
      neg

let subformulas_seq s =
  let fst, snd = s in
  FormulaSet.union (subformulas fst) (subformulas snd)

(*
  ================= Main proof-search algorithm ===================
*)

let prove s axioms subformulas =
  (*
    Generates the corresponding Hashtbl [subformulas] to have a quick access to formulas
    from their unique identifier
  *)
  let substbl = Hashtbl.create 8 in
  FormulaSet.iter
    (fun s ->
      (* Printf.printf "adding %s%!\n" (str_fm true s); *)
      let s' = negate s in
      Hashtbl.replace substbl (get_uid s) s;
      Hashtbl.replace substbl (get_uid s') s')
    subformulas;

  (*
      Main datastructures
  *)
  let proven = Hashtbl.create 8 in
  let p_cut = Hashtbl.create 8 in
  let or_map = Hashtbl.create 8 in
  let and_map = Hashtbl.create 8 in
  let p_and = Hashtbl.create 8 in

  (*
      Fills [and_map] and [or_map]
  *)
  (* let get_main_rep uid = match Hashtbl.find_opt eq uid with None -> uid | Some s -> s in *)
  FormulaSet.iter
    (fun s ->
      match s with
      | And (_, ss) ->
          let fst = List.nth ss 0 in
          let snd = List.nth ss 1 in

          let s_uid = get_uid s in

          let fst_uid = get_uid fst in
          let snd_uid = get_uid snd in

          let map_fst = hash_map and_map fst_uid in
          let map_snd = hash_map and_map snd_uid in

          let map_fst_snd = hash_map_set map_fst snd_uid in
          let map_snd_fst = hash_map_set map_snd fst_uid in

          Hashtbl.replace map_fst snd_uid (FmUidSet.add s_uid map_fst_snd);
          Hashtbl.replace map_snd fst_uid (FmUidSet.add s_uid map_snd_fst);

          Hashtbl.replace and_map fst_uid map_fst;
          Hashtbl.replace and_map snd_uid map_snd
      | Or (_, ss) ->
          let s_uid = get_uid s in
          List.iter
            (fun t ->
              let t_uid = get_uid t in
              let or_map_s = hash_map_set or_map t_uid in
              Hashtbl.replace or_map t_uid (FmUidSet.add s_uid or_map_s))
            ss
      | _ -> ())
    subformulas;

  (*
      Instantiates the [worklist] with the axioms and the hypothesis.
  *)
  let worklist =
    List.fold_left
      (fun acc (a, b) ->
        let a_uid = get_uid a in
        let b_uid = get_uid b in
        (a_uid, b_uid) :: acc)
      [] axioms
  in
  let worklist =
    FormulaSet.fold
      (fun s acc ->
        let s' = negate s in
        let s_uid = get_uid s in
        let s'_uid = get_uid s' in
        (s_uid, s'_uid) :: acc)
      subformulas worklist
  in

  let fm, gm = s in
  let fm_uid = get_uid fm in
  let gm_uid = get_uid gm in

  let s_seq_uid = fm_uid, gm_uid in
  let s_seq_uid' = gm_uid, fm_uid in

  (*
    [add] is the deductive function. It takes as an argument a list of valid sequents
    with which it deduces new sequents.
  *)
  let rec add wl =
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

    match wl with
    | [] -> false
    | seq :: _ when seq = s_seq_uid || seq = s_seq_uid' -> true
    | seq :: tl when Hashtbl.mem proven seq -> add tl
    | seq :: tl ->
        let a_uid, b_uid = seq in

        (*
          Updates the set of proven sequents.
        *)
        Hashtbl.replace proven (a_uid, b_uid) true;
        Hashtbl.replace proven (b_uid, a_uid) true;

        let a = Hashtbl.find substbl a_uid in
        let b = Hashtbl.find substbl b_uid in

        (* let a_uid = get_main_rep a_uid in
        let b_uid = get_main_rep b_uid in *)

        (* Printf.printf "%s, %s\n%!" (str_fm false a) (str_fm false b); *)
        let a' = negate a in
        let b' = negate b in

        let a'_uid = get_uid a' in
        let b'_uid = get_uid b' in

        (*
            Updates P_cut
        *)
        Hashtbl.replace p_cut a'_uid (FmUidSet.add b_uid (hash_map_set p_cut a'_uid));
        Hashtbl.replace p_cut b'_uid (FmUidSet.add a_uid (hash_map_set p_cut b'_uid));

        (*
            Updates P_and
        *)
        update (hash_map and_map a_uid) p_and b_uid;
        update (hash_map and_map b_uid) p_and a_uid;

        (*
            Deduces the new sequents from (a, b)
        *)
        let pair = fun x f acc -> (x, f) :: acc in

        let set_li =
          [
            "A2", hash_map_set p_cut, a_uid, pair b_uid;
            "B2", hash_map_set p_cut, b_uid, pair a_uid;
            "A3", double_hash_set p_and b_uid, a_uid, pair b_uid;
            "B3", double_hash_set p_and a_uid, b_uid, pair a_uid;
            "A1", hash_map_set or_map, a_uid, pair b_uid;
            "B1", hash_map_set or_map, b_uid, pair a_uid;
          ]
        in
        (*
            Adding the deduced sequent for the other rules, according to [set_li]
        *)
        let tl =
          if a_uid = b_uid then
            FormulaSet.fold
              (fun s acc ->
                let s_uid = get_uid s in
                (a_uid, s_uid) :: (s_uid, a_uid) :: acc)
              subformulas tl
          else tl
        in
        let tl =
          List.fold_right
            (fun (_tag, set_fn, x, fn_pair) acc ->
              FmUidSet.fold (fun s acc -> fn_pair s acc) (set_fn x) acc)
            set_li tl
        in
        add tl
  in
  add worklist

(*
  Conversion to shape formula in order to order conjunctive normalization
  and DIMACS writings.
*)

let rec olsc_formula_to_formula pol = function
  | Lit (_, b) -> Logic.Lit (b && pol)
  | Var (_, _, v) when pol -> Logic.Var (fresh_formula_uid (), v)
  | Var _ as s -> Logic.Not (fresh_formula_uid (), olsc_formula_to_formula (not pol) s)
  | Not (_, s) -> olsc_formula_to_formula (not pol) s
  | And (_, ss) when pol ->
      Logic.And (fresh_formula_uid (), List.map (olsc_formula_to_formula pol) ss)
  | Or (_, ss) when pol ->
      Logic.Or (fresh_formula_uid (), List.map (olsc_formula_to_formula pol) ss)
  | And (_, ss) ->
      Logic.Or (fresh_formula_uid (), List.map (olsc_formula_to_formula pol) ss)
  | Or (_, ss) ->
      Logic.And (fresh_formula_uid (), List.map (olsc_formula_to_formula pol) ss)

let equivalence_checking' af =
  let equivs = Hashtbl.create 8 in
  let af_fm_map = Hashtbl.create 8 in

  let fm = aig_formula_to_olsc_formula af_fm_map equivs true af in

  (*
  Renames the intermediate variables.
  *)
  let rename = Hashtbl.create 8 in
  Hashtbl.iter
    (fun k _ ->
      let fresh_vn = fresh_counter var_counter in
      Hashtbl.replace rename k (fresh_vn, make_var false fresh_vn))
    equivs;

  let equivs' = Hashtbl.create 8 in

  (*
  Crafts the equivalent formula.
  *)
  let gm =
    Hashtbl.fold
      (fun k (xv, v) acc ->
        Hashtbl.replace equivs' k (xv, v);
        let k', var = Hashtbl.find rename k in
        (match subst_fm rename v with
        | None -> Hashtbl.replace equivs' k' (var, v)
        | Some s -> Hashtbl.replace equivs' k' (var, s));
        (* Printf.printf "%d -> %d\n%!" k k';  *)
        if fm_eq xv fm then var else acc)
      equivs fm
  in

  (* Printf.printf "Proving %s |- %s\n%!" (str_fm true fm) (str_fm true gm); *)

  (*
    Builds the axiomatization for the equivalence problem modulo renaming.
  *)
  let axioms, subs =
    Hashtbl.fold
      (fun _ (var, v) (acc, subs) ->
        let neg_var = negate var in
        let neg_val = negate v in

        let sfs = subformulas v in
        let subs = FormulaSet.union subs sfs in

        let sfs = subformulas neg_val in
        let subs = FormulaSet.union subs sfs in

        let subs = FormulaSet.add var subs in
        let subs = FormulaSet.add neg_var subs in

        (neg_var, v) :: (var, neg_val) :: acc, subs)
      equivs' ([], FormulaSet.empty)
  in
  let neg_fm = negate fm in
  let subs = FormulaSet.add neg_fm subs in
  let subs = FormulaSet.add gm subs in

  prove (negate fm, gm) axioms subs

let benchmark circuit_names =
  let rec run = function
    | [] -> ()
    | fn :: tl ->
        let _, aig_box = Aiger.parse fn in
        List.iteri
          (fun k (_, aig_formula) ->
            (* let k = 2 in
        let _, aig_formula = List.nth aig_box k in *)
            reset ();
            let current_time = Sys.time () in
            let res = equivalence_checking' aig_formula in
            let delta_time = Sys.time () -. current_time in
            Printf.printf "[benchmark] %s-%d -- %b -- %fs\n%!" fn k res delta_time)
          aig_box;
        run tl
  in
  run circuit_names
