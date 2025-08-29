open Logic

type olnf_finger_print = {
  (*
    Fingerprint for the normalization formulas.

    [uid] the unique identifier
    [inv] the negation of the formula, initially null
    [nrm] the normal form of the formula, initially null
    [lt] the hash table mapping, for each formula, whether it is smaller
  *)
  uid : int;
  mutable inv : olnf_finger_print min_formula option;
  mutable nrm : olnf_finger_print min_formula option;
  lt : (int, bool) Hashtbl.t;
}

type olnf_formula = olnf_finger_print min_formula

let olnf_uid = ref 0

let fresh_olnf_finger_print () =
  { uid = incr olnf_uid; inv = None; nrm = None; lt = Hashtbl.create 4 }

let unit_finger_print () = { uid = 0; inv = None; nrm = None; lt = Hashtbl.create 0 }

let fingerprint_min_formula = function
  | MLit _ -> unit_finger_print ()
  | MVar (fg, _, _) | MAnd (fg, _, _) -> fg

let get_olnf_formula_uid s =
  let s_fg = fingerprint_min_formula s in
  s_fg.uid

let reset () = olnf_uid := 0

let olnf_formula_size s =
  let mem = Hashtbl.create 8 in
  let rec go s =
    let uid = get_olnf_formula_uid s in
    match Hashtbl.mem mem uid with
    | true -> 0
    | _ ->
        let size =
          match s with
          | MLit _ | MVar _ -> 1
          | MAnd (_, ch, _) -> 1 + List.fold_left (fun sum c -> sum + go c) 0 ch
        in
        Hashtbl.replace mem uid size;
        size
  in
  go s

let inverse s =
  let fg = fingerprint_min_formula s in
  match fg.inv with
  | Some t -> t
  | None ->
      let inv =
        match s with
        | MLit pol -> MLit (not pol)
        | MVar (_, name, pol) -> MVar (fresh_olnf_finger_print (), name, not pol)
        | MAnd (_, children, pol) -> MAnd (fresh_olnf_finger_print (), children, not pol)
      in
      let inv_fg = fingerprint_min_formula inv in
      fg.inv <- Some inv;
      inv_fg.inv <- Some s;
      inv

(*
  Transforms the AIG formula to a OLNF formula 
  with the shape of a DAG (with memoization).

  It is an implicit transformation to negative 
  normal form (NNF).
*)

let aig_formula_to_olnf_formula s =
  let mem = Hashtbl.create 8 in
  let rec transform pol s =
    match Hashtbl.find_opt mem (pol, s) with
    | Some t -> if pol then t else inverse t
    | None ->
        let res =
          match s with
          | AIGLit b -> MLit (b = pol)
          | AIGVar v -> MVar (fresh_olnf_finger_print (), v, pol)
          | AIGNot t -> transform (not pol) t
          | AIGAnd (_, u, v) ->
              MAnd
                (fresh_olnf_finger_print (), [ transform true u; transform true v ], pol)
        in
        if pol then Hashtbl.replace mem (pol, s) res
        else Hashtbl.replace mem (pol, s) (inverse res);
        res
  in
  transform true s

let olnf_formula_to_formula s =
  let mem_pos = Hashtbl.create 8 in
  let mem_neg = Hashtbl.create 8 in
  let rec transform pol s =
    let s_fg = fingerprint_min_formula s in
    match
      Hashtbl.find_opt mem_pos s_fg.uid, Hashtbl.find_opt mem_neg s_fg.uid, s_fg.inv
    with
    | Some t, _, _ when pol -> t
    | None, _, Some inv when pol && Hashtbl.mem mem_neg (get_olnf_formula_uid inv) ->
        Hashtbl.find mem_neg (get_olnf_formula_uid inv)
    | _, Some t, _ when not pol -> t
    | _, None, Some inv when (not pol) && Hashtbl.mem mem_pos (get_olnf_formula_uid inv)
      ->
        Hashtbl.find mem_pos (get_olnf_formula_uid inv)
    | _ ->
        let res =
          match s with
          | MLit b -> Lit (b = pol)
          | MVar (_, vn, s_pol) when s_pol = pol -> Var (fresh_formula_uid (), vn)
          | MVar _ -> Not (fresh_formula_uid (), transform (not pol) s)
          | MAnd (_, ch, s_pol) when s_pol = pol ->
              And (fresh_formula_uid (), List.map (transform true) ch)
          | MAnd (_, ch, _) -> Or (fresh_formula_uid (), List.map (transform false) ch)
        in
        if pol then Hashtbl.replace mem_pos s_fg.uid res
        else Hashtbl.replace mem_neg s_fg.uid res;
        res
  in
  transform true s

(*
    Checks the order [s] < [t] in OL.
*)

let rec lat_ord s t =
  let s_fg = fingerprint_min_formula s in
  let t_fg = fingerprint_min_formula t in

  if s_fg.uid = t_fg.uid then true
  else
    match Hashtbl.find_opt s_fg.lt t_fg.uid with
    | Some b -> b
    | None ->
        let r =
          match s, t with
          | MLit s_pol, MLit t_pol -> (not s_pol) || t_pol
          | MLit pol, _ -> not pol
          | _, MLit pol -> pol
          | MVar (_, s_nm, s_pol), MVar (_, t_nm, t_pol) -> s_nm = t_nm && s_pol = t_pol
          | _, MAnd (_, ch, true) -> List.for_all (lat_ord s) ch
          | MAnd (_, ch, false), _ -> List.for_all (fun c -> lat_ord (inverse c) t) ch
          | MVar _, MAnd (_, ch, false) -> List.exists (fun c -> lat_ord s (inverse c)) ch
          | MAnd (_, ch, true), MVar _ -> List.exists (fun c -> lat_ord c t) ch
          | MAnd (_, s_ch, true), MAnd (_, t_ch, false) ->
              List.exists (fun c -> lat_ord c t) s_ch
              || List.exists (fun c -> lat_ord s (inverse c)) t_ch
        in
        Hashtbl.replace s_fg.lt t_fg.uid r;
        r

let simplify children pol =
  let s = MAnd (fresh_olnf_finger_print (), children, pol) in
  let rec zeta s_ch =
    match s_ch with
    | MLit _ | MVar _ -> [ s_ch ]
    | MAnd (_, ch, true) -> ch
    | MAnd (_, ch, false) when pol -> (
        let gt_opt = List.find_opt (fun c -> lat_ord s (inverse c)) ch in
        match gt_opt with None -> [ s_ch ] | Some gt -> zeta (inverse gt))
    | MAnd (_, ch, false) -> (
        let gt_opt = List.find_opt (fun c -> lat_ord c s) ch in
        match gt_opt with None -> [ s_ch ] | Some gt -> zeta (inverse gt))
  in
  let new_ch = List.flatten (List.map zeta children) in
  (*
    Filters out redundant children smaller than another child
  *)
  let rec lat_ord_filter acc = function
    | [] -> acc
    | curr :: tl ->
        if lat_ord (MAnd (fresh_olnf_finger_print (), acc @ tl, true)) curr then
          lat_ord_filter acc tl
        else lat_ord_filter (curr :: acc) tl
  in
  match lat_ord_filter [] new_ch with
  | [] -> MLit pol
  | [ c ] -> if pol then c else inverse c
  | res -> MAnd (fresh_olnf_finger_print (), res, pol)

let contradiction_check s =
  match s with
  | MAnd (_, ch, false) -> List.exists (fun c -> lat_ord c s) ch
  | MAnd (_, ch, true) -> List.exists (fun c -> lat_ord s (inverse c)) ch
  | _ -> false

let rec olnf s =
  let fg = fingerprint_min_formula s in
  match fg.nrm with
  | Some nf -> nf
  | None ->
      let nrm =
        match s with
        | MLit _ -> s
        | MVar (_, vn, pol) -> MVar (fresh_olnf_finger_print (), vn, pol)
        | MAnd (_, ch, pol) ->
            let simp = simplify (List.map olnf ch) pol in
            if contradiction_check simp then MLit (not pol) else simp
      in
      fg.nrm <- Some nrm;
      nrm

let benchmark root =
  let circuits = Sys.readdir (root ^ "/aig") in
  Printf.printf "[olnf] benchmarking over %s\n%!" root;
  Array.iter
    (fun cn ->
      reset ();
      Logic.reset ();

      let fn = root ^ "/aig/" ^ cn in

      let _, aigs = Aiger.parse fn in
      let _, aig = List.nth aigs 0 in
      let mn = aig_formula_to_olnf_formula aig in
      let fm = olnf_formula_to_formula mn in

      let cnf_cl = cnf_formula_to_clauses (cnf fm) in

      let time = Sys.time () in
      let normal_form = olnf mn in
      let delta_time = Sys.time () -. time in

      let normal_form_fm = olnf_formula_to_formula normal_form in
      let cnf_ol = cnf_formula_to_clauses (cnf normal_form_fm) in

      let cnf_path = root ^ "/cnf" in

      Dimacs.write (cnf_path ^ "/" ^ cn ^ "_cl.cnf") cnf_cl;
      Dimacs.write (cnf_path ^ "/" ^ cn ^ "_ol.cnf") cnf_ol;

      Printf.printf "%s\t%d\t%d\t%f\n%!" cn (formula_size fm)
        (formula_size normal_form_fm) delta_time)
    circuits
