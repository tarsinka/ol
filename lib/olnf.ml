open Logic

type olnf_finger_print = {
  (*
    Fingerprint for the normalization formulas.

    [uid] the unique identifier
    [inv] the negation of the formula, initially null
    [nrm] the normal form of the formula, initially null
    [smr] the hash table mapping, for each formula, whether it is smaller
    [lgr] the hash table mapping, for each formula, whether it is larger 
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

(*
  Transforms the AIG formula to a OLNF formula 
  with the shape of a DAG (with memoization).

  Remark that it is an implicit transformation
  to negative normal form (NNF).
*)

let aig_formula_to_olnf_formula s =
  let mem = Hashtbl.create 8 in
  let rec transform pol s =
    match Hashtbl.find_opt mem (pol, s) with
    | Some t -> t
    | None ->
        let res =
          match s with
          | AIGLit b -> if pol then MLit b else MLit (not b)
          | AIGVar v -> MVar (fresh_olnf_finger_print (), v, pol)
          | AIGNot t -> transform (not pol) t
          | AIGAnd (_, ch) ->
              MAnd (fresh_olnf_finger_print (), List.map (transform pol) ch, pol)
        in
        Hashtbl.replace mem (pol, s) res;
        res
  in
  transform true s

let olnf_formula_to_formula s =
  let mem = Hashtbl.create 8 in
  let rec transform s =
    let s_fg = fingerprint_min_formula s in
    match Hashtbl.find_opt mem s_fg.uid with
    | Some t -> t
    | None ->
        let res =
          match s with
          | MLit b -> Lit b
          | MVar (_, vn, true) -> Var (fresh_formula_uid (), vn)
          | MVar (_, vn, false) -> negate (Var (fresh_formula_uid (), vn))
          | MAnd (_, ch, true) -> And (fresh_formula_uid (), List.map transform ch)
          | MAnd (_, ch, false) -> Or (fresh_formula_uid (), List.map transform ch)
        in
        Hashtbl.replace mem s_fg.uid res;
        res
  in
  transform s

let negation = function
  | MLit pol -> MLit (not pol)
  | MVar (_, name, pol) -> MVar (fresh_olnf_finger_print (), name, not pol)
  | MAnd (_, children, pol) -> MAnd (fresh_olnf_finger_print (), children, not pol)

let inverse s =
  let fg = fingerprint_min_formula s in
  match fg.inv with
  | Some t -> t
  | None ->
      let inv = negation s in
      let inv_fg = fingerprint_min_formula inv in
      fg.inv <- Some inv;
      inv_fg.inv <- Some s;
      inv

(*
    Checks the order [s] < [t]
*)

let rec lat_ord s t =
  let s_fg = fingerprint_min_formula s in
  let t_fg = fingerprint_min_formula t in

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
      Printf.printf "%s < %s ? %b\n" (show_min_formula s) (show_min_formula t) r;
      r

let simplify children pol =
  let s = MAnd (fresh_olnf_finger_print (), children, pol) in
  Printf.printf "zeta %s\n" (show_min_formula s);
  let rec zeta s_ch =
    match s_ch with
    | MLit _ | MVar _ -> [ s_ch ]
    | MAnd (_, ch, true) -> ch
    | MAnd (_, ch, false) when pol -> (
        (* let ch = List.map inverse ch in *)
        let gt_opt = List.find_opt (lat_ord s) ch in
        match gt_opt with None -> [ s_ch ] | Some gt -> zeta gt)
    | MAnd (_, ch, false) -> (
        let ch = List.map inverse ch in
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
  let r =
    match lat_ord_filter [] new_ch with
    | [] -> MLit pol
    | [ c ] -> if pol then c else inverse c
    | res -> MAnd (fresh_olnf_finger_print (), List.rev res, pol)
  in
  Printf.printf "= %s\n" (show_min_formula r);
  r

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
        | MVar (_, vn, true) -> MVar (fresh_olnf_finger_print (), vn, true)
        | MVar (_, _, false) -> inverse (olnf (inverse s))
        | MAnd (_, ch, pol) ->
            let simp = simplify (List.map olnf ch) pol in
            if contradiction_check simp then MLit (not pol) else simp
      in
      fg.nrm <- Some nrm;
      nrm
