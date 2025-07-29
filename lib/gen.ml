open Aiger

type formula =
  | T of bool
  | SLit of fgprint * int * bool
  | SAnd of fgprint * formula list
  | SOr of fgprint * formula list

and fgprint = {
  uid : int;
  mutable neg : formula option;
  mutable pol : polar option;
  mutable red : bool option;
  mutable bnf : formula option;
  mutable znf : formula option;
  mutable enf : formula option;
  lt : (int, bool) Hashtbl.t;
}

and polar =
  | PLit of bool
  | PVar of pfgprint * int * bool
  | PAnd of pfgprint * polar list * bool

and pfgprint = {
  puid : int;
  mutable inverse : polar option;
  mutable nnf : polar option;
  mutable pos : formula option;
  mutable neg : formula option;
  lt : (int, bool) Hashtbl.t;
}

module Vars = Set.Make (Int)

let fm_uid = ref (-2)

let fresh_fm_uid () =
  fm_uid := !fm_uid - 1;
  !fm_uid

let var_uid = ref 1

let fresh_var_uid () =
  var_uid := !var_uid + 1;
  !var_uid

let reset () =
  fm_uid := 0;
  var_uid := 0

let str_uid _f = (* let fg = get_fgprint f in
  string_of_int fg.uid ^ "@" *) ""

let rec str_formula f =
  match f with
  | T true -> "t"
  | T false -> "f"
  | SLit (_, k, pol) ->
      let neg = if pol then "" else "~" in
      str_uid f ^ neg ^ string_of_int k
  | SAnd (_, cnj) ->
      str_uid f ^ "(" ^ String.concat " ^ " (List.map str_formula cnj) ^ ")"
  | SOr (_, dsj) -> str_uid f ^ "(" ^ String.concat " v " (List.map str_formula dsj) ^ ")"

let new_fg i j =
  {
    uid = i;
    neg = None;
    pol = None;
    red = None;
    bnf = None;
    znf = None;
    enf = None;
    lt = Hashtbl.create j;
  }

let fresh_fg () = new_fg (fresh_fm_uid ()) 5
let empty_fg_true = new_fg (-1) 0
let empty_fg_false = new_fg (-2) 0

let get_fgprint = function
  | T true -> empty_fg_true
  | T false -> empty_fg_false
  | SLit (fg, _, _) | SAnd (fg, _) | SOr (fg, _) -> fg

let new_lit i pol =
  if i >= !var_uid then var_uid := i;
  SLit (fresh_fg (), i, pol)

(*
  Returns the size not considering the possible
  other occurences of each subformula of [fm]
*)

let get_virtual_size fm =
  let uid_hs = Hashtbl.create 8 in
  let rec go = function
    | T _ | SLit _ -> 1
    | SAnd (_, sbs) | SOr (_, sbs) ->
        List.length sbs + List.fold_left (fun sum s -> sum + og s) 0 sbs
  and og fm =
    let fg = get_fgprint fm in
    match Hashtbl.find_opt uid_hs fg.uid with
    | Some _ -> 0
    | None ->
        let size = go fm in
        (* Printf.printf "%d @ %s ==s %d\n\n" fg.uid (str_formula fm) size; *)
        Hashtbl.add uid_hs fg.uid size;
        size
  in
  og fm

let new_and cnj =
  let fg = fresh_fg () in
  SAnd (fg, cnj)

let new_or dsj =
  let fg = fresh_fg () in
  SOr (fg, dsj)

let vars f =
  let hs = Hashtbl.create 5 in
  let rec aux f =
    let fg = get_fgprint f in
    match Hashtbl.find_opt hs fg.uid with
    | Some vrs -> vrs
    | None ->
        let res =
          match f with
          | T _ -> Vars.empty
          | SLit (_, k, _) -> Vars.singleton k
          | SAnd (_, l) | SOr (_, l) ->
              List.fold_left (fun acc s -> Vars.union acc (aux s)) Vars.empty l
        in
        Hashtbl.add hs fg.uid res;
        res
  in
  aux f

let eq f g =
  match f, g with
  | SLit (_, uida, pola), SLit (_, uidb, polb) -> uida = uidb && pola = polb
  | SAnd (fga, _), SAnd (fgb, _) | SOr (fga, _), SOr (fgb, _) -> fga.uid = fgb.uid
  | _ -> false

let rec eq_syn f g =
  match f, g with
  | SLit _, SLit _ -> eq f g
  | SAnd (_, sf), SAnd (_, sg) | SOr (_, sf), SOr (_, sg) -> List.for_all2 eq_syn sf sg
  | _ -> false

let rec contains f sub =
  if eq_syn f sub then Some f
  else
    match f with
    | SAnd (_, c) | SOr (_, c) ->
        List.fold_right
          (fun s acc -> match acc with None -> contains s sub | _ -> acc)
          c None
    | _ -> None

let rec negate f =
  match f with
  | T pol -> T (not pol)
  | SLit (_, k, pol) -> new_lit k (not pol)
  | SAnd (_, cnj) -> new_or (List.map get_neg cnj)
  | SOr (_, dsj) -> new_and (List.map get_neg dsj)

and get_neg f =
  let fg = get_fgprint f in
  match fg.neg with
  | Some neg -> neg
  | None ->
      let neg = negate f in
      let nfg = get_fgprint neg in
      nfg.neg <- Some f;
      fg.neg <- Some neg;
      neg

(*
  Syntactic sugar
*)

let new_imp f g = new_or [ get_neg f; g ]
let new_equiv f g = new_and [ new_imp f g; new_imp g f ]

let flatten f =
  let hs = Hashtbl.create 8 in

  Printf.printf "flatten\n%!";

  let rec acc s =
    match s with
    | SAnd (_, cnj) ->
        let cnj =
          List.fold_left
            (fun acc s ->
              let xx = aux s in
              match xx with SAnd (_, cnj) -> cnj @ acc | T true -> acc | _ -> xx :: acc)
            [] cnj
        in
        new_and cnj
    | SOr (_, dsj) ->
        let dsj =
          List.fold_left
            (fun acc s ->
              let xx = aux s in
              match xx with
              | SAnd _ -> failwith "A CNF was expected"
              | SOr (_, dsj) -> dsj @ acc
              | _ -> xx :: acc)
            [] dsj
        in
        new_or dsj
    | _ -> s
  and aux s =
    let fg = get_fgprint s in
    match Hashtbl.find_opt hs fg.uid with
    | Some flt -> flt
    | None ->
        let flt = acc s in
        Hashtbl.add hs fg.uid flt;
        flt
  in
  aux f

let rec is_clause = function
  | SAnd _ -> false
  | SOr (_, dsj) -> List.for_all is_clause dsj
  | _ -> true

let simpl f =
  (*
      Distribution of the OR : 
      (a and b) or (c and d) = (a or c) and (a or d) and (b or c) and (b or d)
  *)

  (*
    If the formula is a clause, just returns it.
  *)
  if is_clause f then f
  else
    let hs = Hashtbl.create 8 in

    (* Printf.printf "simpl f size -- %d\n%s\n%!" (get_virtual_size f) (str_formula f); *)
    let rec atom_or_dist atm s =
      match s with
      | T false -> atm
      | T true -> T true
      | SLit _ -> new_or [ atm; s ]
      | SOr (_, []) -> atm
      | SAnd (_, cnj) ->
          let cnj = List.fold_right (fun c acc -> new_or [ atm; c ] :: acc) cnj [] in
          new_and cnj
      | SOr (_, dsj) -> new_or (atm :: dsj)
    and or_dist f s =
      match f with
      | T _ | SLit _ -> atom_or_dist f s
      | SAnd (_, cnj) ->
          let cnj =
            List.fold_right
              (fun c acc ->
                let smp = aux (atom_or_dist c s) in
                smp :: acc)
              cnj []
          in
          new_and cnj
      | SOr (_, dsj) -> List.fold_right (fun d acc -> aux (atom_or_dist d acc)) dsj s
    and acc s =
      match s with
      | SAnd (_, [ x ]) | SOr (_, [ x ]) -> aux x
      | SOr (_, dsj) ->
          (* Printf.printf "acc %s\n" (str_formula s); *)
          let rec split = function
            | [] -> new_or []
            | s :: tl -> or_dist (aux s) (split tl)
          in
          split dsj
      | _ -> s
    and aux s =
      let fg = get_fgprint s in
      match Hashtbl.find_opt hs fg.uid with
      | Some smp -> smp
      | None ->
          let res = acc s in
          Hashtbl.add hs fg.uid res;
          (* Printf.printf "None %d @ %s\n%!" fg.uid (str_formula s); *)
          res
    in
    aux f

(*
    Generates an instantiation of the shape by 
    constructing a DAG of the formula to share
    the same sub-formulas
*)

let get_lits lts fv fb =
  match Hashtbl.find_opt lts (fv, fb) with
  | None ->
      let lit = new_lit fv fb in
      if fv > !var_uid then var_uid := fv else ();
      Hashtbl.add lts (fv, fb) lit;
      lit
  | Some l -> l

let inst sh kd n =
  let lts = Hashtbl.create n in
  let rec inst_rec sh kd up =
    match sh with
    | [] ->
        let fv = Random.int n + 1 in
        let fb = Random.bool () in
        get_lits lts fv fb
    | k :: sh ->
        let li = inst_li sh (not kd) [] up k in
        if kd then new_and li else new_or li
  and inst_li sh kd fli up = function
    | 0 -> fli
    | k ->
        let nf = inst_rec sh kd up in
        let nf =
          List.fold_right
            (fun s sub -> match contains s sub with None -> sub | Some v -> v)
            up nf
        in
        inst_li sh kd (nf :: fli) (nf :: up) (k - 1)
  in
  inst_rec sh kd []

let rec bind hs equiv f =
  let bind_op fg c pol =
    match Hashtbl.find_opt equiv fg.uid with
    | Some fv -> fv
    | None ->
        let nc =
          List.fold_right
            (fun s acc ->
              let lit = bind hs equiv s in
              if List.exists (eq lit) acc then acc else lit :: acc)
            c []
        in
        let fv = fresh_var_uid () in

        let fm = if pol then new_and nc else new_or nc in

        let lt = new_lit fv true in
        Hashtbl.add equiv fg.uid lt;
        Hashtbl.add hs fv (lt, fm);

        (* Printf.printf "%d <-> %s\n" fv (str_formula fm); *)
        lt
  in
  match f with
  | T _ | SLit _ -> f
  | SAnd (i, c) -> bind_op i c true
  | SOr (i, c) -> bind_op i c false

let cnf f =
  let hs = Hashtbl.create 8 in
  let eq = Hashtbl.create 8 in
  let lt = bind hs eq f in
  let conj =
    Hashtbl.fold
      (fun _ (lt, v) conj -> simpl (new_imp lt v) :: simpl (new_imp v lt) :: conj)
      hs [ lt ]
  in
  flatten (new_and conj)

let model sh n r =
  let rn = int_of_float (r *. float_of_int n) in
  let rec aux = function
    | 0 -> []
    | k ->
        let i = inst sh false n in
        i :: aux (k - 1)
  in
  new_and (aux rn)

let rec pow f = function 0 -> 1. | k -> f *. pow f (k - 1)
let rec prob = function [] -> 0.5 | k :: sh -> 1. -. pow (prob sh) k

(*
  OL normalization
*)

(* let rec lat_ord f g =
  let f_fg = get_fgprint f in
  let g_fg = get_fgprint g in

  if eq f g then true
  else
    match Hashtbl.find_opt f_fg.lt g_fg.uid with
    | Some b -> b
    | None ->
        let res =
          match f, g with
          | T pola, T polb -> (not pola) || polb
          | T pol, _ -> not pol
          | _, T pol -> pol
          | SLit _, SLit _ -> eq f g
          | _, SAnd (_, li) -> List.for_all (lat_ord f) li
          | SOr (_, li), _ -> List.for_all (fun s -> lat_ord s g) li
          | SLit _, SOr (_, li) -> List.exists (lat_ord f) li
          | SAnd (_, li), SLit _ -> List.exists (fun s -> lat_ord s g) li
          | SAnd (_, li_f), SOr (_, li_g) ->
              List.exists (fun s -> lat_ord s g) li_f || List.exists (lat_ord f) li_g
        in
        Hashtbl.add f_fg.lt g_fg.uid res;
        res

let rec is_reduced f =
  let aux pol =
    List.for_all (fun s ->
        let neg = get_neg s in
        let r = if pol then lat_ord f neg else lat_ord neg f in
        (not r) && get_reduced s)
  in
  match f with SAnd (_, cnj) -> aux true cnj | SOr (_, dsj) -> aux false dsj | _ -> true

and get_reduced f =
  let fg = get_fgprint f in
  match fg.red with
  | Some v -> v
  | None ->
      let red = is_reduced f in
      fg.red <- Some red;
      red

let rec beta_normal_form f =
  let aux pol li =
    let np = List.map get_beta li in
    let rr = if pol then new_and np else new_or np in
    if get_reduced rr then rr else T (not pol)
  in
  match f with SAnd (_, li) -> aux true li | SOr (_, li) -> aux false li | _ -> f

and get_beta f =
  let fg = get_fgprint f in
  match fg.bnf with
  | Some v -> v
  | None ->
      let beta = beta_normal_form f in
      fg.bnf <- Some beta;
      beta

let rec zeta_normal_form f =
  let check_sub hd p pred (flag, acc) =
    match List.find_opt pred p with None -> flag, hd :: acc | Some v -> true, v :: acc
  in
  let rec check_sup pol (flag, acc) = function
    | [] -> flag, acc
    | (SAnd (_, cnj) as hd) :: tl when not pol ->
        check_sup pol (check_sub hd cnj (fun e -> lat_ord e f) (flag, acc)) tl
    | (SOr (_, dsj) as hd) :: tl when pol ->
        check_sup pol (check_sub hd dsj (lat_ord f) (flag, acc)) tl
    | hd :: tl -> check_sup pol (flag, hd :: acc) tl
  in
  match f with
  | SOr (_, dsj) ->
      let fl, dsj' = check_sup false (false, []) dsj in
      if fl then zeta_normal_form (new_or dsj') else new_or (List.map get_zeta dsj)
  | SAnd (_, cnj) ->
      let fl, cnj' = check_sup true (false, []) cnj in
      if fl then zeta_normal_form (new_and cnj') else new_and (List.map get_zeta cnj)
  | _ -> f

and get_zeta f =
  let fg = get_fgprint f in
  match fg.znf with
  | Some v -> v
  | None ->
      let zeta = zeta_normal_form f in
      fg.znf <- Some zeta;
      zeta

let rec eta_normal_form f =
  let chk pol s t = if pol then lat_ord t s else lat_ord s t in
  let rec check_sup pol fst fl = function
    | [] -> fl, fst
    | s :: tl ->
        if List.exists (chk pol s) tl || List.exists (chk pol s) fst then true, fst @ tl
        else check_sup pol (s :: fst) fl tl
  in
  match f with
  | SOr (_, dsj) ->
      let fl, dsj' = check_sup false [] false dsj in
      if fl then eta_normal_form (new_or dsj') else new_or (List.map get_eta dsj)
  | SAnd (_, cnj) ->
      let fl, cnj' = check_sup true [] false cnj in
      if fl then eta_normal_form (new_and cnj') else new_and (List.map get_eta cnj)
  | _ -> f

and get_eta f =
  let fg = get_fgprint f in
  match fg.enf with
  | Some v -> v
  | None ->
      let eta = eta_normal_form f in
      fg.enf <- Some eta;
      eta

let ol_nf f =
  let bta = get_beta f in
  Printf.printf "Beta done\n%!";
  let zta = get_zeta bta in
  Printf.printf "Zeta done\n%!";
  get_eta zta *)
(*
    Conversion from AIGER

    We keep the intermediate variables by making the equivalence
    between the And operator they are bound to.
*)

let aig_to_sf hdr ctx_vars ctx_gates af =
  let sup = 2 * hdr.i in
  let equivs = Hashtbl.create 16 in
  let extract_from_ctx ctx i v pol =
    match Hashtbl.find_opt ctx i with
    | Some v -> v
    | None ->
        let res = new_lit v pol in
        Hashtbl.add ctx i res;
        res
  in
  let rec aux pol = function
    | Lit t -> T (pol = t)
    | Var i ->
        let i = i / 2 in
        let fv = extract_from_ctx ctx_vars i i true in
        let fv = if pol then fv else get_neg fv in
        if i >= sup && not (Hashtbl.mem ctx_gates i) then Hashtbl.add ctx_gates i fv;
        fv
    | And (k, ch) -> (
        let k = k / 2 in
        match Hashtbl.find_opt equivs k with
        | Some _ ->
            let fv = Hashtbl.find ctx_gates k in
            if pol then fv else get_neg fv
        | None ->
            let ch = List.map (aux true) ch in
            let rg = new_and ch in
            let fr = fresh_var_uid () in
            let fv = extract_from_ctx ctx_gates k fr true in
            (* Printf.printf "%d <-> %s\n" fr (str_formula rg); *)
            Hashtbl.replace equivs k (new_equiv fv rg);
            if pol then fv else get_neg fv)
    | Not f -> aux (not pol) f
  in
  let _fv = aux true af in
  (* Printf.printf "Ret form %s\n" (str_formula fv); *)
  let cnj = Hashtbl.fold (fun _ v acc -> v :: acc) equivs [] in
  new_and cnj

let sf_of_aig hdr aig =
  let lts = Array.make (2 * (hdr.i + 1)) None in
  let fms = Array.make (2 * (hdr.m + 2)) None in
  let test ctx i pol gen_f =
    let ind = i + if pol then 0 else 1 in
    match ctx.(ind) with
    | None ->
        let v = gen_f () in
        (* if i = out_id then Hashtbl.add bds i !var_uid; *)
        let fg = get_fgprint v in
        fg.neg <- Some (get_neg v);
        ctx.(ind) <- Some v;
        v
    | Some v -> v
  in
  let rec aux pol = function
    | Lit t -> T (pol = t)
    | Var i -> test lts i pol (fun () -> new_lit i pol)
    | And (k, cnj) when not pol ->
        test fms k pol (fun () -> new_or (List.map (aux pol) cnj))
    | And (k, cnj) -> test fms k pol (fun () -> new_and (List.map (aux pol) cnj))
    | Not f -> aux (not pol) f
  in
  aux true aig

(*
  Polar version
*)

let polar_uid = ref (-2)

let fresh_polar_uid () =
  polar_uid := !polar_uid - 1;
  !polar_uid

let build_fg uid =
  {
    puid = uid;
    inverse = None;
    nnf = None;
    pos = None;
    neg = None;
    lt = Hashtbl.create 8;
  }

let truth_fg = build_fg (-1)
let false_fg = build_fg (-2)
let new_plit pol = PLit pol
let new_pvar id pol = PVar (build_fg (fresh_polar_uid ()), id, pol)
let new_pand ch pol = PAnd (build_fg (fresh_polar_uid ()), ch, pol)

let rec str_polar = function
  | PLit true -> "t"
  | PLit false -> "f"
  | PVar (_, id, pol) ->
      let n = if pol then "" else "~" in
      Printf.sprintf "%s%d" n id
  | PAnd (_, ch, pol) ->
      let n = if pol then "" else "~" in
      let str = String.concat " ^ " (List.map str_polar ch) in
      Printf.sprintf "%s(%s)" n str

let get_polar_fg = function
  | PLit true -> truth_fg
  | PLit false -> false_fg
  | PVar (pfg, _, _) | PAnd (pfg, _, _) -> pfg

let flatten_polar pf =
  let hs = Hashtbl.create 8 in

  let rec go = function
    | PAnd (_, li, pol) ->
        let li =
          List.fold_right
            (fun s acc ->
              match og s with
              | PAnd (_, li, pol') when pol = pol' -> li @ acc
              | s -> s :: acc)
            li []
        in
        new_pand li pol
    | s -> s
  and og f =
    let pfg = get_polar_fg f in
    match Hashtbl.find_opt hs pfg.puid with
    | Some flt -> flt
    | None ->
        let flt = go f in
        Hashtbl.add hs pfg.puid flt;
        flt
  in
  og pf

let get_inverse pf =
  let pfg = get_polar_fg pf in
  match pfg.inverse with
  | Some inv -> inv
  | None ->
      let res =
        match pf with
        | PLit pol -> new_plit (not pol)
        | PVar (_, id, pol) -> new_pvar id (not pol)
        | PAnd (_, ch, pol) -> new_pand ch (not pol)
      in
      pfg.inverse <- Some res;
      let res_pfg = get_polar_fg res in
      res_pfg.inverse <- Some pf;
      res

let rec polarize pol f =
  let fg = get_fgprint f in
  match fg.pol with
  | Some pf -> if pol then pf else get_inverse pf
  | None ->
      let res =
        match f with
        | T p -> new_plit (pol = p)
        | SLit (_, id, p) -> new_pvar id (pol = p)
        | SAnd (_, cnj) -> new_pand (List.map (polarize true) cnj) pol
        | SOr (_, dsj) -> new_pand (List.map (polarize false) dsj) (not pol)
      in
      if pol then fg.pol <- Some res else fg.pol <- Some (get_inverse res);
      res

let get_polar_virtual_size f =
  let hs = Hashtbl.create 8 in
  let rec go = function
    | PLit _ | PVar _ -> 1
    | PAnd (_, li, _) ->
        List.length li + List.fold_left (fun sum s -> sum + og s) 0 li
  and og f =
    let fg = get_polar_fg f in
    match Hashtbl.mem hs fg.puid with
    | true -> 0
    | _ ->
        let size = go f in
        Hashtbl.add hs fg.puid size;
        size
  in
  og f

let rec lat_leq f g =
  let f_fg = get_polar_fg f in
  let g_fg = get_polar_fg g in

  if f_fg.puid = g_fg.puid then true
  else
    match Hashtbl.find_opt f_fg.lt g_fg.puid with
    | Some b -> b
    | None ->
        let res =
          match f, g with
          | PLit pola, PLit polb -> (not pola) || polb
          | PLit pol, _ -> not pol
          | _, PLit pol -> pol
          | PVar (_, ida, pola), PVar (_, idb, polb) -> ida = idb && pola = polb
          | _, PAnd (_, li, true) -> List.for_all (lat_leq f) li
          | PAnd (_, li, false), _ -> List.for_all (fun s -> lat_leq (get_inverse s) g) li
          | PVar _, PAnd (_, li, false) ->
              List.exists (fun s -> lat_leq f (get_inverse s)) li
          | PAnd (_, li, true), PVar _ -> List.exists (fun s -> lat_leq s g) li
          | PAnd (_, li_f, true), PAnd (_, li_g, false) ->
              List.exists (fun s -> lat_leq s g) li_f
              || List.exists (fun s -> lat_leq f (get_inverse s)) li_g
        in
        Hashtbl.add f_fg.lt g_fg.puid res;
        res

let simplify pol tch =
  let ns = new_pand tch pol in
  let rec zeta z =
    match z with
    | PAnd (_, ch, true) -> ch
    | PAnd (_, ch, false) -> (
        if pol then
          let ch = List.map get_inverse ch in
          match List.find_opt (lat_leq ns) ch with Some s -> zeta s | None -> [ z ]
        else
          match List.find_opt (fun s -> lat_leq s ns) ch with
          | Some s -> zeta (get_inverse s)
          | None -> [ z ])
    | _ -> [ z ]
  in
  let rec eta acc = function
    | [] -> acc
    | s :: tl ->
        (*
          This is where it consideraly slows down when [tch] gets bigger !
        *)

        (* Printf.printf "%d\n%!" (List.length tl); *)
        let b = lat_leq (new_pand (acc @ tl) true) s in
        if b then eta acc tl else eta (s :: acc) tl
  in
  let zeta_rems = List.flatten (List.map zeta tch) in
  match eta [] zeta_rems with
  | [] -> new_plit pol
  | [ s ] -> if pol then s else get_inverse s
  | ss -> new_pand ss pol

let contradiction f =
  match f with
  | PAnd (_, ch, false) -> List.exists (fun s -> lat_leq s f) ch
  | PAnd (_, ch, true) ->
      let ch = List.map get_inverse ch in
      List.exists (lat_leq f) ch
  | _ -> false

let rec nnf pf =
  let pfg = get_polar_fg pf in
  match pfg.nnf with
  | Some nnf -> nnf
  | None ->
      let res =
        match pf with
        | PLit pol -> new_plit pol
        | PVar (_, id, pol) -> new_pvar id pol
        (* | PVar (_, _, false) -> get_inverse (nnf (get_inverse pf)) *)
        | PAnd (_, ch, pol) ->
            let ch = List.map nnf ch in
            let smp = simplify pol ch in
            if contradiction smp then new_plit (not pol) else smp
      in
      pfg.nnf <- Some res;
      res

let rec polar_to_fm pol pf =
  let inv = get_inverse pf in
  let pfg = get_polar_fg pf in
  let inv_pfg = get_polar_fg inv in
  match pfg.pos, pfg.neg, inv_pfg.pos, inv_pfg.neg with
  | Some fm, _, _, _ when pol -> fm
  | _, Some fm, _, _ when not pol -> fm
  | _, _, Some fm, _ when not pol -> fm
  | _, _, _, Some fm when pol -> fm
  | _ ->
      let fm =
        match pf with
        | PLit p -> T (p == pol)
        | PVar (_, id, p) -> new_lit id (pol == p)
        | PAnd (_, ch, p) ->
            let ch = List.map (polar_to_fm (p == pol)) ch in
            if p = pol then new_and ch else new_or ch
      in
      if pol then pfg.pos <- Some fm else pfg.neg <- Some fm;
      fm

let olnf' f =
  let plr = polarize true f in
  (* let plr = flatten_polar plr in *)
  Printf.printf "POL done %d nodes\n%!" (get_polar_virtual_size plr);
  let nnf = nnf plr in
  Printf.printf "NNF done\n%!";
  let fm = polar_to_fm true nnf in
  Printf.printf "OL done\n%!";
  fm
