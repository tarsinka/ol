(*
  Classical formula
*)

type formula =
  | Lit of bool
  | Var of int
  | Neg of ol_fm
  | And of ol_fm list
  | Or of ol_fm list

(*
  Reduced formula
*)
and rformula = RLit of bool | RVar of int * bool | RAnd of ol_rm list * bool
and bio_fm = { u_key : int; mutable neg : ol_fm option; mutable nnf : ol_rm option }

and bio_rm = {
  u_key : int;
  mutable f : ol_fm option;
  mutable red : bool option;
  mutable bnf : ol_rm option;
  mutable znf : ol_rm option;
  mutable enf : ol_rm option;
}

and ol_fm = bio_fm * formula
and ol_rm = bio_rm * rformula

(*
    Constants
*)

let rec bot_ol = { u_key = 0; neg = Some top_ol; nnf = None }, Lit false
and top_ol = { u_key = 1; neg = Some bot_ol; nnf = None }, Lit true

let rbot_ol =
  ( { u_key = 0; f = Some bot_ol; red = None; bnf = None; znf = None; enf = None },
    RLit false )

let rtop_ol =
  ( { u_key = 1; f = Some top_ol; red = None; bnf = None; znf = None; enf = None },
    RLit true )

let get_rlit_bio = function false -> rbot_ol | _ -> rtop_ol
let unique_key_formula = ref 0
let unique_key_rformula = ref 0

let reset () =
  unique_key_formula := 0;
  unique_key_rformula := 0

let new_unique_key u_key =
  u_key := !u_key + 1;
  !u_key

let comp_rel = Stdlib.compare

module Rel = Set.Make (struct
  type t = int * int * bool

  let compare = comp_rel
end)

let rels = ref Rel.empty
let init s = { u_key = new_unique_key unique_key_formula; neg = None; nnf = None }, s

let init_rm s =
  ( {
      u_key = new_unique_key unique_key_formula;
      f = None;
      red = None;
      bnf = None;
      znf = None;
      enf = None;
    },
    s )

(*
    Get the list of variables of a formula
*)

module Vars = Set.Make (Int)

let rec vars_of (_, rf) =
  match rf with
  | RLit _ -> Vars.empty
  | RVar (i, _) -> Vars.singleton i
  | RAnd (li, _) ->
      List.fold_right (fun el acc -> Vars.union acc (vars_of el)) li Vars.empty

(*
    Semantics for rformulas
*)

let rec assign (_, rf) hs =
  match rf with
  | RLit _ -> ()
  | RVar (i, pol) -> Hashtbl.replace hs i pol
  | RAnd (li, _) -> List.iter (fun el -> assign el hs) li

let rec interpret assgn (_, rm) =
  match rm with
  | RLit pol -> pol
  | RVar (i, pol) ->
      let va = Hashtbl.find assgn i in
      if pol then va else not va
  | RAnd (li, true) -> List.for_all (interpret assgn) li
  | RAnd (li, false) -> List.exists (interpret assgn) li

let rec str_pp_rformula (_, rm) =
  match rm with
  | RLit true -> "t"
  | RLit false -> "f"
  | RVar (i, true) -> Format.sprintf "%d" i
  | RVar (i, false) -> Format.sprintf "~%d" i
  | RAnd (li, pol) ->
      let sep = if pol then " ∧ " else " v " in
      let str_li = List.fold_right (fun el acc -> str_pp_rformula el :: acc) li [] in
      "(" ^ String.concat sep str_li ^ ")"

(*
    Flattens the formula
*)

let rec flatten (rb, rm) =
  ( rb,
    match rm with
    | RAnd (li, pol) ->
        let res =
          List.fold_right
            (fun el acc ->
              let elb, el = flatten el in
              match el with
              | RAnd (li, p) when p = pol -> li @ acc
              | _ -> (elb, el) :: acc)
            li []
        in
        RAnd (res, pol)
    | _ -> rm )

(*
    Decides whether f < g.
    f and g being elements of a free latice.

    rformula -> rformula -> bool
*)

let rec lat_ord (f : ol_rm) (g : ol_rm) =
  let fb, fm = f in
  let gb, gm = g in

  (*
        If the relation f < g has already been computed, returns it.
    *)
  match Rel.find_first_opt (fun (i, j, _) -> i = fb.u_key && j = gb.u_key) !rels with
  | Some (_, _, b) -> b
  | None ->
      let res =
        match fm, gm with
        | RLit false, _ | _, RLit true -> true
        | RLit true, _ | _, RLit false -> false
        | RVar (i, p), RVar (j, q) -> p = q && i = j
        | RAnd (li_f, true), RAnd (li_g, false) ->
            List.exists (fun s -> lat_ord s g) li_f || List.exists (lat_ord f) li_g
        | RAnd (li, false), _ -> List.for_all (fun s -> lat_ord s g) li
        | _, RAnd (li, true) -> List.for_all (lat_ord f) li
        | RAnd (li, true), _ -> List.exists (fun s -> lat_ord s g) li
        | _, RAnd (li, false) -> List.exists (lat_ord f) li
      in

      (*
            Adds the newly computed relation
        *)
      rels := Rel.add (fb.u_key, gb.u_key, res) !rels;
      res

(*
    Negates a classical formula.
*)

let rec negate f =
  let fb, fm = f in
  let nb = { u_key = new_unique_key unique_key_formula; neg = Some f; nnf = None } in
  let res =
    match fm with
    | Lit true -> bot_ol
    | Lit false -> top_ol
    | Var _ -> nb, Neg f
    | Neg f_a -> f_a
    | And li -> nb, Or (List.map get_negate li)
    | Or li -> nb, And (List.map get_negate li)
  in
  fb.neg <- Some res;
  res

and get_negate (fb, fm) =
  match fb.neg with
  | Some v -> v
  | None ->
      let neg = negate (fb, fm) in
      fb.neg <- Some neg;
      neg

(*
    Simplification rules on rformulae
*)

let rec simpl_rformula rf =
  let rb, rm = rf in
  match rm with
  | RAnd ([], pol) -> rb, RLit pol
  | RAnd ([ x ], _) -> simpl_rformula x
  | RAnd (li, pol) ->
      let res =
        List.fold_right
          (fun (b, r) acc ->
            match r with RLit p when p = pol -> acc | _ -> simpl_rformula (b, r) :: acc)
          li []
      in
      rb, RAnd (res, pol)
  | _ -> rf

(*
    Takes a formula type and returns its NNF normalization.
    T_OL(X) -> T_L(X + X')
*)

let rec negative_normal_form f =
  let _, fm = f in
  let rb =
    {
      u_key = new_unique_key unique_key_rformula;
      f = Some f;
      red = None;
      bnf = None;
      znf = None;
      enf = None;
    }
  in
  let rf =
    match fm with
    | Lit true -> rtop_ol
    | Lit false -> rbot_ol
    | Var i -> rb, RVar (i, true)
    | Neg (neg_fb, neg_fm) -> (
        match neg_fm with
        | Var i -> rb, RVar (i, false)
        | _ -> get_nnf (get_negate (neg_fb, neg_fm)))
    | And li -> rb, RAnd (List.map get_nnf li, true)
    | Or li -> rb, RAnd (List.map get_nnf li, false)
  in
  let res = simpl_rformula rf in
  res

and get_nnf (fb, fm) =
  match fb.nnf with
  | Some v -> v
  | None ->
      let nnf = negative_normal_form (fb, fm) in
      fb.nnf <- Some nnf;
      nnf

let rec rm_to_fm (_, rm) =
  match rm with
  | RLit true -> top_ol
  | RLit false -> bot_ol
  | RVar (i, true) -> init (Var i)
  | RVar (i, false) -> init (Neg (init (Var i)))
  | RAnd (li, true) -> init (And (List.map get_fm li))
  | RAnd (li, false) -> init (Or (List.map get_fm li))

and get_fm (rb, rm) =
  match rb.f with
  | Some v -> v
  | None ->
      let fm = rm_to_fm (rb, rm) in
      rb.f <- Some fm;
      fm

(*
    Checks whether f is reduced or not, ille est in R or not
*)

let rec reduced rf =
  let _, rm = rf in
  match rm with
  | RAnd (li, pol) ->
      List.for_all
        (fun s ->
          let neg = get_negate (get_fm s) in
          let nnf = get_nnf neg in
          let r = if pol then lat_ord rf nnf else lat_ord nnf rf in
          (not r) && get_reduced s)
        li
  | _ -> true

and get_reduced rf =
  let rb, _ = rf in
  match rb.red with
  | Some v -> v
  | None ->
      let res = reduced rf in
      rb.red <- Some res;
      res

(*
    T_L(X + X') -> R
*)

let rec beta_normal_form rf =
  let _, rm = rf in
  let res =
    match rm with
    | RAnd (li, pol) ->
        let rr = simpl_rformula (init_rm (RAnd (List.map get_beta li, pol))) in
        if get_reduced rr then rr else get_rlit_bio (not pol)
    | _ -> rf
  in
  res

and get_beta rf =
  let rb, _ = rf in
  match rb.bnf with
  | Some v -> v
  | None ->
      let beta = beta_normal_form rf in
      rb.bnf <- Some beta;
      beta

(*
    Computes the ortholattice order
    T_OL(X) -> bool
*)

let ol_ord f g = lat_ord (get_beta (get_nnf f)) (get_beta (get_nnf g))

(*
    Computes the zeta-normal-form. The formula needs to be
    flatten
*)

let rec zeta_normal_form rf =
  let _, rm = rf in
  let or_pred = lat_ord rf in
  let and_pred e = lat_ord e rf in

  let rec aux pol li acc flag =
    let pred = if pol then or_pred else and_pred in
    match li with
    | [] -> acc, flag
    | ((_, RAnd (l, p)) as hd) :: tl when p <> pol -> (
        let el_opt = List.find_opt pred l in
        match el_opt with
        | Some el -> aux pol tl (el :: acc) true
        | None -> aux pol tl (hd :: acc) flag)
    | hd :: tl -> aux pol tl (hd :: acc) flag
  in

  let res =
    match rm with
    | RAnd (li, pol) ->
        let r, flag = aux pol li [] false in
        if flag then get_zeta (init_rm (RAnd (r, pol)))
        else simpl_rformula (init_rm (RAnd (List.map get_zeta li, pol)))
    | _ -> rf
  in
  res

and get_zeta rf =
  let rb, _ = rf in
  match rb.znf with
  | Some v -> v
  | None ->
      let zeta = zeta_normal_form rf in
      rb.znf <- Some zeta;
      zeta

(*
    Computes the antichain normal form
    R -> R
*)

let rec eta_normal_form rf =
  let rec exists_gt s l =
    match l with
    | [] -> false
    | a :: _ when lat_ord s a -> true
    | _ :: tl -> exists_gt s tl
  in
  let rec help l acc flag =
    match l with
    | [] -> acc, flag
    | s :: tl when flag -> help tl (s :: acc) flag
    | s :: tl ->
        if exists_gt s tl || exists_gt s acc then help tl acc true
        else help tl (s :: acc) flag
  in

  let rb, rm = rf in
  match rb.enf with
  | Some v -> v
  | None ->
      let res =
        match rm with
        | RAnd (li, false) ->
            let r, fl = help li [] false in
            if fl then eta_normal_form (init_rm (RAnd (r, false)))
            else simpl_rformula (init_rm (RAnd (List.map get_eta li, false)))
        | _ -> rf
      in
      res

and get_eta rf =
  let rb, _ = rf in
  match rb.enf with
  | Some v -> v
  | None ->
    let eta = eta_normal_form rf in
    rb.enf <- Some eta;
    eta

(*
    Computes the OL normal form of a formula f.
    formula -> rformula
*)

let ol_normal_form f = get_eta (get_zeta (flatten (get_beta (get_nnf f))))
