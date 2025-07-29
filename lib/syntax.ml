open Gen

(*
  De-Tseitinification
*)

module Lits = Set.Make (struct
  type t = int * bool

  let compare = Stdlib.compare
end)

let str_lit (i, b) =
  let sg = if b then "" else "~" in
  Printf.sprintf "%s%d" sg i

let str_lits ls =
  let sl = Lits.fold (fun l acc -> str_lit l :: acc) ls [] in
  "{" ^ String.concat ", " sl ^ "}"

let get_lit_data = function
  | SLit (_, k, b) -> k, b
  | _ -> failwith "This is not a boolean variable!"

let equiv_cl x = function
  | SOr (_, dsj) when List.exists (eq x) dsj ->
      List.fold_right
        (fun s acc -> if eq s x then acc else Lits.add (get_lit_data s) acc)
        dsj Lits.empty
  | _ -> Lits.empty

let rec equiv_cnj x pos_lits neg_lits cnj =
  match cnj with
  | [] -> List.rev pos_lits, List.rev neg_lits
  | cl :: t ->
      let px = equiv_cl x cl in
      let pos_lits = if Lits.is_empty px then pos_lits else px :: pos_lits in
      let nx = equiv_cl (get_neg x) cl in
      let neg_lits = if Lits.is_empty nx then neg_lits else nx :: neg_lits in
      equiv_cnj x pos_lits neg_lits t

(*
    Equiv checks for equivalence between artificial variables and actual
    formulas. If [x] is artificial, then we return its corresponding formula.
    Otherwise, [x] is a part of the original formula, and we keep it as it is.
*)

let equiv id x cnj =
  (* Printf.printf "checking equiv for %s\n" (str_formula x); *)
  let pos_lits, neg_lits = equiv_cnj x [] [] cnj in

  let carac sl c = if Lits.cardinal sl = 1 then c + 1 else c in

  let pn = List.fold_right carac pos_lits 0 in
  let nn = List.fold_right carac neg_lits 0 in

  let flg, a, b =
    if pn > nn then true, pos_lits, neg_lits else false, neg_lits, pos_lits
  in
  let a = List.fold_right Lits.union a Lits.empty in
  let a =
    Lits.fold
      (fun (i, b) acc -> if i >= id then acc else Lits.add (i, not b) acc)
      a Lits.empty
  in
  (* Printf.printf "a = %s\n" (str_lits a); *)
  let opt =
    List.find_opt
      (fun sl ->
        (* Printf.printf "b = %s\n" (str_lits sl); *)
        Lits.for_all (fun (i, _) -> i < id) sl && Lits.equal sl a)
      b
  in
  match opt with
  | None -> None
  | Some sl ->
      let lts =
        Lits.fold
          (fun (i, b) acc ->
            let lit = new_lit i b in
            let lit = if flg then lit else get_neg lit in
            lit :: acc)
          sl []
      in
      if flg then Some (new_or lts) else Some (new_and lts)

let get_cnj = function
  | SAnd (_, cnj) -> cnj
  | _ -> failwith "This is not formula under CNF"

let rec get_lits = function
  | T _ -> Lits.empty
  | SLit (_, k, _) -> Lits.singleton (k, true)
  | SAnd (_, li) | SOr (_, li) ->
      List.fold_right (fun s acc -> Lits.union acc (get_lits s)) li Lits.empty

let detseitin f =
  let hs = Hashtbl.create 8 in
  let lts = get_lits f in

  (* let subst_hs = Hashtbl.create 8 in *)
  let rec subst v =
    let fg = get_fgprint v in
    match Hashtbl.find_opt hs fg.uid with
    | Some v' -> v'
    | None ->
    match v with
    | SLit (_, i, b) as s -> (
        match Hashtbl.find_opt hs i with
        | None -> s
        | Some v -> if b then v else get_neg v)
    | SAnd (fg, cnj) ->
        let s = new_and (List.map subst cnj) in
        Hashtbl.replace hs fg.uid s;
        s
    | SOr (fg, dsj) ->
        let s = new_or (List.map subst dsj) in
        Hashtbl.replace hs fg.uid s;
        s
    | s -> s
  in

  Lits.iter
    (fun (k, b) ->
      match equiv k (new_lit k b) (get_cnj f) with
      | None -> ()
      | Some v ->
          let v' = subst v in
          Printf.printf "%s <-> %s\n"
            (str_lit (k, b))
            (str_formula v');
          Hashtbl.replace hs k v')
    lts;
  subst f
(* thin (fm_flatten dts) *)
