open Gen

let write_dimacs cnf =
  let fmt_lit (uid, pol) = (if pol then "" else "-") ^ string_of_int uid in
  let cnf_n_clauses = function SAnd (_, sli) -> List.length sli | _ -> 1 in
  let rec fmt_clause scl =
    match scl with
    | SLit (_, i, pol) -> fmt_lit (i, pol)
    | SOr (_, dsj) ->
        String.concat " " (List.fold_right (fun s acc -> fmt_clause s :: acc) dsj [])
    | T _ -> ""
    | _ ->
        failwith
          (Printf.sprintf "Unexpected formula within the clause : %s" (str_formula scl))
  in

  let str =
    match cnf with
    | T true | T false -> failwith "Unexpected symbol"
    | SLit (_, uid, pol) -> Printf.sprintf "%s 0\n" (fmt_lit (uid, pol))
    | SAnd (_, sli) ->
        let scnj =
          String.concat " 0\n"
            (List.fold_left (fun acc cl -> fmt_clause cl :: acc) [] sli)
        in
        Printf.sprintf "%s 0\n" scnj
    | SOr _ -> Printf.sprintf "%s 0\n" (fmt_clause cnf)
  in
  let nvars = Vars.cardinal (vars cnf) in
  let ncl = cnf_n_clauses cnf in
  Printf.sprintf "p cnf %d %d\n%s" nvars ncl str

let read_dimacs fn =
  let in_ch = open_in fn in

  let rec header () =
    let hdr_str = input_line in_ch in
    let data = String.split_on_char ' ' hdr_str in

    if List.hd data = "c" then header ()
    else
      let _n_vrs = List.nth data 2 in
      int_of_string (List.nth data 3)
  in
  let n_cls = header () in

  let parse_line ln =
    let lits = String.split_on_char '\t' ln in
    let dsj =
      List.fold_right
        (fun str acc ->
          if str = "" then acc
          else
            let str_int = int_of_string str in
            if str_int = 0 then acc else new_lit (Int.abs str_int) (str_int > 0) :: acc)
        lits []
    in
    new_or dsj
  in

  let rec lines = function
    | 0 -> []
    | k ->
        let ln = input_line in_ch in
        parse_line ln :: lines (k - 1)
  in
  let cnj = lines n_cls in
  new_and cnj
