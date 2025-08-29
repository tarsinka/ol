open Logic

let write filename (cnf : cnf_formula) =
  let out_ch = open_out filename in
  Printf.fprintf out_ch "p cnf %d %d\n%!" cnf.amount_vars cnf.amount_clauses;

  List.iter
    (fun cl ->
      let line = String.concat " " (List.map string_of_int cl) ^ " 0" in
      Printf.fprintf out_ch "%s\n%!" line)
    cnf.clauses

let read fn =
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
    let lits = String.split_on_char ' ' ln in
    let dsj =
      List.fold_right
        (fun str acc ->
          if str = "" then acc
          else (
            let str_int = int_of_string str in
            if str_int = 0 then acc
            else
              let var = Var (fresh_formula_uid (), Int.abs str_int) in
              if str_int > 0 then var :: acc else negate var :: acc))
        lits []
    in
    Or (fresh_formula_uid (), dsj)
  in

  let rec lines = function
    | 0 -> []
    | k ->
        let ln = input_line in_ch in
        parse_line ln :: lines (k - 1)
  in
  let cnj = lines n_cls in
  And (fresh_formula_uid (), cnj)
