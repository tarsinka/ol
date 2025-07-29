open Gen

let funs = [ "INPUT"; "OUTPUT"; "AND"; "OR"; "NOT" ]

let read_iscas fn =
  let in_ch = open_in fn in
  let vars = Hashtbl.create 8 in

  let parse_id vs =
    let vs = String.trim vs in
    let vs =
      if String.contains vs '(' then String.sub vs 1 (String.length vs - 2) else vs
    in
    let len = String.length vs in
    let vs, flag =
      if String.ends_with ~suffix:"_bar" vs then String.sub vs 0 (len - 4), false
      else vs, true
    in
    (* Printf.printf "%s\n%!" vs; *)
    flag, vs
  in
  let parse_fn ln =
    let ln = String.trim ln in
    let lr = String.split_on_char '(' ln in
    let f = List.hd lr in
    let len_fn = String.length f in
    let len = String.length ln - len_fn in
    let data = String.sub ln (len_fn + 1) (len - 2) in
    let args = String.split_on_char ',' data in
    match f with
    | "INPUT" | "OUTPUT" ->
        let _, id = parse_id data in
        let i = 1 +
          if String.equal id "out" then 0
          else
            let str = String.sub id 2 (String.length id - 2) in
            let str = String.trim str in
            int_of_string str
        in
        let var = new_lit i true in
        Hashtbl.replace vars id var;
        var
    | "AND" ->
        new_and
          (List.map
             (fun st ->
               let par, id = parse_id st in
               let s = Hashtbl.find vars id in
               if par then s else get_neg s)
             args)
    | "OR" ->
        new_or
          (List.map
             (fun st ->
               let par, id = parse_id st in
               let s = Hashtbl.find vars id in
               if par then s else get_neg s)
             args)
    | "NOT" ->
        let par, id = parse_id data in
        let s = Hashtbl.find vars id in
        if not par then s else get_neg s
    | _ -> T false
  in

  let rec parse ln_opt =
    match ln_opt with
    | None -> ()
    | Some ln ->
        (if String.contains ln '=' then
           let left_right = String.split_on_char '=' ln in
           let s = parse_fn (List.nth left_right 1) in
           let par, id = parse_id (List.hd left_right) in
           if par then Hashtbl.replace vars id s else ()
         else if String.starts_with ~prefix:"#" ln then ()
         else
           let _ = parse_fn ln in
           ());

        parse (In_channel.input_line in_ch)
  in
  parse (In_channel.input_line in_ch);
  Hashtbl.find vars "out"
