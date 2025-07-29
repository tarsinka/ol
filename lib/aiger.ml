type header = { m : int; i : int; l : int; o : int; a : int } [@@deriving show]

type aig_formula =
  | Lit of bool
  | Var of int
  | And of int * aig_formula list
  | Not of aig_formula
[@@deriving show]

let parse_header ln =
  match String.split_on_char ' ' ln with
  | _ :: [ m; i; l; o; a ] ->
      {
        m = int_of_string m;
        i = int_of_string i;
        l = int_of_string l;
        o = int_of_string o;
        a = int_of_string a;
      }
  | _ -> failwith "[AIG] header parsing error"

let rec read_uint in_ch =
  let by = input_byte in_ch in
  if Int.shift_right_logical by 7 = 0 then by else by - 128 + (128 * read_uint in_ch)

(* let rec flatten = function
  | And (k, cnj) ->
      let cnj =
        List.fold_right
          (fun s acc ->
            let s = flatten s in
            match s with And (_, cnj) -> cnj @ acc | _ -> s :: acc)
          cnj []
      in
      And (k, cnj)
  | Not f -> Not (flatten f)
  | f -> f *)

let parse in_ch =
  let hdr = parse_header (input_line in_ch) in
  let map = Hashtbl.create hdr.m in

  Hashtbl.replace map 0 (Lit false);
  Hashtbl.replace map 1 (Lit true);

  let cur_line = ref 1 in

  let rec inputs = function
    | 0 -> ()
    | k ->
        let ind = 2 * k in
        let var = Var ind in
        Hashtbl.replace map ind var;
        Hashtbl.replace map (ind + 1) (Not var);
        inputs (k - 1)
  in
  inputs hdr.i;

  let rec outputs = function
    (*
      Since inputs are'nt explicitly written in the binary format,
      we straight forward read the outputs.
    *)
    | 0 -> []
    | k ->
        let s = input_line in_ch in
        cur_line := !cur_line + 1;
        let i = int_of_string s in
        i :: outputs (k - 1)
  in
  let outs = outputs hdr.o in

  let rec ands = function
    | 0 -> ()
    | k ->
        let k' = hdr.m + 1 - k in

        let delta_a = read_uint in_ch in
        let delta_b = read_uint in_ch in

        let l = 2 * k' in
        let rha = l - delta_a in
        let rhb = rha - delta_b in

        if rha >= l || rhb > rha then failwith "Parsing error";
        let ma = Hashtbl.find map rha in
        let mb = Hashtbl.find map rhb in

        (* let cnj =
          match ma, mb with
          | And (_, la), And (_, lb) -> la @ lb
          | And (_, la), _ -> mb :: la
          | _, And (_, lb) -> ma :: lb
          | _ -> [ ma; mb ]
        in *)
        let an = And (l, [ma ; mb]) in
        Hashtbl.replace map l an;
        Hashtbl.replace map (l + 1) (Not an);
        ands (k - 1)
  in
  ands hdr.a;
  hdr, List.map (fun x -> x, Hashtbl.find map x) outs
