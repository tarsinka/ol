open Logic

type header = { m : int; i : int; l : int; o : int; a : int } [@@deriving show]

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

let parse filename =
  let in_ch = open_in filename in
  let hdr = parse_header (input_line in_ch) in
  let map = Hashtbl.create hdr.m in

  Hashtbl.replace map 0 (AIGLit false);
  Hashtbl.replace map 1 (AIGLit true);

  let rec inputs = function
    | 0 -> ()
    | k ->
        let ind = 2 * k in
        let var = AIGVar ind in
        Hashtbl.replace map ind var;
        Hashtbl.replace map (ind + 1) (AIGNot var);
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

        if rha >= l || rhb > rha then failwith "[aig] parsing error";
        let ma = Hashtbl.find map rha in
        let mb = Hashtbl.find map rhb in

        let an = AIGAnd (l, [ma ; mb]) in
        Hashtbl.replace map l an;
        Hashtbl.replace map (l + 1) (AIGNot an);
        ands (k - 1)
  in
  ands hdr.a;
  hdr, List.map (fun x -> x, Hashtbl.find map x) outs