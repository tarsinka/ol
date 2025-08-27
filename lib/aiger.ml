open Logic

type header = { m : int; i : int; l : int; o : int; a : int } [@@deriving show]

let header_from_aig_formula s =
  let mem = Hashtbl.create 8 in
  let rec go (i, a) s =
    match Hashtbl.mem mem s with
    | true -> i, a
    | false ->
        let acc =
          match s with
          | AIGLit _ -> i, a
          | AIGVar _ -> i + 1, a
          | AIGNot t -> go (i, a) t
          | AIGAnd (_, u, v) -> go (go (i, a + 1) u) v
        in
        Hashtbl.replace mem s true;
        acc
  in
  let i, a = go (0, 0) s in
  { m = i + a; i; l = 0; o = 1; a }

(*
  Encodes the deltas.
*)

let rec encode out x =
  if Int.logand x (Int.lognot 0x7f) <> 0 then (
    let ch = Int.logor (Int.logand x 0x7f) 0x80 in
    output_byte out ch;
    encode out (Int.shift_right x 7))
  else output_byte out x

let write filename s =
  let out = open_out filename in
  let header = header_from_aig_formula s in

  Printf.fprintf out "aig %d %d %d %d %d\n%d\n" header.m header.i header.l header.o
    header.a (2 * header.m);

  let mem = Hashtbl.create 8 in
  let ind = Hashtbl.create 8 in

  let rec go s =
    match Hashtbl.find_opt mem s with
    | Some x -> x
    | None ->
        let r =
          match s with
          | AIGLit false -> 0
          | AIGLit true -> 1
          | AIGVar v -> 2 * v
          | AIGAnd (k, u, v) ->
              let var_u = go u in
              let var_v = go v in

              let lhs = 2 * k in
              let delta_a = lhs - var_u in
              let delta_b = var_u - var_v in

              if lhs <= var_u || var_u < var_v then failwith "wrong delta";

              Hashtbl.replace ind k (delta_a, delta_b);

              lhs
          | AIGNot t -> go t + 1
        in
        Hashtbl.replace mem s r;
        r
  in
  let _ = go s in
  (*
    Encodes the deltas in the good order.
  *)
  let rec enc = function
    | 0 -> ()
    | k ->
        let k' = header.m + 1 - k in
        let a, b = Hashtbl.find ind k' in

        encode out a;
        encode out b;

        enc (k - 1)
  in
  enc header.a;
  close_out out

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

        let an = AIGAnd (l, ma, mb) in
        Hashtbl.replace map l an;
        Hashtbl.replace map (l + 1) (AIGNot an);
        ands (k - 1)
  in
  ands hdr.a;
  hdr, List.map (fun x -> x, Hashtbl.find map x) outs
