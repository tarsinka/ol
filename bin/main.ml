open Ol.Gen
open Ol.Aiger
open Ol.Translator
open Ol.Syntax
open Ol.Olsc

type par = { n : int; r : float; sh : int list }

let write cl_trs ol_trs root k =
  let cl_fn = Printf.sprintf "%s/%dcl.cnf" root k in
  let ol_fn = Printf.sprintf "%s/%dol.cnf" root k in

  let cl_file = open_out cl_fn in
  let ol_file = open_out ol_fn in

  Printf.fprintf cl_file "%s\n" cl_trs;
  Printf.fprintf ol_file "%s\n" ol_trs;

  close_out cl_file;
  close_out ol_file

let rec _generation_method p = function
  | 0 -> ()
  | k ->
      reset ();

      let mdf = model p.sh p.n p.r in

      let tmp_v, tmp_u = !var_uid, !fm_uid in
      let cl_cnf = cnf mdf in

      var_uid := tmp_v;
      fm_uid := tmp_u;

      let olnf = olnf' mdf in
      let ol_cnf = cnf olnf in

      Printf.printf "cl-size -- %d\nol-size -- %d\nclcnf-size -- %d\nolcnf-size -- %d\n"
        (get_virtual_size mdf) (get_virtual_size olnf) (get_virtual_size cl_cnf)
        (get_virtual_size ol_cnf);

      let cl_trs = write_dimacs cl_cnf in
      let ol_trs = write_dimacs ol_cnf in

      write cl_trs ol_trs "problems/finals/generated/" k;

      Printf.printf "[gen] #%d done\n" k;
      _generation_method p (k - 1)

let _aiger_method fn =
  let in_ch = open_in fn in
  let hdr, fms = parse in_ch in

  let ctx = Hashtbl.create 16 in

  let gts_a = Hashtbl.create 16 in
  let gts_b = Hashtbl.create 16 in

  var_uid := (2 * hdr.i) + 1;
  reset ();

  let rec craft gms fms_a fms_b equivs = function
    | 0 ->
        get_neg (new_and gms)
        (* get_neg (new_imp (new_and (fms_a @ fms_b)) (new_and equivs)) *)
    | k ->
        let x, fm = List.nth fms (k - 1) in

        let fm_a = aig_to_sf hdr ctx gts_a fm in
        let fm_b = aig_to_sf hdr ctx gts_b fm in

        let a, b =
          match x with
          | 0 -> T false, T false
          | 1 -> T true, T true
          | x ->
              let x = x / 2 in
              Hashtbl.find gts_a x, Hashtbl.find gts_b x
        in

        let eqv = new_equiv a b in
        (* Printf.printf "equiv\n%s\n" (str_formula eqv); *)

        craft
          (new_imp (new_and [ fm_a; fm_b ]) eqv :: gms)
          (fm_a :: fms_a) (fm_b :: fms_b) (eqv :: equivs) (k - 1)
  in

  let sfm = craft [] [] [] [] (List.length fms) in

  let cl_cnf = cnf sfm in

  let olnf = olnf' sfm in
  let ol_cnf = cnf olnf in

  let cl_trs = write_dimacs cl_cnf in
  let ol_trs = write_dimacs ol_cnf in

  Printf.printf "cl-size -- %d\nol-size -- %d\nclcnf-size -- %d\nolcnf-size -- %d\n"
    (get_virtual_size sfm) (get_virtual_size olnf) (get_virtual_size cl_cnf)
    (get_virtual_size ol_cnf);

  write cl_trs ol_trs "problems/finals/aig" 0

let rec _sat_competition_method = function
  | 0 -> ()
  | k ->
      let k = k - 1 in
      reset ();

      let root = "problems/ssa" in
      let path = "problems/ssa/ssa0432-003.cnf" in
      let _path = root ^ "test" ^ string_of_int k ^ ".cnf" in
      let fm_cnf = read_dimacs path in

      let dets = detseitin fm_cnf in

      Printf.printf "Detseitinized\n\n%s\n\n" (str_formula dets);

      (* Printf.printf "\n%s\n" (str_formula dets); *)
      let cl_cnf = cnf dets in

      let olnf = olnf' dets in
      let ol_cnf = cnf olnf in

      Printf.printf
        "initial: %d\ndetseitin: %d\nol-size -- %d\nclcnf-size -- %d\nolcnf-size -- %d\n"
        (get_virtual_size fm_cnf) (get_virtual_size dets) (get_virtual_size olnf)
        (get_virtual_size cl_cnf) (get_virtual_size ol_cnf);
      Printf.printf "[dts] #%d done\n" k;

      write (write_dimacs cl_cnf) (write_dimacs ol_cnf) root k;
      _sat_competition_method k

let () =
  Random.self_init ();

  (* _generation_method { n = 120 ; r = 1.16 ; sh = [6 ; 3] } 40 *)
  (* _sat_competition_method 1 *)
  (* _aiger_method "problems/finals/aig/adder.aig" *)
  let avn = fresh_counter var_counter in
  let bvn = fresh_counter var_counter in
  let cvn = fresh_counter var_counter in

  let in_ch = open_in "problems/AIG/multiplier.aig" in
  let _, _biere_aig = parse in_ch in

  (* let biere_aig = List.map (fun (_, aig) -> aig) biere_aig in *)
  let _afm : aig_formula =
    And
      ( fresh_counter var_counter,
        [
          (* Var bvn; *)
          And
            ( fresh_counter var_counter,
              [ And (fresh_counter var_counter, [ Var avn; Var bvn ]); Var avn ] );
          Var cvn;
        ] )
  in
  (* let _bfm : aig_formula = And (fresh_counter var_counter, [ Var avn; Var bvn ]) in
  let _cfm : aig_formula =
    Not
      (And
         ( 278,
           [
             Var 132;
             Var 2;
             (* Not (And (272, [ Not (Var 6); Var 4 ])); *)
             Not (And (270, [ Var 6; Not (Var 4) ]));
           ] ))
  in *)

  (* let _zfm : aig_formula = And (fresh_counter var_counter, [ _bfm; Not _bfm ]) in *)
  (* let b = start (Ol.Olsc.fresh_counter Ol.Olsc.var_counter, _afm) in *)
  let afm_vn, afm = List.nth _biere_aig 16 in
  let b = start (afm_vn, afm) in
  (* Printf.printf "%s\n" (show_aig_formula _bfm); *)
  (* let _ = hg_prove _bfm *)
  Printf.printf "%b\n" b;
  ()
