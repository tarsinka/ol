let run_olnf_benchmarks () =
  let roots =
    [
      (*
          Velev's benchmarks (all unsat)
        *)
      "benchmarks/velev";
      (*
          Cryptographic benchmarks
        *)
      "benchmarks/crypto/des_3_1";
      "benchmarks/crypto/des_4_1";
      "benchmarks/crypto/des_4_2";
      "benchmarks/crypto/des_5_1";
      "benchmarks/crypto/des_5_2";
      "benchmarks/crypto/des_5_3";
      "benchmarks/crypto/des_5_4";
      "benchmarks/crypto/des_GenFacBm";
      "benchmarks/crypto/heljanko";
      (*
          Biere's benchmarks
        *)
      "benchmarks/smtqfbv";
    ]
  in
  List.iter (fun root -> Ol.Olnf.benchmark root) roots

let run_olsc_benchmarks () =
  Ol.Olsc.benchmark [ "benchmarks/epfl-circuits/multiplier.aig" ]

let () =
  run_olsc_benchmarks ();
  run_olnf_benchmarks ()
