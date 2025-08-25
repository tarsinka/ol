let () =
  let circuit_names = [ "benchmarks/epfl-circuits/multiplier.aig" ] in
  Ol.Olsc.benchmark circuit_names (Ol.Olsc.add);
  ()
