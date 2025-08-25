(lang dune 3.17)

(name ol)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Vladislas de Haldat <vlad.hdt@proton.me>")

(maintainers "Vladislas de Haldat <vlad.hdt@proton.me>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ol)
 (synopsis "Algorithms for orthologic.")
 (description "This library implements the algorithms of normalization and of proof search for the framework of orthologic")
 (depends ocaml alcotest ppx)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
