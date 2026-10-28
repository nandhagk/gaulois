(lang dune 3.23)

(using rocq 0.13)

(name gaulois)

(generate_opam_files false)

; No theory has a source file yet, so the package has nothing to install. Remove allow_empty once
; any theory under theories/ has a .v file.

(package
 (name gaulois)
 (synopsis "General, composable program analyses in Rocq")
 (allow_empty))
