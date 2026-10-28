open Core

let () =
  Command_unix.run
    (Command.group ~summary:"Audit Gaulois sources" [ "check", Gaulois_check.Check.command ])
;;
