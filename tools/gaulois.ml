open Core

let () =
  Command_unix.run
    (Command.group
       ~summary:"Audit and measure Gaulois"
       [ "check", Gaulois_check.Check.command; "bench", Gaulois_check.Bench.command ])
;;
