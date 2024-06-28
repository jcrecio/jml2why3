open Common

let _ =

  if Array.length Sys.argv < 2 then failwith "groupe_classement nécessaire";

  let wanted = int_of_string Sys.argv.(1) in

  let res = get_taux wanted in

  match res with
  | Some x -> Format.printf "%d@." x
  | None -> failwith "not found"
