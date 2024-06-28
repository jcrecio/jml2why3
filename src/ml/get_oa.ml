open Common

let _ =

  if Array.length Sys.argv < 2 then failwith "groupe_classement nécessaire";

  let wanted = int_of_string Sys.argv.(1) in

  let oa = get_oa wanted in

  List.iter print_voeu oa
