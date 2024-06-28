open Algo1
open Common

let _ =

  if Array.length Sys.argv < 2 then failwith "taux nécessaire";

  let taux = int_of_string Sys.argv.(1) in

  if taux < 0 || taux > 100 then failwith "taux doit être un entier entre 0 et 100";

  let input = stdin in

  let oa = ref [] in

  try while true do
    let line = input_line input in
    let classement, boursier = Scanf.sscanf line "%d;%d;" (fun x y -> x, ((function | 0 -> false | 1 -> true | _ -> failwith "invalid input") y)) in
    oa := (mk_voeu boursier false classement)::!oa;
  done; with End_of_file -> ();

  let oa = rm_list_dup !oa in

  let oa = Array.of_list oa in

  Array.sort cmp oa;

  let gc = mk_groupe_classement oa taux 0 in

  let oa = algo1 gc in

  print_oa oa
