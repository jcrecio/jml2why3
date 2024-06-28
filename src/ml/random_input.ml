open Algo1
open Common

let _ =

  if Array.length Sys.argv < 2 then failwith "taux nécessaire";

  let taux = int_of_string Sys.argv.(1) in

  if taux < 0 || taux > 100 then failwith "taux doit être un entier entre 0 et 100";

  let v = Array.init 100 (fun i ->
    let est_b = Random.bool () && Random.bool () in
    let est_r = Random.bool () && Random.bool () in
    let r = i + 1 in
    mk_voeu est_b est_r r
  ) in

  let gc = mk_groupe_classement v taux 0 in

  let oa = algo1 gc in

  print_oa oa
