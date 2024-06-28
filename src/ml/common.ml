open Algo1

let mk_groupe_classement voeux taux_b taux_r = {
  taux_boursiers = Z.of_int taux_b;
  taux_residents = Z.of_int taux_r;
  voeux = voeux;
}

let mk_voeu boursier resident rang = {
  boursier = boursier;
  resident = resident;
  rang = Z.of_int rang;
}

let string_of_voeu v =
  Format.sprintf "%d;%d;" (Z.to_int v.rang) (if v.boursier then 1 else 0)

let print_voeu v =
  Format.printf "%s@." (string_of_voeu v)

let print_oa oa =

  try while true do
    let v = Queue.take oa in
    print_voeu v
  done with Queue.Empty -> ()

let cmp v v' =
  Stdlib.compare (Z.to_int v.rang) (Z.to_int v'.rang)

let rm_list_dup l =

  let tbl = Hashtbl.create 1024 in

  List.filter (fun el ->
    let seen = Hashtbl.mem tbl el in
    if not seen then Hashtbl.add tbl el ();
    not seen
  ) l

let bool_of_int = function
  | 0 -> false
  | 1 -> true
  | _ -> failwith "invalid input (bool_of_int)"

let get_taux wanted =

  let input = open_in "taux.csv" in

  let res = ref None in

  (try while true do
    let line = input_line input in
    let groupe_classement, taux = Scanf.sscanf line "%d;%d" (fun x y -> x, y) in
    if groupe_classement = wanted then begin
      res := Some taux;
      raise End_of_file
    end
  done with End_of_file -> ());

  !res

let get_oa wanted =

  let input = open_in "ordre_appels.csv" in

  let oa = ref [] in

  ( try while true do
    let line = input_line input in
    let groupe_classement, rang, boursier = ( try
      Scanf.sscanf line "%d;%d;%d;" (fun x y z -> x, y, bool_of_int z)
    with | Scanf.Scan_failure _ -> Scanf.sscanf line "%d;%d;%d;%d;" (fun x y z _ -> x, y, bool_of_int z)

    ) in
    if groupe_classement = wanted then oa := (mk_voeu boursier false rang)::!oa
  done with End_of_file -> () );

  rm_list_dup (List.rev !oa)
