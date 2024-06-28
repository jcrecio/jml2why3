open Stdlib
open Format

let (let*) = Result.bind

type config = {
  file: string;
  run_proofs: bool;
  print_java_ast: bool;
  print_mlw_ast: bool;
  write_mlw: string option;
}

let parse_args () =
  let open Arg in
  let file = ref None in
  let run_proofs = ref true in
  let print_java_ast = ref false in
  let print_mlw_ast = ref false in
  let write_mlw = ref None in
  let speclist = [
    "--dont-prove", Clear run_proofs, " Don't try to prove ";
    "--print-java-ast", Set print_java_ast, " Print Java AST";
    "--print-mlw-ast", Set print_mlw_ast, " Print Why3 AST";
    "--write-mlw", String (fun s -> write_mlw := Some s), "<file> Write to mlw file"
  ] in
  let anon_fun str =
    match !file with
    | None -> file := Some str
    | Some _ -> raise (Bad "multiple files specified") in
  let usage_msg = Sys.argv.(0)^" [opts] <file-java-json>" in
  parse (align speclist) anon_fun usage_msg;
  let file = match !file with Some f -> f | None -> raise (Bad "no file specified") in
  {file; run_proofs = !run_proofs; print_java_ast = !print_java_ast; print_mlw_ast = !print_mlw_ast; write_mlw = !write_mlw}

let main () =
  let cnf = parse_args () in
  let json = Yojson.Safe.from_file cnf.file in
  let* cu =
    JmlFromJson.compilation_unit json |>
    Result.map_error (asprintf "%a" JmlFromJson.pp_error) in
  if cnf.print_java_ast then
    printf "Java/JML: %a@." JmlAst.pp_compilation_unit cu;
  try
    let decls = Jml2why3.compilation_unit cu in
    let name = Filename.(basename cnf.file |> chop_extension |> chop_extension) in
    let mlw_file = Why3.Ptree.Modules [Why3aux.Ast.mk_ident name, decls] in
    if cnf.print_mlw_ast then
      printf "%a@." Why3aux.PtreeDebug.pp_mlw_file mlw_file;
    (match cnf.write_mlw with
     | None -> ()
     | Some file_mlw ->
       let c = open_out file_mlw in
       let fmt = formatter_of_out_channel c in
       fprintf fmt "%a@." (Why3.Mlw_printer.pp_mlw_file ~attr:true) mlw_file;
       close_out c;
       printf "Written to %s@." file_mlw);
    (* printf "%a@." Mlw_printer.pp_mlw_file mlw_file; *)
    if cnf.run_proofs then
      try
        let pmodules = Why3aux.why3_type_file mlw_file in
        match Why3aux.why3_prove ~name ~limit_depth:3 ~limit_time1:5. ~limit_time2:15. pmodules with
        | Valid -> printf "OK!@."; Result.ok ()
        | Invalid -> Result.error "Invalid."
        | Dontknow -> Result.error "Don't know."
      with Failure msg ->
        Format.kasprintf Result.error "Failure type-ckecking/proving: %s" msg
    else
      Result.ok ()
  with Failure msg ->
    eprintf "Java/JML: %a@." JmlAst.pp_compilation_unit cu;
    Format.kasprintf Result.error "Failure converting: %s" msg

let setup_format () =
  let open Format in
  let aux fmt =
    pp_set_geometry fmt ~max_indent:250 ~margin:300;
    pp_set_max_boxes fmt 500 in
  List.iter aux [std_formatter; err_formatter]

let () =
  (* setup_format (); *)
  match main () with
  | Ok () -> exit 0
  | Error str -> (eprintf "%s@." str; exit 1)
