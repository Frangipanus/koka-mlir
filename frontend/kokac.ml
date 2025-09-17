open Ast
open Format
open Lexing
open Parser
open Lexer
open Algow
(* Option de compilation, pour s'arrêter à l'issue du parser *)
let parse_only = ref false
let type_only = ref false 

(* Nom du fichier source *)
let ifile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche avec --help *)
let options =
  ["--parse-only", Arg.Set parse_only,
   "  Pour ne faire uniquement que la phase d'analyse syntaxique";
   "--type-only", Arg.Set type_only, "Pour ne faire uniquement la phase de typage"]

let usage = "usage: petit kokoa [option] test.koka"

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
  (* Parsing de la ligne de commande *)
  Arg.parse options (set_file ifile) usage;
  
  (* On vérifie que le nom du fichier source a bien été indiqué *)
  if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?"; exit 1 end;

  Printf.printf "%s\n" !ifile;
  let ofile = Filename.chop_suffix !ifile ".koka" ^ ".s" in 
  Printf.printf "%s\n" ofile;
  (* Ce fichier doit avoir l'extension .logo *)
  if not (Filename.check_suffix !ifile ".koka") then begin
    eprintf "Le fichier d'entrée doit avoir l'extension .koka\n@?";
    Arg.usage options usage;
    exit 1
  end;

  (* Ouverture du fichier source en lecture *)
  let f = open_in !ifile in

  (* Création d'un tampon d'analyse lexicale *)
  let buf = Lexing.from_channel f in   

  try
    let p = Parser.file Lexer.next_token buf in
    close_in f;

    (* On s'arrête ici si on ne veut faire que le parsing *)
    if !parse_only then (Printf.printf "Fin de la phase d'analyse syntaxique, réussie avec succès.\n";exit 0);
    let p2 = Algow.w p in 
    if !type_only then (Printf.printf "Fin de la phase de typage, réussie avec succès.\n";exit 0);
    
  with
    | Lexer.Lexing_error c ->
	(* Erreur lexicale. On récupère sa position absolue et
	   on la convertit en numéro de ligne *)
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur lexicale: %s@." c;
	exit 1
    | Parser.Error ->
	(* Erreur syntaxique. On récupère sa position absolue et on la
	   convertit en numéro de ligne *)
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur syntaxique@.";
	exit 1
    |Error2 -> (localisation (Lexing.lexeme_start_p buf);
    eprintf "Erreur de syntaxe\n" ;
    exit 1)
    |Algow.TypeError(s) -> (Printf.printf "%s" s; exit 1)
    |Algow.TypeErrorLoc(s, (loc,_)) -> (Printf.printf "File : \"%s\", TypeError on line %d;\n%s" !ifile loc.pos_lnum s; exit 1)
    |Algow.UnificationFailure(_,_) -> exit 1
   
