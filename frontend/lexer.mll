
(* Analyseur lexical pour mini-Turtle *)

{

  open Lexing
  open Parser
  
  exception Lexing_error of string

  let key_words = Hashtbl.create 11
  let () = Hashtbl.add key_words "if" IF
  let () = Hashtbl.add key_words "then" THEN
  let () = Hashtbl.add key_words "else" ELSE
  let () = Hashtbl.add key_words "elif" ELIF
  let () = Hashtbl.add key_words "fn" FN
  let () = Hashtbl.add key_words "fun" FUN
  let () = Hashtbl.add key_words "return" RETURN
  let () = Hashtbl.add key_words "val" VAL
  let () = Hashtbl.add key_words "var" VAR
  let () = Hashtbl.add key_words "True" TRUE
  let () = Hashtbl.add key_words "False" FALSE
  
  let fin_cont = [PLUS; MINUS; MUL; DIV; MOD; CONCAT ;LT ; LTE; GT ;GTE ;EQ; NEQ ;AND; OR ;LPAR; LBRAC; COMMA; ]
  let debut_cont = [PLUS; MINUS ;MUL; DIV; MOD; CONCAT; LT; LTE; GT; GTE; EQ; NEQ; AND; OR; LBRAC; COMMA; RPAR; RBRAC ;ARROW ; DEF; DOT ;ASSIGN  ;THEN; ELSE; ELIF;]
  let level = ref (-1)  
  let last = ref SEMICOLON
  let indented = ref false 
  let last_line = ref (-1)

}
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let letter_l = ['a' - 'z']
let upper = ['A'-'Z']
let other = ['a'-'z' '-' 'A'-'Z' '0'-'9' '_']
let lud = letter_l | upper | digit
let ident = (lower ('-' (upper | lower))? ( (lud|'_') | (lud '-' (upper | letter_l)))* ('\'' | (lud '-'))?) | (lud '-')
let tabu = ' '+
let integer = '-'? ('0' | ['1'-'9'] digit*)


rule token  = parse
  | "//"  { comment lexbuf }
  | "/*"  { comment2 lexbuf }
  | "++"  { [CONCAT] }
  | '+'   { [PLUS] }
  | '-'   { [MINUS] }
  | '*'   { [MUL] }
  | '/'   { [DIV] }
  | "<="  { [LTE] }
  | "<"   { [LT] }
  | ">="  { [GTE] }
  | ">"   { [GT] }
  | "=="  { [EQ] }
  | "!="  { [NEQ] }
  | "&&"  { [AND] }
  | "||"  { [OR] }
  | '('   { [LPAR] }
  | ')'   { [RPAR] }
  | '{'   { [LBRAC] }
  | '}'   { [SEMICOLON;RBRAC] }
  | '['   { [LSPAR] }
  | ']'   { [RSPAR] }
  | ','   { [COMMA] }
  | ':'   { [COLON] }
  | ';'   { [SEMICOLON] }
  | "->"  { [ARROW] }
  | "="   { [DEF] }
  | ":="  { [ASSIGN] }
  | '.'   { [DOT] }
  | '~'   { [TILD] }
  | "%"   { [MOD] }
  | "!"   { [EXCLAM] }
  
  |"True" {[TRUE]}
  | "False" {[FALSE]}
  | integer as s { [INT(int_of_string s)] }
  |'\n' {Lexing.new_line lexbuf; token lexbuf}
  | ' ' { token lexbuf }
  | '\t' {token lexbuf}
  | ident as id { try [Hashtbl.find key_words id] with Not_found -> [IDENT id] }
  | eof { Lexing.new_line lexbuf;[EOF] }
  | '"'   { [STRING(read_string lexbuf)] }
  | _ as c { raise (Lexing_error ("error read: "^(String.make 1 c))) }

and comment = parse 
  | "\n" {Lexing.new_line lexbuf;  token lexbuf }
  | _  { comment lexbuf }

and comment2 = parse
  | "*/" { token lexbuf }
  | eof  { raise(Lexing_error ("commentaire non finit")) }
  | "\n" {Lexing.new_line lexbuf; comment2 lexbuf }
  | _    { comment2 lexbuf }

and read_string = parse
  | "\\\\" {"\\"^(read_string lexbuf)}
  | "\\\""  {"\""^(read_string lexbuf)}
  |  '"' as s { "" }
  | "\\n" {"\n"^(read_string lexbuf)}
  | "\\t" {"\t"^(read_string lexbuf)} 
  | "\n" {raise (Lexing_error("Les string sont sur une seule ligne"))}
  | _ as c { (String.make 1 c) ^(read_string lexbuf)}
   
{ 
  let next_token =
    let tokens = Queue.create () in
    let pile = Stack.create () in 
    Stack.push 0 pile;
    Queue.add SEMICOLON tokens; (* prochains lexèmes à renvoyer *)
    fun lb ->
      
      if Queue.is_empty tokens then begin
      
        let next = token lb in
        let pos = Lexing.lexeme_start_p lb in 
        let line = pos.pos_lnum in
        if (line <> !last_line) || ((List.length next = 1 && List.nth next 0 = EOF) ) then begin    
              last_line := line;
              let c =  
              if (List.length next = 1 && List.nth next 0 = EOF) then (0) else (pos.pos_cnum - pos.pos_bol) in
             
              let m = ref (Stack.top pile) in 
              if c > !m then ( 
                  if (not (List.mem (!last) fin_cont) &&  (not(List.mem (List.nth next 0) debut_cont))) then (
                      Queue.add LBRAC tokens;
                      Stack.push c pile;
                      );
                  if (!last = LBRAC) then Stack.push c pile
                )
              else (
                while c < !m do
                  
                  let _ = Stack.pop pile in  
                  m := Stack.top pile;
                  if (List.length next == 2 && List.nth next 1 = RBRAC) then () else ( Queue.add SEMICOLON tokens; Queue.add RBRAC tokens)
                done;
                if c > !m then raise(Lexing_error("Erreur d'indentation"));
                if ((not (List.mem (!last) fin_cont)) && (not (List.mem (List.nth next 0) debut_cont))) then
                  Queue.add SEMICOLON tokens;
              )
        end;
        
	      List.iter (fun t -> Queue.add t tokens) next
      end;
      let acc = Queue.pop tokens in 
      last := acc;
      acc
}