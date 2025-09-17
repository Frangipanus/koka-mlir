%{
  open Ast
  
  let is_good (lst : stmt list) = 
  match (List.rev lst) with 
  |[] -> (true)
  |_ -> (match (List.hd (List.rev lst)).stmt with 
        |SBexpr(_)-> true 
        |_ -> false) 

%}

/* Déclaration des tokens */
%token EOF
%token IF
%token THEN
%token ELSE
%token ELIF
%token FN
%token FUN
%token RETURN
%token TRUE
%token FALSE
%token VAL
%token VAR
%token PLUS MINUS MUL DIV MOD CONCAT LT LTE  GTE EQ NEQ AND OR LPAR RPAR LBRAC RBRAC  GT LSPAR RSPAR COMMA ARROW DEF DOT ASSIGN SEMICOLON COLON TILD EXCLAM
%token <string> IDENT
%token <int> INT
%token <string> STRING

/* Priorités et associativités des tokens du plus faible au plus fort */ 
%nonassoc precedence_regle
%nonassoc THEN
%nonassoc IF ELSE ELIF
%left OR
%left AND
%nonassoc ASSIGN EQ NEQ GT GTE LT LTE
%left PLUS MINUS CONCAT
%left MUL DIV MOD
%nonassoc TILD EXCLAM
%nonassoc DOT LBRAC RBRAC FN LPAR RPAR
%nonassoc ARROW
%nonassoc tres
/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <file> file

%%

/* Règles de grammaire */

file:
  | SEMICOLON* ; dl = list( d = decl ; SEMICOLON+ {d}) ; EOF
    { dl }
;

decl:
  | FUN ; i = IDENT ; body = funbody
    { { name = i ; body = body } }
;

funbody:
  | LPAR  ; pl = separated_list(COMMA, param) ; RPAR ; a = annot ; e = expr 
   { { formal = pl ; annot = Some(a) ; body = e } }
   
  | LPAR  ; pl = separated_list(COMMA, param) ; RPAR  ; e = expr %prec precedence_regle
   { { formal = pl ; annot = None ; body = e } }
;

param:
  | s = IDENT ; COLON ; ty = kokatype { {param = (s, ty); loc= ($startpos,$endpos)} } 
;

annot:
  | COLON ; res = result { res } 
;

result:
  | LT  lst = separated_list(COMMA, IDENT)  GT   t = kokatype
    { {res = (lst, t); loc= ($startpos,$endpos)} }
  | t = kokatype { { res = ([], t); loc = ($startpos,$endpos) } }
;
     
kokatype:
  | at = atype { { typ = TAType(at); loc= ($startpos,$endpos) } } %prec precedence_regle
  | at = atype ; ARROW ; res = result { { typ = TFun(at, res); loc = ($startpos,$endpos) } }
  | LPAR ; tl1 = kokatype; COMMA; tl = separated_nonempty_list(COMMA,kokatype) ; RPAR; ARROW ; res = result { { typ = TMulFun(tl1::tl, res); loc= ($startpos,$endpos) } } 
  | LPAR ; tl = kokatype ; RPAR; ARROW ; res = result { { typ = TMulFun([tl], res); loc = ($startpos,$endpos) } } 
  | LPAR; RPAR; ARROW; res = result { { typ = TMulFun([], res) ; loc = ($startpos,$endpos) } }
;
  
atype : 
| s = IDENT  ;LT; ty = kokatype; GT    { { typ = AVar(s, Some(ty)); loc= ($startpos,$endpos) } } 
| s= IDENT { { typ = AVar(s, None); loc= ($startpos,$endpos) } } %prec precedence_regle
| LPAR ty = kokatype RPAR { { typ = AType(ty); loc= ($startpos,$endpos) } } 
| LPAR RPAR { { typ = AEmpty; loc= ($startpos,$endpos) } } %prec precedence_regle
;

atom:
  | TRUE { { bexpr = ATrue; loc= ($startpos,$endpos) } }
  | FALSE { { bexpr = AFalse; loc= ($startpos,$endpos) } }
  | n = INT { { bexpr = Int(n); loc= ($startpos,$endpos) } }
  | id = IDENT { { bexpr = Ident(id); loc= ($startpos,$endpos) } }
  | s = STRING { { bexpr = String(s); loc= ($startpos,$endpos) } }
  | LPAR ; RPAR { { bexpr = Empty; loc= (($startpos,$endpos)) } }
  | LPAR ; e = expr ; RPAR { e }
  | at = atom ; LPAR ; el = separated_list(COMMA, expr) ; RPAR { { bexpr = Eval(at, el); loc= ($startpos,$endpos) } }
  | at = atom ; DOT ; id = IDENT {{bexpr = (Eval({ bexpr = Ident(id); loc= ($startpos,$endpos) }, [at])) ; loc =  ($startpos,$endpos) } }
  | at = atom  FN  fb = funbody 
    { match at.bexpr with
      | Eval(at, el) -> { bexpr = Eval(at, el@[{bexpr = EFn(fb); loc = ($startpos,$endpos)}]) ; loc= ($startpos,$endpos) } 
      | _ -> { bexpr = Eval(at, [{bexpr = EFn(fb); loc = ($startpos,$endpos)}]); loc = ($startpos,$endpos)}}
  | at = atom ; b = block { 
      match at.bexpr with
      | Eval(at, el) -> { bexpr = Eval(at, el@[{bexpr = EFn({formal = []; annot = None; body = {bexpr = EBlock(b); loc = ($startpos, $endpos)}}); loc = ($startpos, $endpos)}]); loc= ($startpos,$endpos) }
      | _ -> { bexpr = Eval(at, [{bexpr = EFn({formal = []; annot = None; body = {bexpr = EBlock(b); loc = ($startpos, $endpos)}}); loc = ($startpos, $endpos)}]); loc= ($startpos,$endpos) } }
  | LSPAR ; el = separated_list(COMMA, expr) ; RSPAR { { bexpr = Brac(el); loc= ($startpos,$endpos) } }
;

expr:
  |s = bexpr { s } %prec precedence_regle
  |s = block {if not(is_good s) then (raise  Error2) else {bexpr = EBlock(s); loc = ($startpos, $endpos)} } 
;

bexpr:
  | a = atom { a } %prec precedence_regle
  | TILD b = bexpr { { bexpr = ETild (b); loc= ($startpos,$endpos) } }
  | EXCLAM b = bexpr { { bexpr = ENot(b); loc= ($startpos,$endpos) } }
  |s = IDENT ASSIGN b =  bexpr { { bexpr = EAsign(s, b); loc= ($startpos, $endpos) } }
  | b1 = bexpr b2 = binop b3 = bexpr  { { bexpr = EBinop(b2,b1,b3); loc= ($startpos,$endpos) } }
  | IF b1 = bexpr THEN b2 = expr lst = elifs { { bexpr = EIf(b1, b2,lst); loc= ($startpos,$endpos) } }
  | IF b1 = bexpr RETURN b2 = expr { { bexpr = EIf (b1, { bexpr = EReturn(b2); loc= ($startpos, $endpos) }, { bexpr = EBlock([]); loc= ($startpos, $endpos) }); loc= ($startpos,$endpos)} }
  | FN f = funbody { { bexpr = EFn(f); loc= ($startpos,$endpos) } }
  | RETURN e = expr { { bexpr = EReturn(e); loc= ($startpos,$endpos) } } 
;

elifs: 
  |%prec precedence_regle  { { bexpr = EBlock([]); loc= ($startpos,$endpos) } }
  | ELIF b2 = bexpr THEN b3 = expr s = elifs { {bexpr = EIf(b2, b3, s); loc= ($startpos,$endpos) } }
  | ELSE b3 = expr { b3 }

block:
  |LBRAC SEMICOLON* lst = list(s = stmt SEMICOLON+ {s})  RBRAC { lst }
;

stmt: 
  | b = bexpr { { stmt = SBexpr(b); loc = ($startpos,$endpos) } }
  | VAL s = IDENT DEF e = expr { { stmt = SDecl(s, e); loc = ($startpos,$endpos) } }
  | VAR s = IDENT ASSIGN e = expr { { stmt = SVar(s,e); loc = ($startpos,$endpos) } }
;

%inline binop:
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | PLUS { Add }
  | MINUS { Sub }
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  | CONCAT { Concat }
  | AND { And }
  | OR { Or }