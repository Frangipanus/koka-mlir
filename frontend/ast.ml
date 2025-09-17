type ident = string
exception Error2

type loc = (Lexing.position * Lexing.position)

(* type *)
and kokaType = {
  typ : kokaType1;
  loc : loc
}

and kokaType1 =
  | TAType of kokaType
  | TFun of kokaType * result
  | TMulFun of kokaType list * result
  | AVar of ident * (kokaType option)
  | AType of kokaType
  | AEmpty

and result = {
  res : ident list * kokaType;
  loc : loc
}

and param = {
  param : ident * kokaType;
  loc : loc
}

(* operations *)
and binop = Eq | Neq | Lt | Lte | Gt | Gte | Add | Sub | Mul | Div | Mod | Concat | And | Or  

(* statement *)
and stmt = {
  stmt : stmt1;
  loc : loc
}

and stmt1 =
  | SBexpr of bexpr
  | SDecl of ident * bexpr 
  | SVar of ident * bexpr

(* expression *)
and bexpr = {
  bexpr : bexpr1;
  loc : loc
}

and bexpr1 =
  | EBlock of stmt list
  | ETild of bexpr
  | ENot of bexpr
  | EBinop of binop * bexpr * bexpr
  | EAsign of ident * bexpr
  | EIf of bexpr * bexpr * bexpr
  | EFn of funbody
  | EReturn of bexpr
  | ATrue | AFalse | Int of int | String of string | Empty
  | Ident of ident
  | Eval of bexpr * (bexpr list)
  | Brac of bexpr list

(* corps d'une fonction *)
and funbody = {
  formal : param list; (* arguments *)
  annot  : result option; (* annotation *)
  body   : bexpr;
}

(* declaration de fonctions *)
and decl = {
  name : string;
  body : funbody;
}

(* fichier *)
and file = decl list