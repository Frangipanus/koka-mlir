open Ast
exception TypeError of string
exception TypeErrorLoc of string * loc
type ident = string

type typ = 
  | Tint 
  | Tbool
  | Tstring 
  | Tunit
  | Tarrow of typ list * full_type
  | Tlist of typ 
  | Tmaybe of typ
  | Tvar of var
 
and var = 
  {id: int; mutable typ : typ option} (*None si c'est une variables libre*)
  
and effect= 
  | Div 
  | Console
  | Full
  | NoEffect
  | Evar of evar

and evar =
  { id : int; mutable containsDiv : bool option; mutable containsConsole : bool option}

and full_type = 
  {typ: typ; effect : effect}

type loc = (Lexing.position * Lexing.position)
  
and tparam = {
  name : ident;
  typ : typ;
  loc : loc
}
  
(* statement *)
and tstmt = {
  stmt  : tstmt1;
  loc   : loc;
  typ   : full_type;
}

and tstmt1 =
  | SBexpr of tbexpr
  | SDecl of ident * tbexpr
  | SVar of ident * tbexpr
  
(* expression *)
and tbexpr = {
  bexpr : tbexpr1;
  loc   : loc;
  typ   : full_type
}

and tbexpr1 = 
  | EBlock of tstmt list
  | ETild of tbexpr
  | ENot of tbexpr
  | EBinop of binop * tbexpr * tbexpr
  | EAsign of ident * tbexpr
  | EIf of tbexpr * tbexpr * tbexpr 
  | EFn of tfunbody 
  | EReturn of tbexpr
  | ATrue
  | AFalse
  | Int of int
  | String of string 
  | Empty 
  | Ident of ident
  | Eval of tbexpr * (tbexpr list)
  | List of tbexpr list
  | Println of tbexpr
  | Default of tbexpr * tbexpr
  | Head of tbexpr
  | Tail of tbexpr
  | For of tbexpr * tbexpr * tbexpr
  | Repeat of tbexpr * tbexpr
  | While of tbexpr * tbexpr
  
(* corps d'une fonction *)
and tfunbody = {
  formal : tparam list; (* arguments *)
  body   : tbexpr;
  typ    : full_type;
}
  
(* declaration de fonctions *)
and tdecl = {
  name : string;
  body : tfunbody;
}
  
(* fichier *)
and tfile = tdecl list

exception Type_Error of string * loc

module Env = Map.Make(String) (*C'est l'environnement de variable.*)
module V = struct
  type t = var
  let compare v1 v2 = Stdlib.compare v1.id v2.id
  let equal v1 v2 = v1.id = v2.id
  let create = let r = ref 0 in fun () -> incr r; { id = !r; typ = None }
end

module Veff = struct
  type t = evar
  let compare v1 v2 = Stdlib.compare v1.id v2.id
  let equal v1 v2 = v1.id = v2.id
  let create = let r = ref 0 in fun () -> incr r; { id = !r; containsDiv = None; containsConsole = None}
end

let rec head t = match t with
  | Tvar { typ = Some(t') } -> head t'
  | _ -> t
  open Format

let rec head_effect eff = match eff with
  | Evar { containsDiv = Some(b1); containsConsole = Some(b2) } -> begin match b1, b2 with
    | false, false -> NoEffect
    | false, true -> Console
    | true, false -> Div
    | true, true -> Full
    end
  | _ -> eff

let hasDiv eff = match head_effect eff with
  | Evar { containsDiv = b} -> b
  | Div | Full -> Some(true)
  | _ -> Some(false)

let hasConsole eff = match head_effect eff with
  | Evar { containsConsole = b} -> b
  | Console | Full -> Some(true)
  | _ -> Some(false)

let rec print_type fmt typ = match head typ with
  | Tint -> fprintf fmt "int"
  | Tbool -> fprintf fmt "bool"
  | Tstring -> fprintf fmt "string"
  | Tunit -> fprintf fmt "()"
  | Tarrow (tl, ft) -> fprintf fmt "@[(@[ %a @]) -> %a@]" print_type_list tl print_full_type ft
  | Tlist(t) -> fprintf fmt "list<@[%a@]>" print_type t
  | Tmaybe(t) -> fprintf fmt "maybe<@[%a@]>" print_type t
  | Tvar(v) -> fprintf fmt "'%d" v.id

and print_type_list fmt tl = match tl with
  | [] -> fprintf fmt ""
  | [typ] -> print_type fmt typ
  | typ::tail -> fprintf fmt "%a, %a" print_type typ print_type_list tail

and print_effect fmt eff = match head_effect eff with
  | NoEffect -> fprintf fmt "<>"
  | Div -> fprintf fmt "<Div>"
  | Console -> fprintf fmt "<Console>"
  | Full -> fprintf fmt "<Div, Console>"
  | Evar(v) -> fprintf fmt "<%d>" v.id

and print_full_type fmt ft =
  fprintf fmt "@[%a@] / %a" print_type ft.typ print_effect ft.effect

let  has_doublon lst = 
  let rec aux lst1 acc = 
    match  lst1 with
    | [] -> false
    |h::q -> (List.mem h acc) || (aux q (h::acc))
  in 
  aux lst []
  
let rec canon t = match t with
  | Tint -> Tint
  | Tbool -> Tbool
  | Tstring -> Tstring
  | Tarrow(tl, ft) -> 
    Tarrow
      (List.fold_right (fun t' acc -> (canon t')::acc) tl [],
       { typ = canon ft.typ; effect = ft.effect })
  | Tlist(t') -> Tlist(canon t')
  | Tmaybe(t') -> Tmaybe(canon t')
  | Tunit -> Tunit
  | Tvar { typ = None } -> t
  | _ -> canon (head t)

exception UnificationFailure of typ * typ
exception UnificationEffectFailure of effect * effect

let unification_error t1 t2 = raise (UnificationFailure (canon t1, canon t2))
let unification_error_eff e1 e2 = raise (UnificationEffectFailure (e1, e2))

let rec occur v t = match head t with
  | Tvar { id = n } when n = v.id -> true
  | Tarrow(tl, ft) -> occur v ft.typ || (List.exists (fun t' -> occur v t') tl)
  | Tlist(t') | Tmaybe(t') -> occur v t'
  | _ -> false

let rec occur_effect ( v : evar) ( eff : effect ) = match head_effect eff with
  | Evar { id = n } when n = v.id -> true
  | _ -> false
    
let full_type_of_type t = { typ = t; effect = NoEffect }

let rec unify_effects (e1 : effect) (e2 : effect) = match head_effect e1, head_effect e2 with
  | ea, eb when ea = eb -> ()
  | Evar v, e | e, Evar v -> 
    if occur_effect v e then unification_error_eff e1 e2
    else
      v.containsDiv <- hasDiv e; v.containsConsole <- hasConsole e
  | _ -> unification_error_eff e1 e2

let rec unify_types (t1 : typ) (t2 : typ) = match head t1, head t2 with
  | ta, tb when ta = tb -> ()
  | Tarrow(tl1, ft1), Tarrow(tl2, ft2) ->
      let rec loop l1 l2 = match l1, l2 with
      | [], [] -> ()
      | [], _ | _, [] -> unification_error t1 t2
      | h1::t1, h2::t2 -> loop t1 t2; unify_types h1 h2
      in loop tl1 tl2; unify_types ft1.typ ft2.typ
  | Tlist(t1'), Tlist(t2') | Tmaybe(t1'), Tmaybe(t2') -> unify_types t1' t2'
  | Tvar v, t -> if occur v t then unification_error t1 t2 else v.typ <-  Some(t2)
  | t, Tvar v -> if occur v t then unification_error t1 t2 else v.typ <- Some(t1)
  | _ -> (unification_error t1 t2)

let rec unify_full_types (t1 : full_type) (t2 : full_type) =
  unify_effects t1.effect t2.effect;
  match head t1.typ, head t2.typ with
  | ta, tb when ta = tb -> ()
  | Tarrow(tl1, ft1), Tarrow(tl2, ft2) ->
      let rec loop l1 l2 = match l1, l2 with
      | [], [] -> ()
      | [], _ | _, [] -> unification_error t1.typ t2.typ
      | h1::t1, h2::t2 -> loop t1 t2; unify_full_types (full_type_of_type h1) (full_type_of_type h2)
      in loop tl1 tl2; unify_full_types ft1 ft2
  | Tlist(t1'), Tlist(t2') | Tmaybe(t1'), Tmaybe(t2') -> unify_full_types (full_type_of_type t1') (full_type_of_type t2')
  | Tvar v, t -> if occur v t then unification_error t1.typ t2.typ else v.typ <- Some(t2.typ)
  | t, Tvar v -> if occur v t then unification_error t1.typ t2.typ else v.typ <- Some(t1.typ)
  | _ -> (unification_error t1.typ t2.typ)

module Vset = Set.Make(V)

let rec fvars t = match head t with
  | Tint | Tbool | Tstring | Tunit -> Vset.empty
  | Tarrow(tl, ft) -> List.fold_left (fun acc t' -> Vset.union acc (fvars t')) Vset.empty (ft.typ::tl)
  | Tlist(t) | Tmaybe(t) -> fvars t
  | Tvar v -> Vset.singleton v

type schema = { vars : Vset.t; typ : full_type }

module Smap = Map.Make(String)

type env = { bindings : schema Smap.t; fvars : Vset.t; muta : ident list }
 
let empty = { bindings = Smap.empty; fvars = Vset.empty; muta = [] }

let add s (t : full_type) env =
  let fvs = fvars t.typ in
  { bindings = Smap.add s { vars = Vset.empty ; typ = t } env.bindings;
    fvars = Vset.union fvs env.fvars; muta = env.muta }

let add_gen s (t : full_type) env =
  let fvs = fvars t.typ in
  let nfvars = (Vset.fold 
    (fun v acc -> Vset.union (fvars (Tvar v)) acc )
    env.fvars Vset.empty) in
  { bindings = Smap.add s { vars = Vset.diff fvs nfvars ; typ = t } env.bindings;
    fvars = nfvars; muta = env.muta }

module Vmap = Map.Make(V)

let find s env =
  let schem = Smap.find s env.bindings in
  let rec aux t vm = match head t with
    | Tint | Tbool | Tstring | Tunit -> t, vm
    | Tarrow(tl, ft) ->
        let tl', vm' = List.fold_right 
          (fun t (acc, vm) ->
            let t', vm' = aux t vm in
            t'::acc, vm')
          tl ([], Vmap.empty) in
        let t', vm'' = aux ft.typ vm' in
        Tarrow(tl', { typ = t'; effect = ft.effect }), vm''
    | Tlist(t) ->
        let t', vm' = aux t vm in
        Tlist(t'), vm' 
    | Tmaybe(t) ->
      let t', vm' = aux t vm in
      Tmaybe(t'), vm' 
    | Tvar v when Vset.mem v schem.vars -> begin match Vmap.find_opt v vm with
      | Some(v') -> Tvar v', vm
      | None -> 
          let v' = V.create () in
          Tvar v', Vmap.add v v' vm
      end
    | Tvar v -> Tvar v, vm
  in 
  let t = (Smap.find s env.bindings).typ in
  { typ = fst (aux t.typ Vmap.empty); effect = t.effect}

(* Calcule le nouvel effet total après lui avoir rajouté un effet *)
let add_effect eff1 eff2 = match head_effect eff1, head_effect eff2 with
  | Full, _ | _, Full -> Full
  | e, NoEffect | NoEffect, e -> e
  | e, f when e = f -> e
  | Evar _, _ | _, Evar _ ->
      let v1 = Veff.create () in
      v1.containsDiv <- begin match hasDiv eff1, hasDiv eff2 with
      | None, None -> None
      | Some(true), _ | _, Some(true) -> Some(true)
      | _ -> Some(false)
      end;
      v1.containsConsole <- begin match hasConsole eff1, hasConsole eff2 with
      | None, None -> None
      | Some(true), _ | _, Some(true) -> Some(true)
      | _ -> Some(false)
      end;
      head_effect (Evar v1)
  | _ -> Full

let effect_of_ident id = match id with
  | "div" -> Div
  | "console" -> Console
  | _ -> raise (TypeError "effet inexistant" )

(* type waiting_type = { mutable typ : full_type option } *)

(* Renvoie la tdecl correspondant à la decl, et le nouvel environnement *)
let rec w_decl env (decl : decl) =
  if (decl.name = "main" && (List.length decl.body.formal > 0)) then (raise (TypeError ("main takes no argument"))) else ();
  let fb, tl, ft = w_funbody env (Some(decl.name)) decl.body in
  if (has_doublon (List.map (fun x ->  x.name) (fb.formal))) then raise (TypeError "fonction a 2 paramètre de meme nom")
  else (
  { name = decl.name; body = fb}, (add decl.name { typ = Tarrow(tl, ft); effect = ft.effect } env) )

(* Renvoie le tfunbody correspondant au funbody, la liste de types des paramètres, et le type de renvoi de la fonction*)
and w_funbody env name (fb : funbody) =
  let env, tl, formal', name = List.fold_right 
    (fun { param = (x, t); loc = loc } (env, tl, fl, name) -> 
      let t' = w_type env t in
      let name = if Some(x) = name then None else name in
      add x { typ = t'; effect = NoEffect } env, t'::tl, { name = x; typ = t'; loc = loc}::fl, name) 
      fb.formal (env, [], [], name) in
  let ft, tbody = match fb.annot with
  | Some(k) -> begin 
        let ft = w_result env k in
        let env= match name with
          | Some(f) -> add f { typ = Tarrow(tl, ft) ; effect = NoEffect } env
          | None -> env
        in let return_type = V.create () in
        return_type.typ <- Some(ft.typ);
        let tbody = w_bexpr env fb.body name return_type in
        (try unify_full_types tbody.typ ft with 
          | UnificationFailure(_,_) -> raise (TypeError "La fonction renvoie le mauvais type \n")
          | UnificationEffectFailure(_,_) -> raise (TypeError "La fonction a le mauvais effet \n")
          );
        ft, tbody end
  | None -> 
      let return_type = V.create () in
      let return_effect = Veff.create () in
      let env = match name with
      | Some(f) -> add f { typ = Tarrow(tl, { typ = Tvar(return_type); effect = Evar(return_effect) }); effect = NoEffect } env
      | None -> env
      in let tbody = w_bexpr env fb.body name return_type in
      try
        unify_effects (Evar return_effect) tbody.typ.effect;
        unify_types (Tvar return_type) tbody.typ.typ;
        tbody.typ, tbody
      with 
      | UnificationFailure(_,_) -> raise (TypeError "La fonction renvoie le mauvais type\n")
      | UnificationEffectFailure(_,_) -> raise (TypeError "La fonction renvoie le mauvais effet\n")
    in { formal = formal' ; body = tbody ; typ = { typ = Tarrow(tl, ft); effect = NoEffect }}, tl, ft

(* Renvoie le tbexpr correspondant à bexpr et vérifie que les éventuels return sont du bon type *)
and w_bexpr env bexpr fun_name (return_type : var) : tbexpr = match bexpr.bexpr with
  | EBlock sl -> 
      let tsl, _, ft = ( List.fold_left 
        (fun (acc, env, ( ft : full_type )) (stmt : stmt) -> 
          let (tstmt, env') = w_stmt env stmt fun_name return_type in
          (acc @ [tstmt], env', { typ = head tstmt.typ.typ; effect = add_effect ft.effect tstmt.typ.effect }))
        ([], env, { typ = Tunit; effect = NoEffect }) sl ) in
      { bexpr = EBlock tsl;
        loc = bexpr.loc;
        typ = ft
      }

  | ETild be ->
      let tbe = w_bexpr env be fun_name return_type in
      begin match head tbe.typ.typ with
      | Tint -> { bexpr = ETild(tbe); loc = bexpr.loc; typ = tbe.typ }
      | _ -> raise (TypeErrorLoc ("~ doit être utilisée sur un entier \n", bexpr.loc))
      end

  | ENot be ->
      let tbe = w_bexpr env be fun_name return_type in
      begin match head tbe.typ.typ with
      | Tbool -> { bexpr = ENot(tbe); loc = bexpr.loc; typ = tbe.typ }
      | _ -> raise (TypeErrorLoc ("! doit être utilisée sur un booléen \n", bexpr.loc))
      end

  | EBinop(op, be1, be2) ->
      let tbe1 = w_bexpr env be1 fun_name return_type in
      let tbe2 = w_bexpr env be2 fun_name return_type in
      begin match op with
      | Add | Sub | Mul | Div | Mod -> begin
        try
          unify_types tbe1.typ.typ Tint;
          unify_types tbe2.typ.typ Tint;
          { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tint; effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
        with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Opération entre deux objets du mauvais type \n", bexpr.loc)) end

      | Lt | Lte | Gt | Gte -> begin 
        try
          unify_types tbe1.typ.typ Tint;
          unify_types tbe2.typ.typ Tint;
          { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tbool; effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
        with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Opération entre deux objets du mauvais type \n", bexpr.loc)) end

      | Eq | Neq -> begin 
        (try
          unify_types tbe1.typ.typ tbe2.typ.typ
        with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Comparaison de deux éléments de types différents \n", bexpr.loc)));
        let t1 = head tbe1.typ.typ in
        if t1 <> Tint && t1 <> Tbool && t1 <> Tstring then raise (TypeErrorLoc ("Impossible de comparer deux éléments de types autre que int, bool ou string. \n", bexpr.loc))
        else { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tbool; effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
        end 
      | And | Or -> begin 
        try
          unify_types tbe1.typ.typ Tbool;
          unify_types tbe2.typ.typ Tbool;
          { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tbool; effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
        with UnificationFailure(_,_) ->raise (TypeErrorLoc ("Opération entre deux objets du mauvais type \n", bexpr.loc)) end

      | Concat -> 
        try
          unify_types tbe1.typ.typ Tstring;
          unify_types tbe2.typ.typ Tstring;
          { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tstring; effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
        with UnificationFailure(_,_) -> try
          unify_types tbe1.typ.typ (Tlist(Tvar(V.create())));
          unify_types tbe2.typ.typ (Tlist(Tvar(V.create())));
          try
            let Tlist(t1) = head tbe1.typ.typ in
            let Tlist(t2) = head tbe2.typ.typ in
            unify_types t1 t2;
            { bexpr = EBinop(op, tbe1, tbe2); loc = bexpr.loc; typ = { typ = Tlist(t1); effect = add_effect tbe1.typ.effect tbe2.typ.effect } }
          with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Impossible de concaténer deux listes contenant des types différents \n", bexpr.loc))
        with UnificationFailure(_,_) -> raise   (TypeErrorLoc ("Opération entre deux objets du mauvais type \n", bexpr.loc));
        
      end

  | EAsign(id, be) ->
    if not(List.mem id env.muta) then (raise (TypeErrorLoc ("La variables n'est pas mutable \n",bexpr.loc))) else();
      let tbe = w_bexpr env be fun_name return_type in
      { bexpr = EAsign(id, tbe); loc = bexpr.loc; typ = { typ = Tunit; effect = tbe.typ.effect } }

  | EIf(be1, be2, be3) -> begin
      let tbe1 = w_bexpr env be1 fun_name return_type in
      let tbe2 = w_bexpr env be2 fun_name return_type in
      let tbe3 = w_bexpr env be3 fun_name return_type in
      try unify_types tbe1.typ.typ Tbool;
        try
          unify_types tbe2.typ.typ tbe3.typ.typ;
          let t2 = head tbe2.typ.typ in
          { bexpr = EIf(tbe1, tbe2, tbe3); loc = bexpr.loc; typ = { typ = t2; effect = add_effect (add_effect tbe1.typ.effect tbe2.typ.effect) tbe3.typ.effect } }
        with UnificationFailure(_,_) -> raise ( TypeErrorLoc ("Les résultats des deux cas de 'If' doivent être du même type \n", bexpr.loc))
      with UnificationFailure(_,_) -> raise (TypeErrorLoc ("'If' attends un booléen \n", be1.loc));
      
    end

  | EFn(fb) ->
      let tfb, tl, ft = w_funbody env None fb in
      if (has_doublon (List.map (fun x ->  x.name) (tfb.formal))) then raise (TypeErrorLoc ("Cette fonction a deux paramètres avec le même nom \n", bexpr.loc))
  else
      { bexpr = EFn(tfb); typ = { typ = Tarrow(tl, ft); effect = NoEffect }; loc = bexpr.loc } 

  | EReturn(be) ->
      let tbe = w_bexpr env be fun_name return_type in
      
      begin match return_type.typ with
      | None -> 
          return_type.typ <- Some(tbe.typ.typ);
          { bexpr = EReturn(tbe); typ = { typ = Tvar(V.create ()); effect = tbe.typ.effect }; loc = bexpr.loc }

      | Some(t) -> 
          try unify_types t tbe.typ.typ; { bexpr = EReturn(tbe); typ = { typ = Tvar(V.create ()); effect = tbe.typ.effect }; loc = bexpr.loc }
          with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Mauvais type retourné \n", bexpr.loc))
      end

  | ATrue -> { bexpr = ATrue; typ = { typ = Tbool; effect = NoEffect }; loc = bexpr.loc }

  | AFalse -> { bexpr = AFalse; typ = { typ = Tbool; effect = NoEffect }; loc = bexpr.loc }

  | Int(n) -> { bexpr = Int(n); typ = { typ = Tint; effect = NoEffect}; loc = bexpr.loc }

  | String(s) -> { bexpr = String(s); typ = { typ = Tstring; effect = NoEffect}; loc = bexpr.loc}

  | Empty -> { bexpr = Empty; typ = { typ = Tunit; effect = NoEffect }; loc = bexpr.loc }

  | Ident(id) -> begin
      try 
        let t = find id env in
        
        let eff = if Some(id) = fun_name then add_effect t.effect Div else t.effect in
        { bexpr = Ident(id); typ = { typ = t.typ; effect = eff }; loc = bexpr.loc } 
      with Not_found -> raise (TypeErrorLoc ("Variable inconnue ici: "^id^" \n", bexpr.loc))
      end

  | Eval(f, args) ->
      begin match f.bexpr with
      | Ident("println") ->
          begin match args with
          | [be] ->
              let tbe = w_bexpr env be fun_name return_type in
              if List.mem (head tbe.typ.typ) [Tunit; Tbool; Tint; Tstring] then
                { bexpr = Println(tbe); typ = { typ = Tunit; effect = add_effect Console tbe.typ.effect }; loc = bexpr.loc }
              else (  
              raise (TypeErrorLoc ("Argument du mauvais type pour println \n", bexpr.loc)))
          | _ -> raise   (TypeErrorLoc   ("Mauvais nombre d'arguments pour println \n", bexpr.loc))
          end

      | Ident("default") ->
          begin match args with
          | [be1; be2] ->
              begin let tbe1 = w_bexpr env be1 fun_name return_type in
              let tbe2 = w_bexpr env be2 fun_name return_type in
              try
                (*printf "%a \n %a \n" print_full_type tbe1.typ print_full_type tbe2.typ;*)
                unify_types tbe1.typ.typ (Tmaybe tbe2.typ.typ);
                { bexpr = Default(tbe1, tbe2); typ = { typ = tbe2.typ.typ; effect = add_effect tbe1.typ.effect tbe2.typ.effect }; loc = bexpr.loc }
              with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Arguments incompatibles \n", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("Mauvais nombre d'arguments pour defaul \nt", bexpr.loc))
          end

      | Ident("head") ->
          begin match args with
          | [be] ->
              begin let tbe = w_bexpr env be fun_name return_type in
              try
                let var = V.create () in
                unify_types tbe.typ.typ (Tlist (Tvar(var)));
                { bexpr = Head(tbe); typ = { typ = Tmaybe (head (Tvar var)); effect = tbe.typ.effect }; loc = bexpr.loc }
              with UnificationFailure(_,_) -> raise (TypeErrorLoc ("head prend une liste en argumen \nt", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("Mauvais nombre d'arguments pour head \n", bexpr.loc))
          end

      | Ident("tail") ->
          begin match args with
          | [be] ->
              begin let tbe = w_bexpr env be fun_name return_type in
              try
                unify_types tbe.typ.typ (Tlist (Tvar(V.create ())));
                { bexpr = Tail(tbe); typ = tbe.typ; loc = bexpr.loc }
              with UnificationFailure(_,_) -> raise (TypeErrorLoc ("tail prend une liste en argument \n", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("Mauvais nombre d'arguments pour tail \n", bexpr.loc))
          end

      | Ident("for") ->
          begin match args with
          | [be1; be2; be3] ->
              let tbe1 = w_bexpr env be1 fun_name return_type in
              let tbe2 = w_bexpr env be2 fun_name return_type in
              let tbe3 = w_bexpr env be3 fun_name return_type in
              begin match head tbe1.typ.typ, head tbe2.typ.typ, head tbe3.typ.typ with
              | Tint, Tint, Tarrow([Tint], { typ = Tunit; effect = eff }) ->
                  { bexpr = For(tbe1, tbe2, tbe3); typ = { typ = Tunit; effect = add_effect tbe1.typ.effect (add_effect tbe2.typ.effect (add_effect tbe3.typ.effect eff)) }; loc = bexpr.loc }
              | _ -> raise (TypeErrorLoc ("For attends un entier de début, un entier de fin et un contenu de la forme (int)->unit. \n", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("For attends un entier de début, un entier de fin et un contenu de la forme (int)->unit. \n", bexpr.loc))
          end

      | Ident("repeat") ->
          begin match args with
          | [be1; be2] ->
              let tbe1 = w_bexpr env be1 fun_name return_type in
              let tbe2 = w_bexpr env be2 fun_name return_type in
              begin match head tbe1.typ.typ, head tbe2.typ.typ with
              | Tint, Tarrow([], { typ = Tunit; effect = eff}) ->
                  { bexpr = Repeat(tbe1, tbe2); typ = { typ = Tunit; effect = add_effect tbe1.typ.effect (add_effect tbe2.typ.effect eff) }; loc = bexpr.loc }
              | _ -> raise (TypeErrorLoc ("Repeat attends un nombre de répétitions ainsi qu'un contenu de la forme ()->unit \n", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("Repeat attends un nombre de répétitions ainsi qu'un contenu de la forme ()->unit \n", bexpr.loc))
          end

      | Ident("while") ->

          begin match args with
          | [be1; be2] ->
              let tbe1 = w_bexpr env be1 fun_name return_type in
              let tbe2 = w_bexpr env be2 fun_name return_type in
              begin match head tbe1.typ.typ, head tbe2.typ.typ with
              | Tarrow([], { typ = tb; effect = eff1 }), Tarrow([], { typ = tu; effect = eff2}) ->  
                  begin try
                    unify_types tb Tbool;
                    unify_types tu Tunit;
                    { bexpr = While(tbe1, tbe2); typ = { typ = Tunit; effect = add_effect tbe1.typ.effect (add_effect eff1 (add_effect tbe2.typ.effect (add_effect eff2 Div))) }; loc = bexpr.loc }
                  with UnificationFailure(_, _) -> raise (TypeErrorLoc ("While attends en premier argument une fonction () -> bool et en second argument une fonction () -> unit \n", bexpr.loc))
                  end
              | _ -> raise (TypeErrorLoc ("While attends en premier argument une fonction () -> bool et en second argument une fonction () -> unit \n", bexpr.loc))
              end
          | _ -> raise (TypeErrorLoc ("While attends deux arguments \n", bexpr.loc))
          end
      | _ ->
          let tf = w_bexpr env f fun_name return_type in
          let targs = List.map (fun arg -> w_bexpr env arg fun_name return_type) args in
          let tl, rt = match head tf.typ.typ with
          | Tarrow(tl, rt) -> tl, rt
          | _ -> raise (TypeErrorLoc ("Fonction attendue \n", bexpr.loc))
          in let rec loop l1 (l2 : tbexpr list) = match l1, l2 with
          | [], [] -> ()
          | _, [] | [], _ -> raise (TypeErrorLoc ("Nombre d'arguments invalide \n", bexpr.loc))
          | h1::t1, h2::t2 -> 
              try unify_full_types (full_type_of_type h1) (full_type_of_type h2.typ.typ); 
              loop t1 t2 
            with UnificationFailure(_,_)|UnificationEffectFailure(_,_) -> raise (TypeErrorLoc ("Arguments de mauvais type \n", bexpr.loc))
          in loop tl targs;
          let eff = add_effect tf.typ.effect (add_effect rt.effect (List.fold_left (fun acc (x : tbexpr) -> add_effect acc x.typ.effect) NoEffect targs)) in
          { bexpr = Eval(tf, targs); typ = { typ = rt.typ; effect = eff }; loc = bexpr.loc}
      end

  | Brac(bel) ->
      let tbel = List.map (fun x -> w_bexpr env x fun_name return_type) bel in
      begin match tbel with
      | [] -> { bexpr = List([]); typ = { typ = Tlist(Tvar(V.create())); effect = NoEffect }; loc = bexpr.loc}
      | h::t ->
          let htyp = h.typ in
          let eff = List.fold_left 
            (fun acc (x : tbexpr) -> 
              try
                unify_types x.typ.typ htyp.typ;
                add_effect acc x.typ.effect
              with UnificationFailure(_,_) -> raise (TypeErrorLoc ("Une file ne peut contenir qu'un seul type \n", bexpr.loc))) htyp.effect t
          in { bexpr = List(tbel); typ = { typ = Tlist(htyp.typ); effect = eff }; loc = bexpr.loc }
      end

(* Renvoie le tstmt correspondant à stmt ainsi que le nouvel environnement *)
and w_stmt env stmt fun_name return_type : tstmt * env = match stmt.stmt with
  | SBexpr(be) ->
      let tbe = w_bexpr env be fun_name return_type in
      { stmt = SBexpr(tbe); typ = tbe.typ; loc = stmt.loc }, env
  | SDecl(id, be) ->
      let tbe = w_bexpr env be fun_name return_type in
      let env' = add id tbe.typ env in
      printf "%a  \n" print_full_type tbe.typ;

      { stmt = SDecl(id, tbe); typ = { typ = Tunit; effect = tbe.typ.effect }; loc = stmt.loc }, env'
  | SVar(id, be) ->
    let tbe = w_bexpr env be fun_name return_type in
    let env' = add id tbe.typ env in

    { stmt = SVar(id, tbe); typ = { typ = Tunit; effect = tbe.typ.effect }; loc = stmt.loc }, {env' with muta = id::env'.muta}
  
(* Renvoie le full_type correspondant au résulat res *)
and w_result env res = match res.res with
  | idl, t -> 
    { typ = w_type env t; 
      effect = List.fold_left (fun acc id -> add_effect acc (effect_of_ident id)) NoEffect idl }

(* Renvoie le type correspondant au kokaType typ *)
and w_type env typ = match typ.typ with
  | TAType(t) | AType(t) -> w_type env t
  | TFun(t, res) ->
      let ft_res = w_result env res in
      let ft_in = w_type env t in
      Tarrow([ft_in], ft_res)
  | TMulFun(tl, res) ->
      let ft_res = w_result env res in
      let tl_in = List.map (fun t -> w_type env t) tl in
      Tarrow(tl_in, ft_res)
  | AEmpty -> Tunit
  | AVar("unit", None) -> Tunit
  | AVar("bool", None) -> Tbool
  | AVar("int", None) -> Tint
  | AVar("string", None) -> Tstring
  | AVar("list", Some(t)) -> Tlist(w_type env t)
  | AVar("maybe", Some(t)) -> Tmaybe(w_type env t)
  | _ -> raise (TypeError "Type inconnu")

let w (file : file)  = 
  if not(List.mem "main" (List.map (fun (x: decl) -> x.name) file)) then raise (TypeError "no main") else ();
  fst (List.fold_left 
  (fun (acc, env) decl -> 
    let decl', env' = w_decl env decl in
    acc@[decl'], env')
   ([], empty) file)

(*let rec print_file fmt file = match file with
  | [] -> fprintf fmt ""
  | decl -> fprintf fmt "@[%a@]" print_decl decl
  | decl::t -> fprintf fmt "@[%a@], %a" print_decl declt print_file t

and print_decl fmt decl =
  fprintf fmt "@[%s %a@]" decl.name print_funbody decl.body

and print_funbody fmt fb =
  fprintf fmt "@[(%a) = %a : %a@]" print_param_list fb.formal print_decl fb.body print_type fb.typ

and print_param_list fmt pl = match pl with
  | [] -> fprintf fmt ""
  | param -> fprintf fmt "@[%s : %a@]" param.name print_type param.typ
  | param::t -> fprintf fmt "@[%s : %a@], %a" param.name print_type param.typ print_param_list t

and print_bexpr fmt bexpr = match bexpr.bexpr with
  | EBlock(sl) -> fprintf fmt "{%a} : %a" print_stmt_list sl print_type bexpr.typ
  | ETild(be) -> fprintf fmt "~(%a) : %a" print_bexpr be print_type bexpr.typ
  | ENot(be) -> fprintf fmt "!(%a) : %a" print_bexpr be print_type bexpr.typ

and print_stmt_list fmt sl = failwith "AF"

and print_stmt fmt stmt = failwith "AF"*)