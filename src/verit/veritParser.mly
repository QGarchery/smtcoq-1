/**************************************************************************/
/*                                                                        */
/*     SMTCoq                                                             */
/*     Copyright (C) 2011 - 2016                                          */
/*                                                                        */
/*     Michaël Armand                                                     */
/*     Benjamin Grégoire                                                  */
/*     Chantal Keller                                                     */
/*                                                                        */
/*     Inria - École Polytechnique - Université Paris-Sud                 */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/


%{
  open SmtAtom
  open SmtForm
  open VeritSyntax

  let apply_opt_atom f = function
  | Some (Atom h) -> Some (Atom (f h))
  | None -> None
  | _ -> assert false

  let apply_bopt_atom f o1 o2 =
    match o1, o2 with
    | Some (Atom h1), Some (Atom h2) -> Some (Atom (f h1 h2))
    | Some (Atom _), None -> None
    | None, Some (Atom _) -> None
    | _ -> assert false

%}


/*
  définition des lexèmes
*/

%token EOL SAT
%token COLON SHARP
%token LPAR RPAR
%token NOT XOR ITE EQ LT LEQ GT GEQ PLUS MINUS MULT OPP LET DIST
%token INPU DEEP TRUE FALS ANDP ANDN ORP ORN XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2 EQUP1 EQUP2 EQUN1 EQUN2 ITEP1 ITEP2 ITEN1 ITEN2 EQRE EQTR EQCO EQCP DLGE LAGE LATA DLDE LADE FINS EINS SKEA SKAA QNTS QNTM RESO AND NOR OR NAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2 EQU1 EQU2 NEQU1 NEQU2 ITE1 ITE2 NITE1 NITE2 TPAL TLAP TPLE TPNE TPDE TPSA TPIE TPMA TPBR TPBE TPSC TPPP TPQT TPQS TPSK SUBP HOLE FORALL
%token <int> INT
%token <Big_int.big_int> BIGINT
%token <string> VAR BINDVAR ATVAR


/* type de "retour" du parseur : une clause */
%type <int> line
/*
%type <VeritSyntax.atom_form_lit> term
%start term
*/
%start line


%%

line:
  | SAT                                                    { raise Sat }
  | INT COLON LPAR typ clause                   RPAR EOL   { mk_clause ($1,$4,$5,[]) }
  | INT COLON LPAR typ clause clause_ids_params RPAR EOL   { mk_clause ($1,$4,$5,$6) }
  | INT COLON LPAR TPQT LPAR SHARP INT COLON LPAR forall_decl RPAR RPAR INT RPAR EOL { add_solver $7 $10; add_ref $7 $1; mk_clause ($1, Tpqt, [], [$13]) }
  | INT COLON LPAR FINS LPAR SHARP INT COLON LPAR OR LPAR NOT SHARP INT RPAR lit RPAR RPAR RPAR EOL
  { match $16 with Some l -> mk_clause ($1, Fins, [l], [get_ref $14]) | None -> assert false } 
;


typ:
  | TPBR                                                   { Tpbr  }
  | INPU                                                   { Inpu  }
  | DEEP                                                   { Deep  }
  | TRUE                                                   { True  }
  | FALS                                                   { Fals  }
  | ANDP                                                   { Andp  }
  | ANDN                                                   { Andn  }
  | ORP                                                    { Orp   }
  | ORN                                                    { Orn   }
  | XORP1                                                  { Xorp1 }
  | XORP2                                                  { Xorp2 }
  | XORN1                                                  { Xorn1 }
  | XORN2                                                  { Xorn2 }
  | IMPP                                                   { Impp  }
  | IMPN1                                                  { Impn1 }
  | IMPN2                                                  { Impn2 }
  | EQUP1                                                  { Equp1 }
  | EQUP2                                                  { Equp2 }
  | EQUN1                                                  { Equn1 }
  | EQUN2                                                  { Equn2 }
  | ITEP1                                                  { Itep1 }
  | ITEP2                                                  { Itep2 }
  | ITEN1                                                  { Iten1 }
  | ITEN2                                                  { Iten2 }
  | EQRE                                                   { Eqre  }
  | EQTR                                                   { Eqtr  }
  | EQCO                                                   { Eqco  }
  | EQCP                                                   { Eqcp  }
  | DLGE                                                   { Dlge  }
  | LAGE                                                   { Lage  }
  | LATA                                                   { Lata  }
  | DLDE                                                   { Dlde  }
  | LADE                                                   { Lade  }
  | EINS                                                   { Eins  }
  | SKEA                                                   { Skea  }
  | SKAA                                                   { Skaa  }
  | QNTS                                                   { Qnts  }
  | QNTM                                                   { Qntm  }
  | RESO                                                   { Reso  }
  | AND                                                    { And   }
  | NOR                                                    { Nor   }
  | OR                                                     { Or    }
  | NAND                                                   { Nand  }
  | XOR1                                                   { Xor1  }
  | XOR2                                                   { Xor2  }
  | NXOR1                                                  { Nxor1 }
  | NXOR2                                                  { Nxor2 }
  | IMP                                                    { Imp   }
  | NIMP1                                                  { Nimp1 }
  | NIMP2                                                  { Nimp2 }
  | EQU1                                                   { Equ1  }
  | EQU2                                                   { Equ2  }
  | NEQU1                                                  { Nequ1 }
  | NEQU2                                                  { Nequ2 }
  | ITE1                                                   { Ite1  }
  | ITE2                                                   { Ite2  }
  | NITE1                                                  { Nite1 }
  | NITE2                                                  { Nite2 }
  | TPAL                                                   { Tpal  }
  | TLAP                                                   { Tlap  }
  | TPLE                                                   { Tple  }
  | TPNE                                                   { Tpne  }
  | TPDE                                                   { Tpde  }
  | TPSA                                                   { Tpsa  }
  | TPIE                                                   { Tpie  }
  | TPMA                                                   { Tpma  }
  | TPBE                                                   { Tpbe  }
  | TPSC                                                   { Tpsc  }
  | TPPP                                                   { Tppp  }
  | TPQS                                                   { Tpqs  }
  | TPSK                                                   { Tpsk  }
  | SUBP                                                   { Subp  }
  | HOLE                                                   { Hole  }
;

clause:
  | LPAR          RPAR                                     { [] }
  | LPAR lit_list RPAR                                     { match list_opt $2 with None -> [] | Some l -> l }
;

lit_list:
  | lit                                                    { [$1] }
  | lit lit_list                                           { $1::$2 }
;

lit:   /* returns a SmtAtom.Form.t option */
  | name_term                                              { apply_opt (lit_of_atom_form_lit rf) $1 }
  | LPAR NOT lit RPAR                                      { apply_opt Form.neg $3 }
;

nlit:   
  | LPAR NOT lit RPAR                                      { apply_opt Form.neg $3 }
;

maybeatvar:   
  | VAR			                                   { $1 }
  | ATVAR			                           { $1 }
;

name_term:   /* returns a (SmtAtom.Form.pform or SmtAtom.hatom) option */
  | SHARP INT                                              { Some (get_solver $2) }
  | SHARP INT COLON LPAR term RPAR                         { apply_opt (fun x -> add_solver $2 x; x) $5 }
  | TRUE                                                   { Some (Form Form.pform_true) }
  | FALS                                                   { Some (Form Form.pform_false) }
  | maybeatvar							   { let x = $1 in if mem_qvar x then None else 
    							     Some (Atom (Atom.get ra (Aapp (get_fun $1, [||])))) }
  | BINDVAR                                                { Some (Hashtbl.find hlets $1) }
  | INT                                                    { Some (Atom (Atom.hatom_Z_of_int ra $1)) }
  | BIGINT                                                 { Some (Atom (Atom.hatom_Z_of_bigint ra $1)) }
;

var_decl_list:
  | LPAR maybeatvar VAR RPAR				   { add_qvar $2 }
  | LPAR maybeatvar VAR RPAR var_decl_list		   { add_qvar $2 }
;

forall_decl:
  | FORALL LPAR var_decl_list RPAR name_term		   { clear_qvar (); Form Form.pform_true }
; 

term:   /* returns a (SmtAtom.Form.pform or SmtAtom.hatom) option */
  | LPAR term RPAR                                         { $2 }

  /* Formulae */
  | TRUE                                                   { Some (Form Form.pform_true) }
  | FALS                                                   { Some (Form Form.pform_false) }
  | AND lit_list                                           { apply_opt (fun x -> Form (Fapp (Fand, Array.of_list x))) (list_opt $2) }
  | OR lit_list                                            { apply_opt (fun x -> Form (Fapp (For, Array.of_list x))) (list_opt $2) }
  | IMP lit_list                                           { apply_opt (fun x -> Form (Fapp (Fimp, Array.of_list x))) (list_opt $2) }
  | XOR lit_list                                           { apply_opt (fun x -> Form (Fapp (Fxor, Array.of_list x))) (list_opt $2) }
  | ITE lit_list                                           { apply_opt (fun x -> Form (Fapp (Fite, Array.of_list x))) (list_opt $2) }
  | forall_decl                                            { Some $1 }

  /* Atoms */
  | INT                                                    { Some (Atom (Atom.hatom_Z_of_int ra $1)) }
  | BIGINT                                                 { Some (Atom (Atom.hatom_Z_of_bigint ra $1)) }
  | LT name_term name_term                                 { apply_bopt_atom (Atom.mk_lt ra) $2 $3 }
  | LEQ name_term name_term                                { apply_bopt_atom (Atom.mk_le ra) $2 $3 }
  | GT name_term name_term                                 { apply_bopt_atom (Atom.mk_gt ra) $2 $3 }
  | GEQ name_term name_term                                { apply_bopt_atom (Atom.mk_ge ra) $2 $3 }
  | PLUS name_term name_term                               { apply_bopt_atom (Atom.mk_plus ra) $2 $3 }
  | MULT name_term name_term                               { apply_bopt_atom (Atom.mk_mult ra) $2 $3 }
  | MINUS name_term name_term                              { apply_bopt_atom (Atom.mk_minus ra) $2 $3}
  | MINUS name_term                                        { apply_opt_atom (Atom.mk_opp ra) $2 }
  | OPP name_term                                          { apply_opt_atom (Atom.mk_opp ra) $2 }
  | DIST args                                              { apply_opt (fun l -> let a = Array.of_list l in Atom (Atom.mk_distinct ra (Atom.type_of a.(0)) a)) (list_opt $2) }
  | VAR                                                    { let x = $1 in if mem_qvar x then None else 
    							     Some (Atom (Atom.get ra (Aapp (get_fun x, [||])))) }
  | VAR args                                               { let x = $1 in if mem_qvar x then None else 
    							     apply_opt (fun l -> Atom (Atom.get ra (Aapp (get_fun x, Array.of_list l)))) (list_opt $2) }

  /* Both */
  | EQ name_term name_term                                 { let t1 = $2 in let t2 = $3 in match t1,t2 with | Some (Atom h1), Some (Atom h2) when (match Atom.type_of h1 with | SmtBtype.Tbool -> false | _ -> true) -> Some (Atom (Atom.mk_eq ra (Atom.type_of h1) h1 h2)) | Some t1, Some t2 -> Some (Form (Fapp (Fiff, [|lit_of_atom_form_lit rf t1; lit_of_atom_form_lit rf t2|]))) | _ -> None }
  | EQ nlit lit                                            { match $2, $3 with Some t1, Some t2 -> Some (Form (Fapp (Fiff, [|t1; t2|]))) | _ -> None }
  | EQ name_term nlit                                      { match $2, $3 with Some t1, Some t2 -> Some (Form (Fapp (Fiff, [|lit_of_atom_form_lit rf t1; t2|]))) | _ -> None }	
  | LET LPAR bindlist RPAR name_term                       { $3; $5 }
  | BINDVAR                                                { Some (Hashtbl.find hlets $1) }
;

blit:   
  | name_term                                              { $1 } 
  | LPAR NOT lit RPAR                                      { apply_opt (fun l -> Lit (Form.neg l)) $3 }
;

bindlist:
  | LPAR BINDVAR blit RPAR	                           { match $3 with | Some t -> Hashtbl.add hlets $2 t | None -> assert false }
  | LPAR BINDVAR blit RPAR bindlist                        { begin match $3 with | Some t -> Hashtbl.add hlets $2 t | None -> assert false end; $5 }

args:
  | name_term                                              { match $1 with Some (Atom h) -> [Some h] | None -> [None] | _ -> assert false }
  | name_term args                                         { match $1 with Some (Atom h) -> (Some h)::$2 | None -> None::$2 | _ -> assert false }
;

clause_ids_params:
  | int_list                                               { $1 }
;

int_list:
  | INT                                                    { [$1] }
  | INT int_list                                           { let x1 = $1 in let x2 = $2 in x1::x2 }
;
