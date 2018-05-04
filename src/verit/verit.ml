(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SmtAtom


let debug = false


(******************************************************************************)
(* Given a verit trace build the corresponding certif and theorem             *)
(******************************************************************************)
exception Import_trace of int

let get_val = function
    Some a -> a
  | None -> assert false

                            
let rec import_trace filename first =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let confl_num = ref (-1) in
  let first_num = ref (-1) in
  let is_first = ref true in
  let line = ref 1 in
  (* let _ = Parsing.set_trace true in *)
  try
    while true do
      confl_num := VeritParser.line VeritLexer.token lexbuf;
      if !is_first then (
        is_first := false;
        first_num := !confl_num
      );
      incr line
    done;
    raise VeritLexer.Eof
  with
    | VeritLexer.Eof ->
       close_in chan;
       let first =
         let aux = VeritSyntax.get_clause !first_num in
         match first, aux.value with
         | Some (root,l), Some (fl::nil) ->
            if Form.equal l fl then
              aux
            else (
              aux.kind <- Other (ImmFlatten(root,fl));
              SmtTrace.link root aux;
              root
            )
         | _,_ -> aux in
       let confl = VeritSyntax.get_clause !confl_num in
       SmtTrace.select confl;
       (* Trace.share_prefix first (2 * last.id); *)
       occur confl;
       print_certif first "/tmp/certif.log";
       (alloc first, confl)
    | Parsing.Parse_error -> failwith ("Verit.import_trace: parsing error line " ^ (string_of_int !line))

and print_certif c where=
  let r = ref c in
  let out_channel = open_out where in
  let continue = ref true in
  while !continue do
    let kind = to_string (!r.kind) in
    let id = !r.id in
    let pos = match !r.pos with
      | None -> "None"
      | Some p -> string_of_int p in
    Printf.fprintf out_channel "id:%i kind:%s pos:%s\n" id kind pos;
    flush out_channel;
    match !r.next with
    | None -> continue := false
    | Some n -> r := n 
  done


let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace fproof None in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace (import_all fsmt fproof)
let theorem name fsmt fproof = SmtCommands.theorem name (import_all fsmt fproof)
let checker fsmt fproof = SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export out_channel rt ro l ls_stmc =
  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic UFLIA)@.";


  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    VeritSyntax.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (Btype.to_list rt);

  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    VeritSyntax.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; Btype.to_smt fmt t) dom;
    Format.fprintf fmt ") ";
    Btype.to_smt fmt cod;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);


  Format.fprintf fmt "(assert ";
  Form.to_smt Atom.to_smt fmt l;
  Format.fprintf fmt ")\n";

  List.iter (fun u -> Format.fprintf fmt "(assert ";
                      Atom.to_smt fmt u;
                      Format.fprintf fmt ")\n"
    ) ls_stmc;

  (* Format.fprintf fmt "(assert (forall ((x Int) (y Int)) (= (op_0 x) (op_0 y))))\n"; *)
  Format.fprintf fmt "(check-sat)\n";
  Format.fprintf fmt "(exit)@."

(* val call_verit : Btype.reify_tbl -> Op.reify_tbl -> Form.t -> (Form.t clause * Form.t) -> (int * Form.t clause) *)
let call_verit rt ro fl root ls_smtc =
  let filename, outchan = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro fl ls_smtc;
  close_out outchan;
  let logfilename = Filename.chop_extension filename ^ ".vtlog" in
  let wname, woc = Filename.open_temp_file "warnings_verit" ".log" in
  close_out woc;
  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=" ^ logfilename ^ " " ^ filename ^ " 2> " ^ wname in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);
  let win = open_in wname in
  try let _ = input_line win in
      close_in win; Sys.remove wname;
      Structures.error "veriT returns 'unknown'"
  with End_of_file -> 
  close_in win; Sys.remove wname;
  if exit_code <> 0 then
    failwith ("Verit.call_verit: command " ^ command ^
	        " exited with code " ^ string_of_int exit_code);
  try
    import_trace logfilename (Some root)
  with
  | VeritSyntax.Sat -> Structures.error "veriT found a counter-example"


let tactic lpl =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  SmtCommands.tactic call_verit rt ro ra rf lpl
