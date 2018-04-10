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
       print first;
       SmtTrace.select confl;
       (* Trace.share_prefix first (2 * last.id); *)

       occur confl;
       (alloc first, confl)
    | Parsing.Parse_error -> failwith ("Verit.import_trace: parsing error line "^(string_of_int !line))

and print c =
  let r = ref c in
  let out_channel = open_out "/tmp/debug.log" in
  while !r.next <> None do
    Printf.fprintf out_channel "%s\n" (to_string (!r.kind));
    flush out_channel;
    r := get_val (!r.next)
  done;
  Printf.fprintf out_channel "%s\n" (to_string (!r.kind));
  flush out_channel;
  close_out out_channel

and get_val = function
    Some a -> a
  | None -> assert false
  
            

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

let export out_channel rt ro l =
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
  Format.fprintf fmt "(assert (forall ((x Int) (y Int)) (= (op_0 x) (op_0 y))))\n";
  Format.fprintf fmt "(check-sat)\n";
  Format.fprintf fmt "(exit)@."

(* val call_verit : Btype.reify_tbl -> Op.reify_tbl -> Form.t -> (Form.t clause * Form.t) -> (int * Form.t clause) *)
let call_verit rt ro fl root =
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro fl;
  close_out outchan;
  let logfilename = (Filename.chop_extension filename)^".vtlog" in

  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof="^logfilename^" "^filename in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);
  if exit_code <> 0 then
    failwith ("Verit.call_verit: command "^command^
	      " exited with code "^(string_of_int exit_code));
  try
    import_trace logfilename (Some root)
  with
    | VeritSyntax.Sat -> Structures.error "veriT can't prove this"


let tactic () =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  SmtCommands.tactic call_verit rt ro ra rf
