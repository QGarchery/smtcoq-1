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


Require Export Int63 List PArray.
Require Export SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.

Declare ML Module "smtcoq_plugin".

Require Import Bool.
Open Scope Z_scope.

Lemma impl_split a b:
  implb a b = true -> orb (negb a) b = true.
Proof.
  destruct a; destruct b; intuition.
Qed.

Hint Resolve impl_split.


Lemma impl_or_split_right A B C:
  implb (A || B) C -> negb B || C.
Proof.
  destruct A; destruct B; destruct C; intuition.
Qed.

Lemma impl_or_split_left A B C:
  implb (A || B) C -> negb A || C.
Proof.
  destruct A; destruct B; destruct C; intuition.
Qed.

Ltac vauto :=
  try (let H := fresh "H" in
       intro H; try (rewrite Z.eqb_sym; apply H);
       match goal with
       | [ |- is_true (negb ?A || ?B) ] => try (eapply impl_or_split_right; apply H);
                                           eapply impl_or_split_left; apply H
       end;
       apply H);
  auto.

Ltac verit :=
  verit_base; vauto.
    
