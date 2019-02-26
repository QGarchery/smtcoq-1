(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Local Open Scope Z_scope.

Ltac intro_lemma :=
  repeat match goal with
    | [ |- (?X -> _) -> _ ] => match type of X with
                               | Set => intro SET
                               | Prop =>  intro PROP end
  end.


(* Goal forall *)
(*     (x: Z) *)
(*     (f: Z -> Z), *)
(*     (forall x, f (x + 1) = f x + 1) -> f (x + 2) = f x + 2. *)
(* Proof. *)
(*   introduce. *)
(*   intros x f. *)
(*   intro_lemma. *)
(*   prop2bool. *)
(*   verit. *)
(* Qed. *)


(* Lemma simple_apply1 : *)
(*   forall (x y: Z) (f: Z -> Z), *)
(*     (f x = f y -> f (x+1) = f y - 1) -> f x = f y -> f y = f (x+1) + 1. *)
(* Proof. *)
(*   intros x y f. *)
(*   intro_lemma. *)
(*   prop2bool. *)

(* Goal forall *)
(*     (x y: Z) *)
(*     (f: Z -> Z), *)
(*     f x = f y + 1 -> f y = f x - 1. *)
(*   prop2bool. *)
(*   intros x y f. *)
(* intro_lemma. *)

(* Lemma calc_lin1 : *)
(*   forall (f : Z -> Z), *)
(*     f 0 = 0 -> (forall x, f (x+1) = f x + 1) -> f 3 = 3. *)
(* Proof. *)
(*   introduce. *)

Lemma calc_lin2 :
  forall (f : Z -> Z),
    (forall x, f (x+1) = f x + 1) -> f 0 = 0 -> f 3 = 3.
Proof.
  intro f.
  assert (H :(forall x : Z, f (x + 1) = f x + 1) <-> (forall x : Z, f (x+1) =? f x + 1)).
  -split.
   +intros. rewrite H. apply Z.eqb_refl.
   +intros. prop2bool. apply H.
  -rewrite H. prop2bool.
   verit_bool_base H0; vauto.
Qed.

(* Lemma simple_apply1 : *)
(*   forall (x y: Z) (f: Z -> Z), *)
(*     (f x = f y -> f (x+1) = f y - 1) -> f x = f y -> f y = f (x+1) + 1. *)
(* Proof. *)
(*   prop2bool. *)

(* Lemma simple_apply2 : *)
(*   forall (x y: Z) (f: Z -> Z), *)
(*     f x = f y -> (f x = f y -> f (x+1) = f y - 1) -> f y = f (x+1) + 1. *)
(* Proof. *)
(*   prop2bool. *)


Lemma nat_convert_bug x :
  (3 + x =? x + 3) %nat.
Proof.

  fold nat_convert_type.add nat_convert_type.eqb.
  nat_convert_mod.converting.
  nat_convert_mod.rewriting.
  nat_convert_mod.renaming.
  nat_convert_mod.renaming'.
  repeat match goal with
         | |- context C[nat_convert_type.inT ?X] =>
           let inT_unfold := eval red in (nat_convert_type.inT X) in
               change (nat_convert_type.inT X) with inT_unfold
         | |- context C[nat_convert_type.T2Z ?X] =>
           let T2Z_calc := eval compute in (nat_convert_type.T2Z X) in
               change (nat_convert_type.T2Z X) with T2Z_calc end.
  verit.
Qed.

Import nat_convert_type nat_convert_mod.

Lemma destruct_existT A P x p v:
  v = @existT A P x p -> P x.
auto. Qed.

Lemma alt_convert x :
  (x =? x + 3) %nat.
Proof.
  fold add eqb.
  let v := conv false false (add x 3)%nat in
  pose v as u.
  unfold Equal_by in u.
  case_eq u. intros. unfold u in H.
  inversion H. rewrite e, <- H1.




(*   converting. *)



Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.


(* Examples that check ZChaff certificates *)

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.

Zchaff_Checker "hole4.cnf" "hole4.log".


(* Example that checks a VeriT certificate, for logic QF_UFLIA *)

Section Verit.
  Verit_Checker "lia.smt2" "lia.vtlog".
End Verit.


(* Example that checks a LFSC certificate, for logic QF_UFLIA *)

Section Lfsc.
  Lfsc_Checker "lia.smt2" "lia.lfsc".
End Lfsc.


(* Examples of the zchaff tactic (requires zchaff in your PATH
   environment variable):
   - with booleans
   - with concrete terms *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := (i == j)%int in
  let b := (j == k)%int in
  let c := (k == i)%int in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.


(* Examples of the verit tactics (requires verit in your PATH environment
   variable), which handle
   - propositional logic
   - theory of equality
   - linear integer arithmetic *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit_bool.
Qed.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit_bool.
Qed.

Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  verit_bool.
Qed.



Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  verit.
Qed.


(* Examples of the smt tactic (requires verit and cvc4 in your PATH environment
   variable):
   - propositional logic
   - theory of equality
   - linear integer arithmetic
   - theory of fixed-sized bit-vectors
   - theory of arrays *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  smt.
Qed.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  smt.
Qed.
Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  smt.
Qed.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  smt.
Qed.

Goal forall (bv1 bv2 bv3: bitvector 4),
    bv1 = #b|0|0|0|0|  /\
    bv2 = #b|1|0|0|0|  /\
    bv3 = #b|1|1|0|0|  ->
    bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
Proof.
  smt.
Qed.

(* Goal forall (a b c d: farray Z Z), *)
(*     b[0 <- 4] = c  -> *)
(*     d = b[0 <- 4][1 <- 4]  -> *)
(*     a = d[1 <- b[1]]  -> *)
(*     a = c. *)
(* Proof. *)
(*   smt. *)
(* Qed. *)

Goal forall (a b: farray Z Z) (v w x y z t: Z)
            (r s: bitvector 4)
            (f: Z -> Z)
            (g: farray Z Z -> Z)
            (h: bitvector 4 -> Z),
    a[x <- v] = b /\ a[y <- w] = b ->
    a[z <- w] = b /\ a[t <- v] = b ->
    r = s -> v < x + 10 /\ v > x - 5 ->
    ~ (g a = g b) \/ f (h r) = f (h s).
Proof.
  smt.
Qed.


(* Examples of using the conversion tactics *)

Local Open Scope positive_scope.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof.
pos_convert.
verit.
Qed.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((3 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof.
pos_convert.
verit.
Qed.

Local Close Scope positive_scope.

Local Open Scope N_scope.

Goal forall (f : N -> N) (x y : N),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof.
N_convert.
verit.
Qed.

Goal forall (f : N -> N) (x y : N),
  implb ((x + 3) =? y)
        ((2 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof.
N_convert.
verit.
Qed.

Local Close Scope N_scope.

Require Import NPeano.
Local Open Scope nat_scope.

Goal forall (f : nat -> nat) (x y : nat),
  implb (Nat.eqb (x + 3) y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof.
nat_convert.
verit.
Qed.

Goal forall (f : nat -> nat) (x y : nat),
  implb (Nat.eqb (x + 3) y)
        ((2 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof.
nat_convert.
verit.
Qed.

Local Close Scope nat_scope.

(* An example with all 3 types and a binary function *)
Goal forall f : positive -> nat -> N, forall (x : positive) (y : nat),
  implb (x =? 3)%positive
    (implb (Nat.eqb y 7)
      (implb (f 3%positive 7%nat =? 12)%N
        (f x y =? 12)%N)) = true.
pos_convert.
nat_convert.
N_convert.
verit.
Qed.

Open Scope Z_scope.

(* Some examples of using verit with lemmas. Use <verit_base H1 .. Hn; vauto>
   to temporarily add the lemmas H1 .. Hn to the verit environment. *)
Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof.
  intros f Hf.
  verit_bool_base Hf; vauto.
Qed.

Section Without_lemmas.
  Lemma fSS:
    forall (f : Z -> Z) (k : Z) (x : Z),
      implb (f (x+1) =? f x + k)
     (implb (f (x+2) =? f (x+1) + k)
            (f (x+2) =? f x + 2 * k)).
  Proof. verit. Qed.
End Without_lemmas.

Section With_lemmas.
  Variable f : Z -> Z.
  Variable k : Z.
  Hypothesis f_k_linear : forall x, f (x + 1) =? f x + k.

  Lemma fSS2:
    forall x, f (x + 2) =? f x + 2 * k.
  Proof. verit_bool_base f_k_linear; vauto. Qed.
End With_lemmas.

(* You can use <Add_lemmas H1 .. Hn> to permanently add the lemmas H1 .. Hn to
   the environment. If you did so in a section then, at the end of the section,
   you should use <Clear_lemmas> to empty the globally added lemmas because
   those lemmas won't be available outside of the section. *)
Section mult3.
  Variable mult3 : Z -> Z.
  Hypothesis mult3_0 : mult3 0 =? 0.
  Hypothesis mult3_Sn : forall n, mult3 (n+1) =? mult3 n + 3.
  Add_lemmas mult3_0 mult3_Sn.

  Lemma mult3_21 : mult3 4 =? 12.
  Proof. verit. Qed.

  Clear_lemmas.
End mult3.

Section NonLinear.
  Lemma distr_right_inst a b (mult : Z -> Z -> Z) :
    (forall x y z, mult (x + y)  z =? mult x z + mult y z) ->
    (mult (3 + a) b =? mult 3 b + mult a b).
  Proof.
    intro H.
    verit_bool_base H; vauto.
  Qed.
End NonLinear.

Section group.
  Variable op : Z -> Z -> Z.
  Variable inv : Z -> Z.
  Variable e : Z.

  Hypothesis associative :
    forall a b c : Z, op a (op b c) =? op (op a b) c.
  Hypothesis inverse :
    forall a : Z, (op (inv a) a =? e).
  Hypothesis identity :
    forall a : Z, (op e a =? a).
  Add_lemmas associative identity inverse.
  Lemma inverse' :
    forall a : Z, (op a (inv a) =? e).
  Proof. verit. Qed.
  Add_lemmas inverse'.
  Lemma identity' :
    forall a : Z, (op a e =? a).
  Proof. verit. Qed.
  Add_lemmas identity'.

  Lemma unique_identity e':
    (forall z, op e' z =? z) -> e' =? e.
  Proof. intros pe'. verit_bool_base pe'; vauto. Qed.
  Lemma simplification_right x1 x2 y:
      op x1 y =? op x2 y -> x1 =? x2.
  Proof. intro H. verit_bool_base H; vauto. Qed.

  Lemma simplification_left x1 x2 y:
      op y x1 =? op y x2 -> x1 =? x2.
  Proof. intro H. verit_bool_base H; vauto. Qed.

  Clear_lemmas.
End group.
