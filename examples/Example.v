(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Lemma calling_verit :
  forall f, forall y, 
      Zeq_bool (f 2%Z) (f y).

Proof.  
  verit.
  

  
(* Examples that check ZChaff certificates *)

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.

Lemma sat2:
  forall v : int -> bool,
    (v 1 || v 2 || v 3) &&
    (negb (v 1) || negb (v 2) || negb (v 3)) &&
    (negb (v 1) || v 2) &&
    (negb (v 2) || v 3) &&
    (negb (v 3) || v 1)  = false.
Proof.
  zchaff.
Qed.

Zchaff_Checker "hole4.cnf" "hole4.log".

(* Example that checks a VeriT certificate, for logic QF_UF *)

Section Verit.
  Verit_Checker "euf.smt2" "euf.log".
End Verit.

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
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.

(* About positive. *)
(* Print N. *)

(* About Z. *)
(* Print Z. *)
(* Check (-5)%Z. *)
(* Check 5%N. *)

(* Print eq. *)

(* Set Printing All. *)

(* Print Zeq_bool. *)
(* Print Z.compare. *)

(* SearchAbout Zeq_bool. *)
(* About Zeq_bool. *)
(* Print Zeq_bool. *)


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).

Proof.
  intros.
  destruct_with_eqn (P (f a)).
  destruct_with_eqn (Zeq_bool (f a) b).
  +apply orb_true_iff. right.
   rewrite <- Zeq_is_eq_bool in Heqb1.
   now rewrite Heqb1 in Heqb0.
  +auto.
  +apply orb_true_iff; left; apply orb_true_iff; right; now simpl.
   (* verit. *)
Qed.

Definition Myeqbool : Z -> Z -> bool := Zeq_bool.
Print Zeq_bool.


Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Zeq_bool (2*x1+1) (2*x2+1)) (Zeq_bool (2*x1+1) (2*x2)))
    (ifb b2 (Zeq_bool (2*x1) (2*x2+1)) (Zeq_bool (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Zeq_bool x1 x2)).

Proof.
  verit.
Qed.

(* Parameter toto : Z -> Z. *)
(* Variable toto : Z. *)

Section S.
  Variable f : Z -> Z.
  Hypothesis th : forall x, Zeq_bool (f x) 3.
  Definition g z := f z.
  (* Add Theorem th. *)
  (* Goal forall x, Zeq_bool ((f x) + 1) 4. *)
    (* verit. *)
End S.

Check g.
Definition g1 (f : Z -> Z) (x : Z) := f x.

Lemma comp f g (x1 x2 x3 : Z) :
  ifb (Zeq_bool x1 (f x2))
      (ifb (Zeq_bool x2 (g x3))
           (Zeq_bool x1 (f (g x3)))
           true)
      true.
Proof.
  verit.
Qed.


Lemma irrelf_ltb :
  forall a b c,
  (Z.ltb a b) &&
  (Z.ltb b c) &&
  (Z.ltb c a) = false.

Proof.
  verit.
Qed.

Lemma un_menteur (a b c d : Z) dit:
  negb ((Zeq_bool (dit a) c) &&
        (Zeq_bool (dit b) d) &&
        (Zeq_bool a d || Zeq_bool b c) &&
        (Zeq_bool a c || Zeq_bool a d) &&
        (Zeq_bool b c || Zeq_bool b d)) ||
        (Zeq_bool a d) = true.

Proof.
  verit.
Qed.

Lemma un_menteur_prop (a b c d : Z) dit:
  (dit a = c) ->
  (dit b = d) ->
  (a = d \/ b = c) ->
  (a = c \/ a = d) ->
  (b = c \/ b = d) ->
  a = d.

Proof.
  intros.
  intuition.
  rewrite <- H1 in H4.
  rewrite H4 in H0.
  rewrite H0 in H.
  intuition.
Qed.


Lemma sat2_gen a1 a2 a3:
  forall v : int -> bool,
    (v a1 || v a2 || v a3) &&
    (negb (v a1) || negb (v a2) || negb (v a3)) &&
    (negb (v a1) || v a2) &&
    (negb (v a2) || v a3) &&
    (negb (v a3) || v a1)  = false.

Proof.
  verit.
  exists Int63Native.eqb.
  intros x y.
  apply Int63Properties.reflect_eqb.
Defined.

Print sat2_gen.
Check checker_b_correct.



