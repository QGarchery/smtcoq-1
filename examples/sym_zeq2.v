Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Lemma sym_zeq_bool x y :
  Zeq_bool x y = Zeq_bool y x.

Proof.
  case_eq (Zeq_bool x y).
  rewrite <- Zeq_is_eq_bool. intro H. symmetry. now rewrite <- Zeq_is_eq_bool.
  symmetry. apply not_true_is_false.
  intro H1. rewrite <- Zeq_is_eq_bool in H1.
  symmetry in H1. rewrite Zeq_is_eq_bool in H1.
  rewrite H in H1. discriminate H1.
Qed.

Parameter f : Z -> Z.
Axiom f1 : orb (Zeq_bool (f 1) (f 2)) (Zeq_bool (f 1) 3).

Lemma f23_f13 :
  implb (Zeq_bool (f 2) 3) (Zeq_bool (f 1) 3).
Proof.
  verit f1.
Qed.

  