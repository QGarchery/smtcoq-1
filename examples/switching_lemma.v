Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Parameter h : Z -> Z -> Z.
Axiom h_Sm_n : forall x y, Zeq_bool (h (x+1) y) (h x y).

Lemma h_1_0 :
  Zeq_bool (h 1 0) (h 0 0).

Proof.
  verit h_Sm_n.
  intro H. unfold is_true. rewrite <- Zeq_is_eq_bool.
  symmetry. rewrite Zeq_is_eq_bool.
  apply H.
Qed.
