Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Parameter h : Z -> Z -> Z.
Axiom h_Sm_n : forall x y, Zeq_bool (h (x+1) y) (h x y).

Lemma sym_zeq_bool x y :
  Zeq_bool x y <-> Zeq_bool y x.

Proof.
  unfold is_true. rewrite <- ? Zeq_is_eq_bool.
  split; intro H; now rewrite H.
Qed.  

Lemma h_1_0 :
  Zeq_bool (h 1 0) (h 0 0).

Proof.
  verit h_Sm_n.
  rewrite sym_zeq_bool. auto.
Qed.
