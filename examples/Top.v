Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Parameter f : Z -> Z.
Axiom f1 : andb (Zeq_bool (f 1) 3) (Zeq_bool (f 2) 4).

Lemma f1f2 :
  Zeq_bool (f 1) 3.

Proof.
  assert (G : Zeq_bool (f 1) 3).
  assert (H := f1). apply andb_true_iff in H.
  intuition.
  verit G.
Qed.  

  