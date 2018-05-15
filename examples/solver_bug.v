Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Parameter f : Z -> Z.

Axiom f_spec : forall x, andb (Zeq_bool (f (x+1)) (f x + 1)) (Zeq_bool (f 0) 0).

Lemma f_1 : Zeq_bool (f 1) 1.

Proof.  
  verit f_spec.




