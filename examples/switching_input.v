Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Parameter m : Z -> Z.
Axiom m_0 : Zeq_bool (m 0) 5.

Lemma cinq_m_0 :
  Zeq_bool (m 0) 5.

Proof.
  verit m_0.
