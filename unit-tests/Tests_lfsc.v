Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.

Section Arrays.
  Local Close Scope int63_scope.

  Require Import FArray.
  (* Existing Instance Typ.Z_ord. *)
  (* Existing Instance Typ.Z_dec. *)
  (* Existing Instance Typ.Z_comp. *)
  (* Existing Instance Typ.Z_inh. *)

  
  Goal forall (a b c d: farray Z Z),
      (implb (equal c (store b 0 4))
      (implb (equal d (store (store b 0 4) 1 4))
      (implb (equal a (store d 1 (select b 1)))
      (equal a c)))).
  Proof.
    cvc4.
    Qed.
  Admitted.

  
  Goal forall (a b: farray Z Z) i,
        (Z.eqb (select (store (store (store a i 3) 1 (select (store b i 4) i)) 2 2) 1) 4).
  Proof.
    intros.
    cvc4.
    simpl.
  Qed.


  
End Arrays.

Section BV.

  Require Import BVList.
  Import BITVECTOR_LIST.

  Goal forall (a b c: bitvector 4), implb
                                 (bv_eq c (bv_and a b))
                                 (bv_eq (bv_and (bv_and a c) b) c).
  Proof.
    cvc4.
  Qed.
  
End BV.


  
(* CVC4 tactic *)

(* Simple connectors *)

Goal forall (a:bool), a || negb a.
  cvc4.
Qed.


Goal forall a, negb (a || negb a) = false.
  cvc4.
Qed.

Goal forall a, (a && negb a) = false.
  cvc4.
Qed.

Goal forall a, negb (a && negb a).
  cvc4.
Qed.

Goal forall a, implb a a.
  cvc4.
Qed.

Goal forall a, negb (implb a a) = false.
  cvc4.
Qed.

(* *)
(* Goal forall a , (xorb a a) || negb (xorb a a). *)
(*   cvc4. *)
(* Qed. *)

                                    
(* Goal forall a, (a||negb a) || negb (a||negb a). *)
(*   cvc4. *)
(* Qed. *)
(* Print Unnamed_thm5. *)
(* *)

(* Polarities *)

Goal forall a b, andb (orb (negb (negb a)) b) (negb (orb a b)) = false.
Proof.
  cvc4.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  cvc4.
Qed.



(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof.
  cvc4.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4.
Qed.


 
(* *)
(* Goal true. *)
(*   cvc4. *)
(* Qed. *)

                                    
(* Goal negb false. *)
(*   cvc4. *)
(* Qed. *)


 
(* Goal forall a, Bool.eqb a a. *)
(* Proof. *)
(*   cvc4. *)
(* Qed. *)

 
(* Goal forall (a:bool), a = a. *)
(*   cvc4. *)
(* Qed. *)


(* (* Other connectors *) *)

(* Goal (false || true) && false = false. *)
(* Proof. *)
(*   cvc4. *)
(* Qed. *)


(* Goal negb true = false. *)
(* Proof. *)
(*   cvc4. *)
(* Qed. *)


(* Goal false = false. *)
(* Proof. *)
(*   cvc4. *)
(* Qed. *)


(* Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)). *)
(* Proof. *)
(*   cvc4. *)
(* Qed. *)
(* *)

Goal forall x y, Bool.eqb (implb x y) ((x && y) || (negb x)).
Proof.
  cvc4.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof.
  cvc4.
Qed.


(* sat2.smt *)
(* ((a ∧ b) ∨ (b ∧ c)) ∧ ¬b = ⊥ *)

Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof.
  cvc4.
Qed.


(* sat3.smt *)
(* (a ∨ a) ∧ ¬a = ⊥ *)

Goal forall a, ((a || a) && (negb a)) = false.
Proof.
  cvc4.
Qed.


(* sat4.smt *)
(* ¬(a ∨ ¬a) = ⊥ *)

Goal forall a, (negb (a || (negb a))) = false.
Proof.
  cvc4.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4.
Qed.


(* Le même, mais où a, b et c sont des termes concrets *)

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4.
Qed.


(* sat6.smt *)
(* (a ∧ b) ∧ (c ∨ d) ∧ ¬(c ∨ (a ∧ b ∧ d)) = ⊥ *)

Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof.
  cvc4.
Qed.


(* sat7.smt *)
(* a ∧ b ∧ c ∧ (¬a ∨ ¬b ∨ d) ∧ (¬d ∨ ¬c) = ⊥ *)

Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof.
  cvc4.
Qed.


(* Pigeon hole: 4 holes, 5 pigeons *)

Goal forall x11 x12 x13 x14 x15 x21 x22 x23 x24 x25 x31 x32 x33 x34 x35 x41 x42 x43 x44 x45, (
  (orb (negb x11) (negb x21)) &&
  (orb (negb x11) (negb x31)) &&
  (orb (negb x11) (negb x41)) &&
  (orb (negb x21) (negb x31)) &&
  (orb (negb x21) (negb x41)) &&
  (orb (negb x31) (negb x41)) &&

  (orb (negb x12) (negb x22)) &&
  (orb (negb x12) (negb x32)) &&
  (orb (negb x12) (negb x42)) &&
  (orb (negb x22) (negb x32)) &&
  (orb (negb x22) (negb x42)) &&
  (orb (negb x32) (negb x42)) &&

  (orb (negb x13) (negb x23)) &&
  (orb (negb x13) (negb x33)) &&
  (orb (negb x13) (negb x43)) &&
  (orb (negb x23) (negb x33)) &&
  (orb (negb x23) (negb x43)) &&
  (orb (negb x33) (negb x43)) &&

  (orb (negb x14) (negb x24)) &&
  (orb (negb x14) (negb x34)) &&
  (orb (negb x14) (negb x44)) &&
  (orb (negb x24) (negb x34)) &&
  (orb (negb x24) (negb x44)) &&
  (orb (negb x34) (negb x44)) &&

  (orb (negb x15) (negb x25)) &&
  (orb (negb x15) (negb x35)) &&
  (orb (negb x15) (negb x45)) &&
  (orb (negb x25) (negb x35)) &&
  (orb (negb x25) (negb x45)) &&
  (orb (negb x35) (negb x45)) &&


  (orb (negb x11) (negb x12)) &&
  (orb (negb x11) (negb x13)) &&
  (orb (negb x11) (negb x14)) &&
  (orb (negb x11) (negb x15)) &&
  (orb (negb x12) (negb x13)) &&
  (orb (negb x12) (negb x14)) &&
  (orb (negb x12) (negb x15)) &&
  (orb (negb x13) (negb x14)) &&
  (orb (negb x13) (negb x15)) &&
  (orb (negb x14) (negb x15)) &&

  (orb (negb x21) (negb x22)) &&
  (orb (negb x21) (negb x23)) &&
  (orb (negb x21) (negb x24)) &&
  (orb (negb x21) (negb x25)) &&
  (orb (negb x22) (negb x23)) &&
  (orb (negb x22) (negb x24)) &&
  (orb (negb x22) (negb x25)) &&
  (orb (negb x23) (negb x24)) &&
  (orb (negb x23) (negb x25)) &&
  (orb (negb x24) (negb x25)) &&

  (orb (negb x31) (negb x32)) &&
  (orb (negb x31) (negb x33)) &&
  (orb (negb x31) (negb x34)) &&
  (orb (negb x31) (negb x35)) &&
  (orb (negb x32) (negb x33)) &&
  (orb (negb x32) (negb x34)) &&
  (orb (negb x32) (negb x35)) &&
  (orb (negb x33) (negb x34)) &&
  (orb (negb x33) (negb x35)) &&
  (orb (negb x34) (negb x35)) &&

  (orb (negb x41) (negb x42)) &&
  (orb (negb x41) (negb x43)) &&
  (orb (negb x41) (negb x44)) &&
  (orb (negb x41) (negb x45)) &&
  (orb (negb x42) (negb x43)) &&
  (orb (negb x42) (negb x44)) &&
  (orb (negb x42) (negb x45)) &&
  (orb (negb x43) (negb x44)) &&
  (orb (negb x43) (negb x45)) &&
  (orb (negb x44) (negb x45)) &&


  (orb (orb (orb x11 x21) x31) x41) &&
  (orb (orb (orb x12 x22) x32) x42) &&
  (orb (orb (orb x13 x23) x33) x43) &&
  (orb (orb (orb x14 x24) x34) x44) &&
  (orb (orb (orb x15 x25) x35) x45)) = false.
Proof.
  cvc4.
Qed.


(* uf1.smt *)

Goal forall a b c f p, ((Z.eqb a c) && (Z.eqb b c) && ((negb (Z.eqb (f a) (f b))) || ((p a) && (negb (p b))))) = false.
Proof.
  cvc4.
Qed.


(* uf2.smt *)

Goal forall a b c (p : Z -> bool), ((((p a) && (p b)) || ((p b) && (p c))) && (negb (p b))) = false.
Proof.
  cvc4.
Qed.


(* uf3.smt *)

Goal forall x y z f, ((Z.eqb x y) && (Z.eqb y z) && (negb (Z.eqb (f x) (f z)))) = false.
Proof.
  cvc4.
Qed.


(* uf4.smt *)

Goal forall x y z f, ((negb (Z.eqb (f x) (f y))) && (Z.eqb y z) && (Z.eqb (f x) (f (f z))) && (Z.eqb x y)) = false.
Proof.
  cvc4.
Qed.


(* uf5.smt *)

Goal forall a b c d e f, ((Z.eqb a b) && (Z.eqb b c) && (Z.eqb c d) && (Z.eqb c e) && (Z.eqb e f) && (negb (Z.eqb a f))) = false.
Proof.
  cvc4.
Qed.


(* lia1.smt *)


(* lia1.smt *)

Theorem lia1: forall x y z, implb ((x <=? 3) && ((y <=? 7) || (z <=? 9)))
  ((x + y <=? 10) || (x + z <=? 12)) = true.
Proof.
  intros.
  cvc4.
  verit.
Qed.

Print Assumptions lia1.

(* lia2.smt *)

Theorem lia2: forall x, implb (Z.eqb (x - 3) 7) (x >=? 10) = true.
Proof.
  intros.
  cvc4.
  verit.
Qed.


(* lia3.smt *)

Theorem lia3: forall x y, implb (x >? y) (y + 1 <=? x) = true.
Proof.
  intros.
  cvc4.
  verit.
Qed.


(* lia4.smt *)

Theorem lia4: forall x y, Bool.eqb (x <? y) (x <=? y - 1) = true.
Proof.
  intros.
  cvc4; verit.
Admitted.


(* lia5.smt *)
(* cvc4 crashes *)
(* Theorem lia5: forall x y, ((x + y <=? - (3)) && (y >=? 0) *)
(*         || (x <=? - (3))) && (x >=? 0) = false. *)
(* Proof. *)
(*   cvc4. *)
(* Admitted. *)

(* Print Assumptions lia5. *)


(* lia6.smt *)

Theorem lia6: forall x, implb (andb ((x - 3) <=? 7) (7 <=? (x - 3))) (x >=? 10) = true.
Proof.
  intros.
  cvc4; verit.
Qed.

(* lia7.smt *)

Theorem lia7: forall x, implb (Z.eqb (x - 3) 7) (10 <=? x) = true.
Proof.
  intros.
  cvc4; verit.
Qed.


(* More general examples *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  cvc4.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  cvc4.
Qed.


Theorem lia8: forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
    (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  intros.
  cvc4; verit.
Admitted.


(* With let ... in ... *)

Goal forall b,
  let a := b in
  a && (negb a) = false.
Proof.
  cvc4.
Qed.

Goal forall b,
  let a := b in
  a || (negb a) = true.
Proof.
  cvc4.
Qed.
(* Does not work since the [is_true] coercion includes [let in]
Goal forall b,
  let a := b in
  a || (negb a).
Proof.
  cvc4.
Qed.
*)

(* With concrete terms *)

Goal forall i j,
  let a := i == j in
  a && (negb a) = false.
Proof.
  cvc4.
Qed.

Goal forall i j,
  let a := i == j in
  a || (negb a) = true.
Proof.
  cvc4.
Qed.

Section Concret.
  Theorem c1: forall i j,
    (i == j) && (negb (i == j)) = false.
  Proof.
    cvc4.
  Admitted.
  Print Assumptions c1.

  
End Concret.

Section Concret2.
  Lemma concret : forall i j, (i == j) || (negb (i == j)).
  Proof.
    cvc4.
    econstructor; eexact Int63Properties.reflect_eqb.
    apply 0.
    exists Int63Native.ltb.
    intros x y z; rewrite !Int63Axioms.ltb_spec; apply Z.lt_trans.
    intros x y; rewrite !Int63Axioms.ltb_spec, <- Int63Properties.to_Z_eq.
    apply Z.lt_neq.
    intros.
    destruct eq0 as (eq0, r0), ltb0 as (ltb, ltb_trans, ltb_neq); simpl.
    (* destruct (Typ.Z_comp). *)
    (* unfold FArray.lt in compare. *)
    (* destruct (Typ.Z_ord). *)
    (* destruct (compare [|x|] [|y|]). *)

    case_eq (Int63Native.ltb x y); intro.
    
    case_eq (Int63Op.compare x y); rewrite Int63Properties.compare_spec; intro.
    - apply OrderedType.EQ.
      apply (reflect_iff _ _ (r0 x y)).
      apply Int63Properties.to_Z_eq.
      apply Z.compare_eq; trivial.
    - apply OrderedType.LT.
Admitted.
  Check concret.
  Print Assumptions concret.
End Concret2.
Check concret.



(* Congruence in which some premices are REFL *)

Goal forall (f:Z -> Z -> Z) x y z,
  implb (Z.eqb x y) (Z.eqb (f z x) (f z y)).
Proof.
  cvc4.
Qed.

Goal forall (P:Z -> Z -> bool) x y z,
  implb (Z.eqb x y) (implb (P z x) (P z y)).
Proof.
  cvc4.
Qed.

