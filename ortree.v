Require Import Bool.

Inductive OrTree :=
  Bool (b : bool)
| Or (left: OrTree) (right: OrTree).

Inductive Interp : OrTree -> Prop :=
  InterpBool :
    Interp (Bool true) 
| InterpOrLeft t1 t2 :
    Interp t1 -> Interp (Or t1 t2) 
| InterpOrRight t1 t2 :
    Interp t2 -> Interp (Or t1 t2).

Definition t :=
  Or (Or (Bool false) (Bool true)) (Or (Bool false) (Bool false)).

Lemma Interp_t : Interp t.
Proof.
  apply InterpOrLeft.
  apply InterpOrRight.
  apply InterpBool.
Qed.

Fixpoint interp (t : OrTree) :=
  match t with
    Bool b => b
  | Or t1 t2 => interp t1 || interp t2
  end.

Proposition Interp_equiv_interp t :
  Interp t <-> interp t = true.

Proof.
  induction t as [a | t1 IHt1 t2 IHt2]; simpl.
  -split; intro H.
   +now inversion H.
   +rewrite H. apply InterpBool.
  -split; intro H.
   +inversion H.
    now apply IHt1 in H1; rewrite H1.
    apply IHt2 in H1; rewrite H1. apply orb_true_r.
   +apply orb_true_iff in H. destruct H.
    now apply InterpOrLeft, IHt1.
    now apply InterpOrRight, IHt2. 
Qed.

Lemma interp_t : interp t = true.
Proof.
  reflexivity.
Qed.

Fixpoint append t1 t2 :=
  match t1 with
  | Bool _ => Or t1 t2
  | Or t11 t12 => Or t11 (append t12 t2)
  end.

Fixpoint peigne (t : OrTree) :=
  match t with
  | Bool n => t
  | Or t1 t2 => let pt1 := peigne t1 in
                  let pt2 := peigne t2 in
                  append pt1 pt2
  end.

Inductive eqt : OrTree -> OrTree -> Prop :=
  refl t: eqt t t
| sym t1 t2: eqt t1 t2 -> eqt t2 t1
| assoc t1 t2 t3: eqt (Or t1 (Or t2 t3)) (Or (Or t1 t2) t3)
| congru ta1 ta2 tb1 tb2: eqt ta1 tb1 -> eqt ta2 tb2 ->
                             eqt (Or ta1 ta2) (Or tb1 tb2)
| trans t1 t2 t3: eqt t1 t2 -> eqt t2 t3 -> eqt t1 t3.

Lemma eqt_correct t1 t2:
  eqt t1 t2 -> interp t1 = interp t2.
Proof.
  intro eq12. induction eq12; simpl.
  -reflexivity.
  -auto.
  -apply orb_assoc.
  -now rewrite IHeq12_1, IHeq12_2.
  -now rewrite IHeq12_1.
Qed.

Lemma append_eqt t1 t2:
  eqt (append t1 t2) (Or t1 t2).
Proof.
  revert t2. induction t1; intro t2; simpl.
  -apply refl.
  -eapply trans. eapply congru. apply refl. apply IHt1_2.
   apply assoc.
Qed.

Lemma peigne_eqt t:
  eqt (peigne t) t.
Proof.
  induction t; simpl.
  -apply refl.
  -eapply trans. apply append_eqt. now apply congru.
Qed.

Lemma peigne_correct t:
  interp (peigne t) = interp t.
Proof.
  apply eqt_correct. now apply peigne_eqt.
Qed.

Ltac reify A := match A with
                | orb ?X ?Y => let rx := reify X in
                                 let ry := reify Y in
                                 constr:(Or rx ry)
                | ?X => constr:(Bool X) end.

Ltac peignify :=
  match goal with
  | [ |- ?A = ?B] =>
    let a := reify A in
    let b := reify B in
    change A with (interp a);
    change B with (interp b);
    rewrite <- (peigne_correct a);
    rewrite <- (peigne_correct b);
    simpl
  end.

Lemma or_tree_equality b1 b2 b3 b4:
  (b1 || b2) || (b3 || b4) = b1 || ((b2 || b3) || b4).
Proof.
  peignify. reflexivity.
Qed.
