(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Parameter f : Z -> Z.
Axiom f_is_constant : forall x y, Zeq_bool (f x) (f y).
  
Lemma apply_lemma :
  forall y,
  Zeq_bool  (f y) (f 5%Z).

Proof.  
  verit f_is_constant. auto.
Qed.  

Lemma find_inst :
  implb (Zeq_bool (f 2) 5) (Zeq_bool (f 3) 5).

Proof.  
  verit f_is_constant.
  intro H. apply H.
Qed.  

Parameter g : Z -> Z.
Parameter k : Z.
Axiom g_k_linear : forall x, Zeq_bool (g (x + 1)) ((g x) + k).

Lemma apply_lemma_multiple :
  forall x, Zeq_bool (g (x + 5)) ((g x) + 5 * k).

Proof.
  verit g_k_linear; auto.
Qed.



Lemma sat2_gen a1 a2 a3:
  forall v : int -> bool,
    (v a1 || v a2 || v a3) &&
    (negb (v a1) || negb (v a2) || negb (v a3)) &&
    (negb (v a1) || v a2) &&
    (negb (v a2) || v a3) &&
    (negb (v a3) || v a1)  = false.

Zchaff_Theorem sat "sat.cnf" "sat.log".
About sat.

Proof.
  verit f_is_constant.
  exists Int63Native.eqb.
  intros x y.
  apply Int63Properties.reflect_eqb.
Defined.




Lemma irrelf_ltb :
  forall a b c,
  (Z.ltb a b) &&
  (Z.ltb b c) &&
  (Z.ltb c a) = false.

Proof.
  verit f_is_constant.
Qed.

Lemma sat2:
  forall a1 a2 a3 : bool,
    (a1 || a2 || a3) &&
    (negb (a1) || negb (a2) || negb (a3)) &&
    (negb (a1) || a2) &&
    (negb (a2) || a3) &&
    (negb (a3) || a1)  = false.
Proof.
  verit.
Qed.
  
(* Examples that check ZChaff certificates *)

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.


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



Print sat2_gen.
Check checker_b_correct.



Parameter y : Z.
Parameter app328061879 : lemma -> Zeq_bool (f 2) (f y).
Definition t_i := [! | unit_typ_eqb !] : array typ_eqb.
Definition t_func :=[!Tval t_i (Typ.TZ :: nil, Typ.TZ) f;Tval t_i (nil, Typ.TZ) y |Tval t_i (nil, Typ.Tbool) true !] : array (tval t_i).
Definition t_atom := [!Acop CO_xH;Auop UO_xO 0;Auop UO_Zpos 1;Aapp 0 (2 :: nil);Aapp 1 nil;Aapp 0 (4 :: nil);Abop (BO_eq Typ.TZ) 3 5;Aapp 0 nil;Aapp 0 (7 :: nil);Abop (BO_eq Typ.TZ) 8 8 |Acop CO_xH !] : array atom.
Definition t_form := [!Ftrue;Ffalse;Fatom 6;Fatom 9;For [!7;4 | 0 !] | Ftrue !] : array form.
Definition t := [![!ForallInst (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 2 pl (concl:=4 :: nil) app328061879;Res (t_i:=t_i) t_func t_atom t_form 3 [!2;1 | 0 !] | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] |[! | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] !].
Definition c := Certif (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 4 t 3 :certif (t_i:=t_i) t_func t_atom t_form.

Definition l := 4.
Definition confl := 3.
Definition nclauses := 4.
Definition nl := Lit.neg l.
Definition d := (PArray.make nclauses nl).

Compute (checker_b 4 true c).

Compute (Form.check_form t_form).
About checker.
Compute (checker (PArray.make nclauses l) None c).
Compute (Form.check_form t_form && Atom.check_atom t_atom).
Compute (euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d None) t confl).
About Atom.wt.

Compute (Atom.wt t_i t_func t_atom ).
