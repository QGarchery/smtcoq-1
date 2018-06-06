(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Lemma xylt :
  forall x y : Z,
    (x <? 7) || (y <? 4) || (x + y >=? 11).
Proof. verit. Qed.  

Parameter mult_by_7 : Z -> Z.
Axiom m0 : mult_by_7 0 =? 0.
Axiom mSn : forall x, mult_by_7 (x+1) =? mult_by_7 x + 7.
Lemma m5 : mult_by_7 5 =? 35.
Proof. verit m0 mSn. now rewrite Z.eqb_sym. Qed.

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
  verit. 
  exists Int63Native.eqb.
  apply Int63Properties.reflect_eqb.
Defined.

Parameter f : Z -> Z.
Axiom f0 : 0 =? f 0.

Lemma justf0 :
  0 =? f 0.
Proof.
  verit f0.
Qed.

(* c = Certif nclauses t confl  *)
(*    checker_b l true c = checker (PArray.make nclauses nl) None c *)
(*    checker d used_roots c=   *)
(*    Form.check_form t_form && Atom.check_atom t_atom &&  *)
(*    Atom.wt t_i t_func t_atom &&  *)
(*    euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)
(* Close Scope Z_scope. *)


(* Parameter ass347262118 : Z.eqb 0 (f 0) -> Z.eqb 0 (f 0). *)
(* Definition t_i := [! | unit_typ_eqb !] : array typ_eqb. *)
(* Definition t_func := [!Tval t_i (Typ.TZ :: nil, Typ.TZ) f | Tval t_i (nil, Typ.Tbool) true !] *)
(* : array (tval t_i). *)
(* Definition t_atom := [!Acop CO_Z0;Aapp 0 (0 :: nil);Abop (BO_eq Typ.TZ) 0 1 | Acop CO_xH !] : *)
(* array atom. *)
(* Definition t_form := [!Ftrue;Ffalse;Fatom 2 | Ftrue !] : array form. *)
(* Definition t := [![!Hole (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 2 *)
(*         (2 :: nil) (prem:=(4 :: nil) :: nil) (concl:= *)
(*         4 :: nil) ass347262118;Res (t_i:=t_i) t_func t_atom t_form 1 [!2;1 | 0 !] | *)
(*     Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] | *)
(*   [! | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] !]. *)

(* Definition c := *)
(* Certif (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 3 t *)
(*    1 : *)
(* certif (t_i:=t_i) t_func t_atom t_form. *)


(* Definition l := 4. *)
(* Definition nclauses := 3. *)
(* Definition confl := 1. *)

(* Definition nl := Lit.neg l. *)
(* Definition d := (PArray.make nclauses nl). *)
(* Definition s := (add_roots (S.make nclauses) d None). *)


(* Compute (checker_b l true c). *)
(* Compute (checker (PArray.make nclauses nl) None c). *)

(* Compute (Form.check_form t_form). *)
(* Compute (Atom.check_atom t_atom). *)
(* Compute (Atom.wt t_i t_func t_atom). *)
(* Compute (euf_checker (* t_atom t_form *) C.is_false s t confl). *)

(* Definition flatten {A : Type} (trace : array (array A)) := *)
(* PArray.fold_left (fun l_step arr_step => l_step ++ PArray.to_list arr_step) *)
(*                  nil trace. *)

(* Import ListNotations. *)
(* Fixpoint firsts {A : Type} n (l : list A) := *)
(*   match n with *)
(*   | 0 => [] *)
(*   | S n => match l with *)
(*            | [] => [] *)
(*            | he :: ta => he :: firsts n ta end end. *)

(* Definition step_euf := @step_checker t_i t_func t_atom t_form. *)
(* Definition l_t := flatten t. *)


(* Definition up_to n := List.fold_left step_euf (firsts n l_t) s. *)
(* Definition nth n := List.nth (n-1) l_t (Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !]). *)

(* Compute (List.length l_t). *)

(* Compute (up_to 0). *)
(* Compute (up_to 1). *)
(* Compute (nth 1). *)
(* Compute (up_to 2). *)

(* Compute (up_to 3). *)
(* Compute (up_to 4). *)
(* Compute (up_to 5). *)
(* Compute (up_to 6). *)
(* Compute (up_to 7). *)
(* Compute (up_to 8). *)
(* Compute (up_to 9). *)
(* Compute (up_to 10). *)


Parameter p : Z -> Z.
Axiom p0 : p 0 =? 0.

Lemma justp0 :
  p 0 =? 0.
Proof.
  verit f0 p0.
Qed.


Parameter a b c d : bool.
Axiom andab : andb a b.
Axiom orcd  : orb c d.

Lemma sat6 :
  orb c (andb a (andb b d)).
Proof.
  verit andab orcd.
Qed.

(* Verit_Checker "sat6.smt2" "sat6.vtlog". *)

Parameter h : Z -> Z.
Axiom h1h2 : andb (h 1 =? 3) (h 2 =? 4).

Lemma h1 :
  h 1 =? 3.

Proof.
  verit h1h2.
Qed.

Parameter f' : Z -> Z.
Parameter g : Z -> Z.
Parameter k : Z.
Axiom g_k_linear : forall x, g (x + 1) =? (g x) + k.
Axiom f'_equal_k : forall x, f' x =? k.


Lemma apply_lemma_multiple :
  forall x y, g (x + 1) =? g x + f' y.

Proof.
  verit g_k_linear f'_equal_k.
Qed.


Parameter u : Z -> Z.
Axiom u_is_constant : forall x y, u x =? u y.


Lemma apply_lemma :
  forall x, u x =? u 2.

Proof.
  verit u_is_constant.
  (* ; try (intro H; try (rewrite sym_zeq_bool; apply H); apply H). *)
Qed.

Parameter mult4 : Z -> Z.
Axiom mult4_0 : mult4 0 =? 0.
Axiom mult4_Sn : forall n, mult4 (n+1) =? mult4 n + 4.

Lemma mult4_1 : mult4 1 =? 4.

Proof.
  verit mult4_0 mult4_Sn; try (intro H; rewrite Z.eqb_sym; apply H).
Qed.

Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof.
  intros f Hf.
  verit Hf.
Qed.
  
Lemma find_inst : 
  implb (u 2 =? 5) (u 3 =? 5).

Proof.
  verit u_is_constant.
Qed.  


Lemma irrelf_ltb :
  forall a b c,
  (Z.ltb a b) &&
  (Z.ltb b c) &&
  (Z.ltb c a) = false.

Proof.
  verit.
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
Print sat2.  

(* Examples that check ZChaff certificates *)


Close Scope Z_scope.
Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat3 "sat.cnf" "sat.log".
Check sat3.


Zchaff_Checker "hole4.cnf" "hole4.log".


(* Example that checks a VeriT certificate, for logic QF_UF *)

(* Section Verit. *)
(*   Verit_Checker "euf.smt2" "euf.log". *)
(* End Verit. *)

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

(* Print Z.eqb. *)
(* Print Z.compare. *)

(* SearchAbout Z.eqb. *)
(* About Z.eqb. *)
(* Print Z.eqb. *)


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
    negb (Z.eqb (f a) b) || negb (P (f a)) || P b.

Proof.
  intros a b P f.
  destruct_with_eqn (P (f a)).
  destruct_with_eqn (Z.eqb (f a) b).
  +apply orb_true_iff. right.
   rewrite Z.eqb_eq in Heqb1.
   now rewrite Heqb1 in Heqb0.
  +auto.
  +apply orb_true_iff; left; apply orb_true_iff; right; now simpl.
   (* verit. *)
Qed.

Definition Myeqbool : Z -> Z -> bool := Z.eqb.
Print Z.eqb.


Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
    (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).

Proof.
  verit.
Qed.

(* Parameter toto : Z -> Z. *)
(* Variable toto : Z. *)

(* Section S. *)
(*   Variable f : Z -> Z. *)
(*   Hypothesis th : forall x, Z.eqb (f x) 3. *)
(*   Definition g z := f z. *)
(*   (* Add Theorem th. *) *)
(*   (* Goal forall x, Z.eqb ((f x) + 1) 4. *) *)
(*     (* verit. *) *)
(* End S. *)

Definition g1 (f : Z -> Z) (x : Z) := f x.

Lemma comp f g (x1 x2 x3 : Z) :
  ifb (Z.eqb x1 (f x2))
      (ifb (Z.eqb x2 (g x3))
           (Z.eqb x1 (f (g x3)))
           true)
      true.
Proof.
  verit.
Qed.


Lemma un_menteur (a b c d : Z) dit:
  implb (Z.eqb (dit a) c)
 (implb (Z.eqb (dit b) d)
 (implb (Z.eqb a d || Z.eqb b c)
 (implb (Z.eqb a c || Z.eqb a d)
 (implb (Z.eqb b c || Z.eqb b d)
        (Z.eqb a d))))).

Proof.
  verit.
Qed.

Lemma un_menteur_prop (a b c d : Z) dit:
  dit a = c ->
  dit b = d ->
  a = d \/ b = c ->
  a = c \/ a = d ->
  b = c \/ b = d ->
  a = d.

Proof.
  intros H1 H2 H3 H4 H5.
  destruct H3 as [H3 | H3]; trivial.
  destruct H4 as [H4 | H4]; trivial.
  rewrite H3, H4 in *. 
  now rewrite <- H1.
Qed.


