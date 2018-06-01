(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

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
Axiom f0 : Zeq_bool 0 (f 0).

Lemma justf0 :
  Zeq_bool 0 (f 0).
Proof.
  verit f0. auto. 
Qed.





(* c = Certif nclauses t confl  *)
(*    checker_b l true c = checker (PArray.make nclauses nl) None c *)
(*    checker d used_roots c=   *)
(*    Form.check_form t_form && Atom.check_atom t_atom &&  *)
(*    Atom.wt t_i t_func t_atom &&  *)
(*    euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)
(* Close Scope Z_scope. *)


(* Parameter ass347262118 : Zeq_bool 0 (f 0) -> Zeq_bool 0 (f 0). *)
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


(* Parameter p : Z -> Z. *)
(* Axiom p0 : Zeq_bool (p 0) 0. *)

(* Lemma justp0 : *)
(*   Zeq_bool (p 0) 0. *)
(* Proof. *)
(*   verit f0 p0. auto. *)
(* Qed. *)


Parameter a b c d : bool.
Axiom andab : andb a b.
Axiom orcd  : orb c d.

Lemma sat6 :
  orb c (andb a (andb b d)).
Proof.
  verit andab orcd; auto.
Qed.


(* Verit_Checker "sat6.smt2" "sat6.vtlog". *)

Parameter h : Z -> Z.
Axiom h1h2 : andb (Zeq_bool (h 1) 3) (Zeq_bool (h 2) 4).

Lemma h1 :
  Zeq_bool (h 1) 3.

Proof.
  verit h1h2. auto.
Qed.





Parameter f' : Z -> Z.
Parameter g : Z -> Z.
Parameter k : Z.
Axiom g_k_linear : forall x, Zeq_bool (g (x + 1)) ((g x) + k).
Axiom f'_equal_k : forall x, Zeq_bool (f' x) k.


Lemma apply_lemma_multiple :
  forall x y, Zeq_bool (g (x + 1)) (g x + f' y).

Proof.
  verit g_k_linear f'_equal_k. auto.
  auto.
Qed.




Parameter u : Z -> Z.
Axiom u_is_constant : forall x, Zeq_bool (u x) (u 2%Z).


Lemma apply_lemma :
  forall y,
  Zeq_bool (u y) (u 2%Z).

Proof.
  verit u_is_constant. auto.
Qed.

Parameter mult4 : Z -> Z.
Axiom mult4_0 : Zeq_bool (mult4 0) 0.
Axiom mult4_Sn : forall n, Zeq_bool (mult4 (n+1)) (mult4 n + 4).

Lemma mult4_1 : Zeq_bool (mult4 1) 4.

Proof.
  verit mult4_0 mult4_Sn. exact (fun f => f _).
  rewrite sym_zeq_bool. auto.
Qed.

(* c = Certif nclauses t confl 
   checker_b l true c = checker (PArray.make nclauses nl) None c
   checker d used_roots c=  
   Form.check_form t_form && Atom.check_atom t_atom && 
   Atom.wt t_i t_func t_atom && 
   euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)


(* Definition l := 4. *)
(* Definition nclauses := 8. *)
(* Definition confl := 4. *)

(* Definition nl := Lit.neg l. *)
(* Definition d := (PArray.make nclauses nl). *)
(* Definition s := (add_roots (S.make nclauses) d None). *)


(* Compute (checker_b 4 true c). *)
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

(* Compute (up_to 11). *)
(* Compute (nth 11). *)

(* Compute (up_to 12). *)
(* Compute (up_to 13). *)
(* Compute (up_to 14). *)
(* Compute (up_to 15). *)
(* Compute (up_to 16). *)
(* Compute (up_to 17). *)
(* Compute (up_to 18). *)
(* Compute (up_to 19). *)


Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, Zeq_bool (f a) (f b)) ->
    forall x, Zeq_bool (f x) (f 0).
Proof.
  intros f Hf.
  verit Hf; auto.
Qed.
  
Lemma find_inst : 
  implb (Zeq_bool (u 2) 5) (Zeq_bool (u 3) 5).

Proof.
  verit u_is_constant.
  rewrite sym_zeq_bool. auto.
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
  verit.
  exists Int63Native.eqb.
  apply Int63Properties.reflect_eqb.
Defined.

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

(* Print Zeq_bool. *)
(* Print Z.compare. *)

(* SearchAbout Zeq_bool. *)
(* About Zeq_bool. *)
(* Print Zeq_bool. *)


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).

Proof.
  intros a b P f.
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

(* Section S. *)
(*   Variable f : Z -> Z. *)
(*   Hypothesis th : forall x, Zeq_bool (f x) 3. *)
(*   Definition g z := f z. *)
(*   (* Add Theorem th. *) *)
(*   (* Goal forall x, Zeq_bool ((f x) + 1) 4. *) *)
(*     (* verit. *) *)
(* End S. *)

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
  implb (Zeq_bool (dit a) c)
 (implb (Zeq_bool (dit b) d)
 (implb (Zeq_bool a d || Zeq_bool b c)
 (implb (Zeq_bool a c || Zeq_bool a d)
 (implb (Zeq_bool b c || Zeq_bool b d)
        (Zeq_bool a d))))).

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


