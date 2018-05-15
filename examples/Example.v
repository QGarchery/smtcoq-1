
(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Open Scope Z_scope.

Lemma sym_zeq_bool x y :
  Zeq_bool x y <-> Zeq_bool y x.

Proof.
  unfold is_true. rewrite <- ? Zeq_is_eq_bool.
  split; intro H; now rewrite H.
Qed.
(* Parameter f : Z -> Z. *)
(* Axiom f_is_constant : forall x, Zeq_bool (f x) (f 2%Z). *)


(* Lemma apply_lemma : *)
(*   forall y, *)
(*   Zeq_bool (f y) (f 2%Z). *)

(* Proof. *)
(*   verit f_is_constant. auto. *)
(* Qed. *)

Parameter mult4 : Z -> Z.
Axiom mult4_0 : Zeq_bool (mult4 0) 0.
Axiom mult4_Sn : forall n, Zeq_bool (mult4 (n+1)) (mult4 n + 4).

Lemma mult4_1 : Zeq_bool (mult4 1) 4.

Proof.
  verit mult4_0 mult4_Sn.
  intros [H1 H2].
  apply H2.
  apply sym_zeq_bool.
  apply mult4_0.
Qed.

Close Scope Z_scope.

Parameter app1024435598 :
Zeq_bool (mult4 0) 0 /\ (forall n : Z, Zeq_bool (mult4 (n + 1)) (mult4 n + 4)) ->
Zeq_bool (mult4 (0 + 1)) (mult4 0 + 4).

Parameter ass1045277882 : Zeq_bool 0 (mult4 0) -> Zeq_bool 0 (mult4 0).
Definition t_i := [! | unit_typ_eqb !] : array typ_eqb.
Definition t_func :=
[!Tval t_i (Typ.TZ :: nil, Typ.TZ) mult4 | Tval t_i (nil, Typ.Tbool) true !] :
array (tval t_i).
Definition t_atom :=
[!Acop CO_xH;Auop UO_Zpos 0;Aapp 0 (1 :: nil);Auop UO_xO 0;
Auop UO_xO 3;Auop UO_Zpos 4;Abop (BO_eq Typ.TZ) 2 5;
Acop CO_Z0;Aapp 0 (7 :: nil);Abop (BO_eq Typ.TZ) 7 8;
Abop BO_Zplus 7 1;Aapp 0 (10 :: nil);Abop BO_Zplus 8 5;
Abop (BO_eq Typ.TZ) 11 12;Abop (BO_eq Typ.TZ) 2 11;
Abop (BO_eq Typ.TZ) 5 12;Abop (BO_eq Typ.TZ) 1 10;Abop BO_Zle 5 12;
Abop BO_Zle 12 5;Abop BO_Zle 1 10;Abop BO_Zle 10 1 | 
Acop CO_xH !] : array atom.

Definition t_form :=
[!Ftrue;Ffalse;Fatom 6;Fatom 9;Fatom 13;Fatom 14;Fatom 15;
Fatom 16;Fatom 17;Fatom 18;For [!12;17;19 | 0 !];Fatom 19;
Fatom 20;For [!14;23;25 | 0 !] | Ftrue !] : array form.
Definition t := [![!Hole (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 2
        (2 :: nil) (prem:=(6 :: nil) :: nil) (concl:=
        6 :: nil) ass1045277882;ForallInst (t_i:=t_i) (t_func:=t_func)
                                  (t_atom:=t_atom) (t_form:=t_form) 3
                                  (conj mult4_0 mult4_Sn) (concl:=
                                  8 :: nil) app1024435598;
    EqTr (t_i:=t_i) t_func t_atom t_form 4 4 (13 :: 9 :: 11 :: nil);
    EqCgr (t_i:=t_i) t_func t_atom t_form 5 10 (Some 15 :: nil);
    Res (t_i:=t_i) t_func t_atom t_form 5 [!4;5 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 3 [!5;1;3 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 1 
      (20 :: nil) nil;ImmBuildDef (t_i:=t_i) t_func t_atom t_form 1 1;
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 5 
      (26 :: nil) nil;ImmBuildDef (t_i:=t_i) t_func t_atom t_form 5 5;
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 4 
      (18 :: 7 :: nil) nil;Res (t_i:=t_i) t_func t_atom t_form 4 [!4;2 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 6 
      (24 :: nil) nil;LiaMicromega (t_i:=t_i) t_func t_atom t_form 7 
                        (22 :: nil) nil;Res (t_i:=t_i) t_func t_atom t_form 6
                                          [!5;7;6 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 6 [!3;6 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 4 [!1;6;4 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 6 
      (16 :: 7 :: nil)
      (ZMicromega.RatProof
         (RingMicromega.PsatzAdd
            (RingMicromega.PsatzMulC (EnvRing.Pc ((-1)%Z))
               (RingMicromega.PsatzIn Z 0)) (RingMicromega.PsatzIn Z 1))
         ZMicromega.DoneProof :: nil);Res (t_i:=t_i) t_func t_atom t_form 4
                                        [!6;2;4 | 0 !] |
    Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] |
  [! | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] !].
Definition c :=
Certif (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 8 t 4 :
certif (t_i:=t_i) t_func t_atom t_form.
  
(* c = Certif nclauses t confl 
   checker_b l true c = checker (PArray.make nclauses nl) None c
   checker d used_roots c=  
   Form.check_form t_form && Atom.check_atom t_atom && 
   Atom.wt t_i t_func t_atom && 
   euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)


Definition l := 4.
Definition nclauses := 8.
Definition confl := 4.

Definition nl := Lit.neg l.
Definition d := (PArray.make nclauses nl).
Definition s := (add_roots (S.make nclauses) d None).


Compute (checker_b 4 true c).
Compute (checker (PArray.make nclauses nl) None c).

Compute (Form.check_form t_form).
Compute (Atom.check_atom t_atom).
Compute (Atom.wt t_i t_func t_atom).
Compute (euf_checker (* t_atom t_form *) C.is_false s t confl).

Definition flatten {A : Type} (trace : array (array A)) :=
PArray.fold_left (fun l_step arr_step => l_step ++ PArray.to_list arr_step)
                 nil trace.

Import ListNotations.
Fixpoint firsts {A : Type} n (l : list A) :=
  match n with
  | 0 => []
  | S n => match l with
           | [] => []
           | he :: ta => he :: firsts n ta end end.

Definition step_euf := @step_checker t_i t_func t_atom t_form.
Definition l_t := flatten t.


Definition up_to n := List.fold_left step_euf (firsts n l_t) s.
Definition nth n := List.nth (n-1) l_t (Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !]).

Compute (List.length l_t).

Compute (up_to 0).
Compute (up_to 1).
Compute (nth 1).

Compute (up_to 2).
Compute (up_to 3).
Compute (up_to 4).
Compute (up_to 5).
Compute (up_to 6).
Compute (up_to 7).
Compute (up_to 8).
Compute (up_to 9).
Compute (up_to 10).

Compute (up_to 11).
Compute (nth 11).

Compute (up_to 12).
Compute (up_to 13).
Compute (up_to 14).
Compute (up_to 15).
Compute (up_to 16).
Compute (up_to 17).
Compute (up_to 18).
Compute (up_to 19).





*)


(* Lemma f_const_is_eq_val_0 : *)
(*   forall x, (forall f : Z -> Z, forall a b, Zeq_bool (f a) (f b)) -> *)
(*             Zeq_bool (f x) (f 0). *)
(* Proof. *)
(*   intros x H. *)
(*   verit H. *)

Lemma find_inst : 
  implb (Zeq_bool (f 2) 5) (Zeq_bool (f 3) 5).

Proof.
  verit f_is_constant.
  intro H. apply H.
Qed.  

Parameter g : Z -> Z.
Parameter k : Z.
Axiom g_k_linear : forall x, Zeq_bool (g (x + 1)) ((g x) + k).
Axiom f_equal_k : forall x, Zeq_bool (f x) k.


Lemma apply_lemma_multiple :
  forall x y, Zeq_bool (g (x + 1)) (g x + f y).

Proof.
  verit g_k_linear f_equal_k; intro H; repeat destruct H; auto.
Qed.

(* c = Certif nclauses t confl 
   checker_b l true c = checker (PArray.make nclauses nl) None c
   checker d used_roots c=  
   Form.check_form t_form && Atom.check_atom t_atom && 
   Atom.wt t_i t_func t_atom && 
   euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)

(*
Definition l := 4.
Definition nclauses := 7.
Definition confl := 3.

Definition nl := Lit.neg l.
Definition d := (PArray.make nclauses nl).
Definition s := (add_roots (S.make nclauses) d None).


Compute (checker_b 4 true c).
Compute (checker (PArray.make nclauses nl) None c).

Compute (Form.check_form t_form).
Compute (Atom.check_atom t_atom).
Compute (Atom.wt t_i t_func t_atom).
Compute (euf_checker (* t_atom t_form *) C.is_false s t confl).

Definition flatten {A : Type} (trace : array (array A)) :=
PArray.fold_left (fun l_step arr_step => l_step ++ PArray.to_list arr_step)
                 nil trace.

Import ListNotations.
Fixpoint firsts {A : Type} n (l : list A) :=
  match n with
  | 0 => []
  | S n => match l with
           | [] => []
           | he :: ta => he :: firsts n ta end end.

Definition step_euf := @step_checker t_i t_func t_atom t_form.
Definition l_t := flatten t.
SearchAbout PArray.array.

Definition up_to n := List.fold_left step_euf (firsts n l_t) s.
Definition nth n := List.nth (n-1) l_t (Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !]).

Compute (List.length l_t).

Compute (up_to 0).
Compute (up_to 1).

Compute (up_to 2).

Compute (up_to 3).
Compute (nth 3).
*)

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

