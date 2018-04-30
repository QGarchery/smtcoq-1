Require Import SMTCoq.

Local Open Scope int63_scope.

Parameter mult4 :  Z -> Z.
Axiom mult4_0 : (* forall y : int, *) Zeq_bool (mult4 0) 0.
Axiom mult4_Sx : forall x, Zeq_bool (mult4 (x+1)) (mult4 x + 4).

(* Lemma mult4_1 : Zeq_bool (mult4 1) 4. *)
(* Proof. *)
(*   verit mult4_0 mult4_Sx; *)
(*   intro H; destruct H as [H1 H2]; auto. *)
(* Qed. *)


Parameter app1024435598 :
Zeq_bool (mult4 0) 0 /\ (forall x : Z, Zeq_bool (mult4 (x + 1)) (mult4 x + 4)) ->
Zeq_bool (mult4 (0 + 1)) (mult4 0 + 4).
Definition t_i := [! | unit_typ_eqb !] : array typ_eqb.
Definition t_func := [!Tval t_i (Typ.TZ :: nil, Typ.TZ) mult4 | Tval t_i (nil, Typ.Tbool) true !] :
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
[!Ftrue;Ffalse;Fatom 6;Fatom 9;Fatom 13;For [!1;8 | 0 !];
Fatom 14;Fatom 15;Fatom 16;Fatom 17;Fatom 18;For [!14;19;21 | 0 !];
Fatom 19;Fatom 20;For [!16;25;27 | 0 !] | Ftrue !] : 
array form.
Definition t := [![!ForallInst (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 3
        (conj mult4_0 mult4_Sx) (concl:=8 :: nil) app1024435598;
    EqTr (t_i:=t_i) t_func t_atom t_form 4 4 (15 :: 9 :: 13 :: nil);
    EqCgr (t_i:=t_i) t_func t_atom t_form 5 12 (Some 17 :: nil);
    Res (t_i:=t_i) t_func t_atom t_form 5 [!4;5 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 3 [!5;1;3 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 1 
      (22 :: nil) nil;ImmBuildDef (t_i:=t_i) t_func t_atom t_form 1 1;
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 5 
      (28 :: nil) nil;ImmBuildDef (t_i:=t_i) t_func t_atom t_form 5 5;
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 4 
      (20 :: 7 :: nil) nil;Res (t_i:=t_i) t_func t_atom t_form 4 [!4;2 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 6 
      (26 :: nil) nil;LiaMicromega (t_i:=t_i) t_func t_atom t_form 7 (24 :: nil) nil;
    Res (t_i:=t_i) t_func t_atom t_form 6 [!5;7;6 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 6 [!3;6 | 0 !];
    Res (t_i:=t_i) t_func t_atom t_form 4 [!1;6;4 | 0 !];
    LiaMicromega (t_i:=t_i) t_func t_atom t_form 6 
      (18 :: 7 :: nil)
      (ZMicromega.RatProof
         (RingMicromega.PsatzAdd
            (RingMicromega.PsatzMulC (EnvRing.Pc (-1)%Z) (RingMicromega.PsatzIn Z 0))
            (RingMicromega.PsatzIn Z 1)) ZMicromega.DoneProof :: nil);
    Res (t_i:=t_i) t_func t_atom t_form 1 [!6;2;4 | 0 !] |
    Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] |
  [! | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] !].

Definition c :=
Certif (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form) 8 t 1 :
certif (t_i:=t_i) t_func t_atom t_form.

(* c = Certif nclauses t confl *)
(* checker_b l true c = checker (PArray.make nclauses nl) None c*)
(* checker d used_roots c=  *)
(*  Form.check_form t_form && Atom.check_atom t_atom && *)
(*  Atom.wt t_i t_func t_atom && *)
(*  euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)



Definition l := 4.
Definition nclauses := 8.
Definition confl := 1.

Definition nl := Lit.neg l.
Definition d := (PArray.make nclauses nl).
Definition s := (add_roots (S.make nclauses) d None).

Definition flatten {A : Type} (trace : array (array A)) :=
PArray.fold_left (fun l_step arr_step => l_step ++ PArray.to_list arr_step)
                 nil trace.

Import ListNotations.

Close Scope Z_scope.
Fixpoint firsts {A : Type} n (l : list A) :=
  match n with
  | 0 => []
  | S n => match l with
           | [] => []
           | he :: ta => he :: firsts n ta end end.

Definition step_euf := @step_checker t_i t_func t_atom t_form.
Definition l_t := flatten t.
SearchAbout PArray.array.

(* SET AD HOC *)
Definition s' := PArray.set s 2 [6].
(* SET AD HOC *)

Definition up_to n := List.fold_left step_euf (firsts n l_t) s'.
Compute (List.length l_t).
Definition nth n := List.nth (n-1) l_t (Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !]).

Compute (up_to 0).
Compute (up_to 1).
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
