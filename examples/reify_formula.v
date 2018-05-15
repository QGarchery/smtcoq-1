Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Parameter f : Z -> Z.
Parameter a : Z.

Axiom faf2 : andb (Zeq_bool (f a) (f 2)) (Zeq_bool (f 2) 1).

Lemma f_1 : Zeq_bool (f a) 1.

Proof.
  verit faf2.
Qed.

Definition t_i := [! | unit_typ_eqb !] : array typ_eqb.
Definition t_func :=
[!Tval t_i (Typ.TZ :: nil, Typ.TZ) f;Tval t_i (nil, Typ.TZ) a |
Tval t_i (nil, Typ.Tbool) true !] : array (tval t_i).
Definition t_atom :=
[!Aapp 1 nil;Aapp 0 (0 :: nil);Acop CO_xH;Auop UO_Zpos 2;
Abop (BO_eq Typ.TZ) 1 3;Auop UO_xO 2;Auop UO_Zpos 5;
Aapp 0 (6 :: nil);Abop (BO_eq Typ.TZ) 1 7;Abop (BO_eq Typ.TZ) 3 7 | 
Acop CO_xH !] : array atom.
Definition t_form := [!Ftrue;Ffalse;Fatom 4;Fatom 8;Fatom 9;Fand [!6;8 | 0 !] | Ftrue !] :
array form.
Definition t := [![!ImmBuildProj (t_i:=t_i) t_func t_atom t_form 3 2 0;
    ImmBuildProj (t_i:=t_i) t_func t_atom t_form 2 2 1;
    EqTr (t_i:=t_i) t_func t_atom t_form 4 4 (9 :: 7 :: nil);
    Res (t_i:=t_i) t_func t_atom t_form 2 [!4;1;3;2 | 0 !] |
    Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] |
  [! | Res (t_i:=t_i) t_func t_atom t_form 0 [! | 0 !] !] !].
Definition c :=
  Certif (t_i:=t_i) (t_func:=t_func) (t_atom:=t_atom) (t_form:=t_form)
         5 t 2 :
certif (t_i:=t_i) t_func t_atom t_form.

(* c = Certif nclauses t confl 
   checker_b l true c = checker (PArray.make nclauses nl) None c
   checker d used_roots c=  
   Form.check_form t_form && Atom.check_atom t_atom && 
   Atom.wt t_i t_func t_atom && 
   euf_checker (* t_atom t_form *) C.is_false (add_roots (S.make nclauses) d used_roots) t confl *)


Definition l := 4.
Definition nclauses := 5.
Definition confl := 2.

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

Close Scope Z_scope.
Fixpoint firsts {A : Type} (n : nat) (l : list A) :=
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




