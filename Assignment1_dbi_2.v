(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

(* Inductive free_var : Type :=
   | lc_var( x:nat). *)

Inductive lc_term : Type:=
  | lc_var( x:nat) 
  | lc_abs (e:lc_term)
  | lc_app (e1 e2 : lc_term).

Fixpoint size (p : lc_term) : nat :=
  match p with
  | lc_var x => 1
  | lc_abs e => 1 + size e
  | lc_app e1 e2 => (size e1) + (size e2)
  end.

Fixpoint ht ( e : lc_term) : nat :=
  match e with
  | lc_var x => 0
  | lc_abs e1 => 1 + (ht e1)
  | lc_app e1 e2 => 1 + ( max (ht e1) (ht e2) )
  end.

Check lc_abs (lc_var 5).
Check lc_var 5.


Notation "M --> N" := (lc_app M N)
                     (at level 61, left associativity).

(* Notation "-- 1":= (lc_var 1) (at level 61, left associativity).

Compute "-- 1".
 *)
Check lc_var 1 --> lc_var 2 .

Check lc_app (lc_var 1) (lc_var 1).

Fixpoint eqlc (e1 e2 : lc_term) : bool :=
  match e1 with
    | lc_var x => match e2 with 
         | lc_var y => (x =? y)
         | _ => false
        end
    | lc_abs e1' => match e2 with
                    | lc_abs e2' => eqlc e1' e2'
                    | _  => false
                    end
    | lc_app e11' e12' => match e2 with 
                        | lc_app e21' e22' => if ( andb (eqlc e11' e21') (eqlc e12' e22')) then true else false
                        | _ =>false
                        end
  end.

Compute eqlc (lc_var 1) (lc_var 2).

Compute eqlc (lc_abs (lc_var 1)) (lc_var 2).
Compute eqlc (lc_var 1) (lc_var 2).



Fixpoint db_shift_i_co (i :nat) (co:nat) (e : lc_term) : lc_term :=
  match e with
    | lc_var n => if n <? co then (lc_var n) else lc_var( n + i)
    | lc_abs e' => lc_abs (db_shift_i_co i (co+1) e')
    | lc_app e1 e2 => lc_app (db_shift_i_co i co e1) (db_shift_i_co i co e2)
  end.

Compute db_shift_i_co 1 2 (lc_abs (lc_var 2)).

Compute (lc_app (lc_var 2) (lc_var 4)).

Compute db_shift_i_co 1 2  ((lc_var 2) --> ( lc_abs (lc_var 2))).

(* Fixpoint db_shift_left_i_co (i :nat) (co:nat) (e : lc_term) : lc_term :=
  match e with complete this
    | lc_var n => if n <? co-i then (lc_var n) else lc_var( n + i)
    | lc_abs e' => lc_abs (db_shift_i_co i (co+1) e')
    | lc_app e1 e2 => lc_app (db_shift_i_co i co e1) (db_shift_i_co i co e2)
  end.

Compute db_shift_i_co 1 2 (lc_abs (lc_var 2)).
 *)

(* Check if e1 occurs in e2*)
Fixpoint occurs_e (e1 e2:lc_term) : bool:= (* Check if e1 occurs in e2*)
  if (eqlc e1 e2) then true else match e2 with
                                  | lc_var x1 => false
                                  | lc_abs e2' => occurs_e (db_shift_i_co 1 0 e1) e2'  (* Shifting needs to be applied here*)
                                  | lc_app e21 e22 => orb (occurs_e e1 e21) (occurs_e e1 e22)
                                  end.


Compute 3-1.
Compute ltb 3 1.
Compute 3<?1.

Compute occurs_e (lc_var 2) (lc_abs ((lc_var 1)-->(lc_abs (lc_var 4)  ) ) ) .

(* Fixpoint getFreeVars ( e: lc_term) : bag:
  match e with 
    | lc_var x => cons x nil
    | lc_abs co e1 => remove_all co (getFreeVars e1)
 *)

(*
  subsitute free variable fr_x with e2 in e1
*)
Compute db_shift_i_co 1 0 (lc_var 0).
Fixpoint subsitute_lc (fr_x : nat) (e2 : lc_term) (e1 :lc_term) :lc_term :=
  if ( eqlc e1 (lc_var fr_x)) then e2 else 
    match e1 with 
      | lc_var x => e1
      | lc_abs e1' => lc_abs (subsitute_lc (fr_x+1) (db_shift_i_co 1 0 e2) e1')
      | lc_app e1' e2' => lc_app (subsitute_lc fr_x e2 e1') (subsitute_lc fr_x e2 e2' )
      end.

Compute subsitute_lc (1) (lc_var 12) (lc_abs (lc_var 2)).
Compute subsitute_lc (1) (lc_var 12) (lc_abs (lc_var 2) --> (lc_var 1)).


(*
    1 subgoal
x, y' : nat
hyp_ab : (y' =? x) = true
______________________________________(1/1)
lc_var x = lc_var y'

*)

Search (?x =? ?y ).

Theorem nat_eq : forall (n m : nat),
 ((m =? n) = true) ->   (m=n)  .
Proof. 
  intros. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(*  
    Proving Subsitution lema
*)

Theorem substitution_x_x : forall (x:nat) ( e:lc_term),
  subsitute_lc x (lc_var x) e = e.
(* [x:=x]e = e*)

Proof. intros. induction e as [y'| abs | e1e2 ]. 
  - simpl. case_eq (y' =? x); intros hyp_ab.
    -- 
 induction x as [| n'].
    -- simpl. induction y' as [| n2]. 
        ---simpl.  reflexivity.
        --- simpl. reflexivity.
    -- induction y' as [| n2].
        ---simpl. reflexivity.
        --- simpl.
    --
  - simpl. rewrite IHv. reflexivity.
  Qed.





