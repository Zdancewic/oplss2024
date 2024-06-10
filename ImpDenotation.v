From Coq Require Import String Nat Program.
From RIP Require Import Imp Maps Utils.

(* INTSTRUCTORS: Compatability [state] vs [mem] *)
Definition mem := Imp.state.
Notation val := nat.

From Coq Require Import
     String.
From ITree Require Import
     ITree Events.State.
Import Monads.
Import ITreeNotations.
Open Scope itree.
Open Scope com_scope.


(* ================================================================= *)
(** ** Imp Semantics, Denotationally *)

(**
  Through this course, we have notably seen that infinite behaviors
  of systems are naturally modelled as coinductive data-types, the
  equivalence of such systems as bisimulations, and that co-induction
  is hence a central tool to reason about these systems.

  One particular class of such systems are general purpose, Turing-complete,
  programming languages. In this project, we turn our attention to Imp¹, a
  simple imperative, sequential, programming language equipped with a global
  memory and loops.
*)

(* ----------------------------------------------------------------- *)
(** *** Representing Imp as Interaction Trees *)

(** Imp programs interact with a memory. We will represent these interactions
   through read and writes events *)

Variant MemE : Type -> Type :=
  | Read  (x : string)           : 	MemE val
  | Write (x : string) (v : val) : 	MemE unit
.

Definition rd x   := ITree.trigger (Read x).
Definition wr x v := ITree.trigger (Write x v).

(* ----------------------------------------------------------------- *)
(** *** Arithmetic operations *)

Variant aop :=  | op_plus | op_minus | op_mult.

(** And their semantics as Coq functions: *)
Definition aop_sem (op : aop) :=
  match op with
  | op_plus => add
  | op_minus => sub
  | op_mult => mult
  end.

(* ----------------------------------------------------------------- *)
(** *** Translation into ITrees *)

Reserved Notation "⟦ a '⟧a'".
Fixpoint repr_aexp (a : aexp) : itree MemE val :=
  let aop op a b :=
    a <- ⟦ a ⟧a;;        (* We simply bind recursive calls *)
    b <- ⟦ b ⟧a;;
    Ret (aop_sem op a b)
  in
  match a with
  | ANum n      => Ret n (* Pure computation: we simply return n *)
  | AId x       => rd x  (* We put the responsability on the environment:
                        we just "trigger" the read *)
  | APlus a b => aop op_plus a b
  | AMinus a b => aop op_minus a b
  | AMult a b => aop op_mult a b
  end
where "⟦ a '⟧a'" := (repr_aexp a)
.

(* ----------------------------------------------------------------- *)
(** *** Boolean operations *)

Reserved Notation "⟦ b '⟧b'".
Fixpoint repr_bexp (b : bexp) : itree MemE bool :=
  match b with
  | <{ true  }>     => Ret true
  | <{ false }>     => Ret false

  | <{ a1 = a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (x =? y)

  | <{ a1 <> a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (negb(x =? y))

  | <{ a1 > a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (negb(x <=? y))

  | <{ a1 <= a2 }> =>
      x <- ⟦ a1 ⟧a;;
      y <- ⟦ a2 ⟧a;;
      Ret (x <=? y)

  | <{ b1 && b2 }> =>
      x <- ⟦ b1 ⟧b;;
      y <- ⟦ b2 ⟧b;;
      Ret (andb x y)

  | <{ ~ b }> =>
      x <- ⟦ b ⟧b;;
      Ret (negb x)
  end
where "⟦ b '⟧b'" := (repr_bexp b)
.

(* ----------------------------------------------------------------- *)
(** *** Representation of commands *)

Reserved Notation "⟦ c ⟧".
Fixpoint repr_com (c : com) : itree MemE unit :=
  match c with
  | <{ skip }> => Ret tt
  | <{ x := a }> => v <- ⟦ a ⟧a;; wr x v
  | <{ c1 ; c2 }> => ⟦c1⟧;; ⟦c2⟧

  | <{ if b then c1 else c2 end }> =>
      x <- ⟦ b ⟧b;;
      if x then ⟦c1⟧ else ⟦c2⟧

  | <{ while b do c end }> =>
      repeat (                   (* <== NOTE: use of _repeat_ *)
	  x <- ⟦b⟧b;;
	  if x
	  then ⟦c⟧;; Ret (inl tt)
	  else Ret (inr tt)
	)
  end
where "⟦ c ⟧" := (repr_com c)
.

(* ----------------------------------------------------------------- *)
(** *** Some observations *)

(** This version of the Imp semantics is:
- defined by _structural induction_ on the syntax.
- is _parametric_ in the interpretation of memory events
- is compatible with extraction (for interpretation)
*)

(** In some sense, this is still _syntactic_, but it already has "unfolded" the
control-flow of the program into a big (possibly infinite) tree. That will make
proving [Imp] equivalences easier.  *)

(* ----------------------------------------------------------------- *)
(** *** Memory Event Handlers *)

(** Here, [stateT] is a _monad transformer_ that lifts a monadic
computation into the [state] monad: *)

Notation M := (stateT mem (itree void1)).

Example Mdef : M unit = (mem -> itree void1 (mem * unit)).
Proof. reflexivity. Qed.

(** The handler for [MemE] events *)
Definition handle_Mem : MemE ~> M :=
  fun _ e st => match e with
             | Read x    => Ret (st, st x)
             | Write x v => Ret (x !-> v; st, tt)
             end.

(* ----------------------------------------------------------------- *)
(** *** Finally, some nice notation for Imp semantics *)

Notation "'ℑ'" := (interp_state handle_Mem) (at level 0).

Definition model_com : com -> M unit :=
  fun c => ℑ ⟦ c ⟧.
Notation "'⟦{' c '}⟧'" := (model_com c).

(* ----------------------------------------------------------------- *)
(** *** Running Factorial *)

(** Now that we have a functional implementation of the [Imp] semantics,
 we can run it...

Unfortunately, the result has type [string -> nat], and Coq prints it
in a very ugly way, so we've cheated...*)

Eval compute in (burn 50 (⟦{ <{ X := 5 ; fact_in_coq }> }⟧ (fun _ => 0))).

(** ==>

Ret (fun v =>
     match v with
     | "Z" => 0
     | "Y" => 120
     | "X" => 5
     end.)  : itree mem unit
*)

Module ImpPrint.

(* ----------------------------------------------------------------- *)
(** *** Exercise *)

(** Challenge: add a "print" command to Imp. Use the following event signature. *)

Variant PrintE : Type -> Type :=
  | print (s:string) : PrintE unit.

(** Set up the semantics so that the new denotation of a command has the type: [MP unit]. *)

Definition MP := stateT mem (itree PrintE).

End ImpPrint.

(* 2024-06-07 10:32 *)
