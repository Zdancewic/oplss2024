(** ** Imp: Imperative Programs *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From RIP Require Import Maps Imp.

Open Scope com_scope.

(* ================================================================= *)
(** ** Imp Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     a := n | x | a + a | a - a | a * a

     b := true | false | a = a | a ≠ a | a ≤ a | a > a | ~ b | b && b

     c := skip | x := a | c ; c | if b then c else c end
         | while b do c end
*)

(** Abstract syntax as _inductive datatypes_ in Coq. E.g.: *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(* ================================================================= *)
(** ** Example: Factorial *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* ================================================================= *)
(** ** OPTIMIZATION / REASONING DEMO *)

(** See Coq devlopment *)

(* ================================================================= *)
(** ** Imp Memory *)

(** The state of an [Imp] program is a _memory_ of type [mem]
  that maps variables to their current values.  *)

Definition mem := string -> nat.

(** We can use some notation to write some example memories: *)

Example mem_init := (_ !-> 0).

Example mem_ex2 := (X !-> 3; Y !-> 120).

Example mem_final := (Z !-> 0; X !-> 6; Y !-> 720).

(* ================================================================= *)
(** ** Semantics *)

(** We need to endow the abstract syntax with a _semantics_.  One
    way to do that is to implement an interpreter.  It is just
    a recursive functions that computes the result, given
    a starting memory.
 *)
Fixpoint aeval (m : mem) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => m x
  | <{a1 + a2}> => (aeval m a1) + (aeval m a2)
  | <{a1 - a2}> => (aeval m a1) - (aeval m a2)
  | <{a1 * a2}> => (aeval m a1) * (aeval m a2)
  end.

Eval compute in (aeval mem_ex2 <{ X * Y }>).
(** [===> 360 : nat] *)

(* ----------------------------------------------------------------- *)
(** *** Boolean expression interpreter *)

Fixpoint beval (m : mem) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval m a1) =? (aeval m a2)
  | <{a1 <> a2}>  => negb ((aeval m a1) =? (aeval m a2))
  | <{a1 <= a2}>  => (aeval m a1) <=? (aeval m a2)
  | <{a1 > a2}>   => negb ((aeval m a1) <=? (aeval m a2))
  | <{~ b1}>      => negb (beval m b1)
  | <{b1 && b2}>  => andb (beval m b1) (beval m b2)
  end.

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [while] case. *)

Fixpoint denote (c : com) (st : mem) : mem :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := denote c1 st in
        let st'' := denote c2 st' in
        st''
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then denote c1 st
          else denote c2 st
    | <{ while b do c end }> =>
        st  (* bogus! *)
  end.

(* ----------------------------------------------------------------- *)
(** *** Relational Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

(* ----------------------------------------------------------------- *)
(** *** In Coq *)
Inductive ceval : com -> mem -> mem -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').


(* ----------------------------------------------------------------- *)
(** *** Some observations *)

(** This large-step operational semantics is fine for many purposes, primary among them:

- specifying [Imp] program behaviors

But there are drawbacks:

- is _partial_: there is no resulting [mem] for a diverging program
- isn't _structural_: the [E_WhileTrue] rule is defined in terms of itself
- isn't _executable_: we can't extract this as a program (no QuickChick!)
- is a _deep_ embedding: no re-use of meta-level (Coq) functionality

Consequently: not very extensible, hard to re-use the metatheory.

Can we do it differently?
*)

(* 2024-06-07 10:32 *)
