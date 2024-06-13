From Coq Require Import String Nat.
From Coq Require Import ZArith Ascii List RelationClasses Eqdep.
From RIP Require Import Monads.
Import Monad.
Import ListNotations.
Import MonadLawsEqM.
Import MonadNotation.

(* ================================================================= *)
(** ** Extensible Semantics and the [Free] Monad

    Through this chapter, we introduce successive intuitions to build up to the
 Interaction Tree monad, a convenient data-structure for building semantic
 domains. As we will see, Interaction Trees are one way to solve the
 problem of representing divergent computations in Coq.  They also share
 many properties with something called a "free monad", which is the topic
 of this Chapter.

 We start by looking at how to create an extensible evaluator for simple
 arithmetic expressions.
 *)

Module Expr.

(** Consider a trivial datatype of expressions, made of only constants
 and additions: *)

Inductive Expr : Set :=
| Val (n : nat)
| Add (e1 e2 : Expr).

(** We may easily define functions that fold over this datatype. For instance, an
 evaluation function: *)
Fixpoint eval (e : Expr) : nat :=
  match e with
  | Val n => n
  | Add e1 e2 => eval e1 + eval e2
  end.

Example e : Expr := Add (Val 3) (Val 4).
Eval compute in eval e.
(** ==> [7 : nat] *)

(* ----------------------------------------------------------------- *)
(** *** The expression problem

    Philip Wadler phrased in 1998 the _expression problem_ as the following challenge:
Can one define a data type by cases where one can add new cases to the data types, while still being able to define new functions over the data
   type, without recompiling existing code, all while retaining type safety?
   *)

(** Indeed, if decide to add subtraction to these expressions, our best bet
   seems to be to edit the definition of [Expr], and then extend the [eval]
   function.  It is here trivial, but scales poorly!  *)

Inductive Expr' : Set :=
| Val' (n : nat)
| Add' (e1 e2 : Expr')
| Minus' (e1 e2 : Expr').

Fixpoint eval' (e : Expr') : nat :=
  match e with
  | Val' n => n
  | Add' e1 e2 => eval' e1 + eval' e2
  | Minus' e1 e2 => eval' e1 - eval' e2
  end.

Example e' : Expr' := Minus' (Val' 7) (Val' 4).
Eval compute in eval' e'.
(** ==> [3 : nat] *)

End Expr.

Module FreeExpr.

 (** *** One solution (Datatypes à la carte) *)

  (** We consider here a solution to the expression problem popularized by Wouter
  Swierstra in "Datatypes à la carte".  (Our case is a bit simplified and we make
  adaptations to move from Haskell to Coq.)

 Consider the following new langage of expressions. It is parameterized by a
 certain domain of operations [Op], and can represent expressions built out of two
 constructors:
 *)
  (** Add a parameter so [Expr Op] is now either
   - a value, or,
   - a computation that first performs an [Op], and then builds a new expression indexed by a natural number.

  In the latter case, we think of the index provided to continuation [k] as the result of computing [op].

 *)

Inductive Expr (Op : Type) :=
| Val (n : nat)
| Do (op : Op) (k : nat -> Expr Op).
Arguments Val {Op} n.
Arguments Do {Op} op k.

(* ----------------------------------------------------------------- *)
(** *** Instantiating [Op] *)

(** To recover the expressiveness of the language from before, let us define an
operation to perform additions: it takes two [nat]s as arguments. Though we think
of [Plus] as the the operations that sums its inputs, note that this definition
doesn't actually say anything about that.  This is still just _syntax_ for
the operation. *)
Inductive Plus := add (n1 n2 : nat).

(** It looks a bit weird, but we can write the [Expr] summing 3 and 4 and
returning the result as follows:  *)
Example e : Expr Plus := Do (add 3 4) (fun n => Val n).

(** The next thing we wanted to do is to define an evaluation function. We could
do it directly: *)
Fixpoint eval_naive (t : Expr Plus) : nat :=
  match t with
  | Val n => n
  | Do (add n m) k => eval_naive (k (n + m))
  end.

Eval compute in (eval_naive e).
(** ==> [7 : nat] *)

(** But if we did that, we would have a weirder syntax, and gained nothing. *)

(** Instead, we can notice that we can abstract away the concrete
computation that we perform to realize our operation.  Consider an expression
over an arbitrary signature [Op], rather than specifically [Plus], and assume
that you are given a function that knows how to evaluate any such operation into
a [nat].  *)

Fixpoint fold_eval {Op} (h : Op -> nat) (t : Expr Op) : nat :=
  match t with
  | Val n => n
  | Do op k => fold_eval h (k (h op))
  end.

(** Then we can, in particular, define _in isolation_ what we do for [Plus] *)
Definition hplus : Plus -> nat :=
	fun '(add n1 n2) => n1 + n2.

(** And we obtain our evaluation function by feeding [hplus] to our generic
 folding function.
*)
Definition evalp := fold_eval hplus.
Eval compute in evalp e.
(** ==> [7 : nat] *)

(** Before moving further, let's introduce a few constructions and notations
 to hide the syntactic awkwardness.

 First, note that we can build the sequence of two computations quite
 easily: our terms look like abstract syntax trees, we can crawl them until we find a
 value at a leaf, and we use it as the argument to the end of the computation.
 *)
Fixpoint seq {Op} (e : Expr Op) (k : nat -> Expr Op) : Expr Op :=
  match e with
  | Val n   => k n
  | Do op h => Do op (fun n => seq (h n) k)
  end.

Notation "x <- t1 ;; t2" := (seq t1 (fun x => t2))
  (at level 61, t1 at next level, right associativity).

(** Next, we often simply want to do an operation, and finish the computation
   with whatever value the operation resulted in.  The [trigger] function
   capture this "minimal effectful computation".  *)

Definition trigger {Op} (op : Op): Expr Op :=
  Do op (fun x => Val x).

(** With this, we can already write examples a bit more comfortably: *)
Example e1 : Expr Plus :=
  trigger (add 3 4).

Eval compute in evalp e1.
(** ==> [7 : nat] *)

Example e2 : Expr Plus :=
	x <- trigger (add 1 2);;
	y <- trigger (add 3 4);;
	trigger (add x y).

Eval compute in evalp e2.
(** ==> [10 : nat] *)

(** Alright, but we claimed that we would be able to extend our language without
breaking what we did so far!  To see how we can achieve this, let's now define a
signature for a substraction operation.  *)

Inductive Minus := sub (n1 n2 : nat).

(** Its meaning can be defined in isolation as before *)
Definition hminus : Minus -> nat :=
  fun '(sub n1 n2) => n1 - n2.

(** And used to evaluate expressions performing subtractions: *)
Definition evalm := fold_eval hminus.

Example e3 : Expr Minus :=
  trigger (sub 4 3).

Eval compute in evalm e3.
(** ==> [1 : nat] *)

Example e4 : Expr Minus :=
	x <- trigger (sub 2 1);;
	y <- trigger (sub 6 3);;
	trigger (sub y x).

Eval compute in evalm e4.
(** ==> [2 : nat] *)

(** But of course we don't want to be able to work with either expressions with
 just additions, or expressions with just substractions: we want to be able to
 combine both operations!  To do that, we will observe that we can combine both
 expressions by working with the coproduct of the signatures, i.e., here the sum
 type.  *)
Notation "Op1 +' Op2" := ((Op1 + Op2)%type) (at level 10).

(** An expression of type [Expr (Plus +' Minus)] can perform _both_ operations *)

(** Furthermore, we can combine two _handlers_ generically: *)
Definition hsum {Op1 Op2} (h1 : Op1 -> nat) (h2 : Op2 -> nat)
	: Op1 +' Op2 -> nat :=
	fun op => match op with
	| inl op => h1 op
	| inr op => h2 op
	end.
Notation "h1 ⊕ h2" := (hsum h1 h2) (at level 10).

(** We hence can evaluate mixed expressions as well without any additional
 	 definitions *)
Definition eval := fold_eval (hplus ⊕ hminus).

Example e5 : Expr (Plus +' Minus) :=
	x <- trigger (inr (sub 2 1));;
	y <- trigger (inr (sub 6 3));;
	trigger (inl (add x y)).

Eval compute in eval e5.
(** ==> [4 : nat] *)

(** *** Using explicit [inl] and [inr] is painful, so...*)

(** Writing computations got slightly worse however: we now need to carefully
tag our operations depending on their position in the signature. We alleviate
this pain by asking Coq to find these tags itself. *)

Class Subop Op1 Op2 := inject : Op1 -> Op2.

#[local] Instance subop_refl Op : Subop Op Op :=
  fun x => x.

#[local] Instance subop_left Op1 Op2 :
  Subop Op1 (Op1 +' Op2) := inl.

#[local] Instance subop_right Op1 Op2 Op3 `{Subop Op1 Op3}
  : Subop Op1 (Op2 +' Op3)
  := fun e => inr (inject e).

Notation trigger' e := (trigger (inject e)).

Example e5' : Expr (Plus +' Minus) :=
	x <- trigger' (sub 2 1);;
	y <- trigger' (sub 6 3);;
	trigger' (add x y).

Eval compute in (eval e5').
(** ==> [4 : nat] *)

(** And finally with a little bit of additional notations,
   we get an acceptable syntax *)
Notation add' n m := (trigger' (add n m)).
Notation sub' n m := (trigger' (sub n m)).

Example e5'' : Expr (Plus +' Minus) :=
	x <- sub' 2 1;;
	y <- sub' 6 3;;
	add' x y.

Eval compute in eval e5''.
(** ==> [4 : nat] *)

(** Note that, instead of seeing [Expr Op] as our programming language itself,
   we can see it alternatively as a _semantic domain_ for our original syntax.
*)
Inductive ExprAST : Set :=
| ValAST (n : nat)
| AddAST (e1 e2 : ExprAST)
| MinusAST (e1 e2 : ExprAST).

Fixpoint repr (e : ExprAST) : Expr (Plus +' Minus) :=
  match e with
  | ValAST n => Val n
  | AddAST e1 e2 =>
      x <- repr e1;;
      y <- repr e2;;
      add' x y
  | MinusAST e1 e2 =>
      x <- repr e1;;
      y <- repr e2;;
      sub' x y
  end.
Definition sem (e : ExprAST) : nat := eval (repr e).

Example e6 : ExprAST :=
  MinusAST (AddAST (ValAST 3) (ValAST 4)) (ValAST 5).

Eval compute in (sem e6).
(** ==> [2 : nat] *)

End FreeExpr.

Module Free.

(* ================================================================= *)
(** ** Free Monads *)

(** While our datatype [Expr] worked out, it is rather specific: we can extend
our language, but only with operations whose meaning can be captured by a [nat]:
this is encapsulated by the fact that the continuation to the [Do] constructor
expects a [nat].  Of course a language that goes beyond a simple calculator
performs operations of all sorts of different nature.

We therefore generalize our approach by asking the operations to statically
specify what kind of answer they expect from the environment: [E] is now a
family of types.  Furthermore, we also allow for computations returning other
values than [nat]s.  *)

Inductive FFree (E : Type -> Type) (R : Type) : Type :=
| Ret (x : R)
| Do {X} (op : E X) (k : X -> FFree E R).

Arguments Ret {E R} x.
Arguments Do {E R X} op k.

(** Note that [op] is now characterized by an indexed type [E], and [op : E X]
means that, semantically, [op] produces an [X] (which will be fed to the
continuation [k]).
*)

(* ----------------------------------------------------------------- *)
(** *** Operations, dependently *)

(** In this format, the signature of the addition operation looks like the following: *)
Inductive Plus : Type -> Type :=
  add (n1 n2 : nat) : Plus nat.

(** Or, for Boolean operations:  *)
Inductive BoolOp : Type -> Type :=
| or  (b1 b2 : bool) : BoolOp bool
| not (b : bool) : BoolOp bool.

(** The implementation of an operation is now aware of the type it must implement. *)

Definition hplus : forall X, Plus X -> X :=
	fun _ '(add n1 n2) => n1 + n2.

Definition hbool : forall X, BoolOp X -> X :=
	fun _ op => match op with
	| or b1 b2 => orb b1 b2
	| not b => negb b
	end.

Fixpoint fold_pure {E R} (h : forall X, E X -> X) (t : FFree E R) : R :=
  match t with
  | Ret x => x
  | Do op k => fold_pure h (k (h _ op))
  end.

(** We can rebuild the machinery from before, but this time [seq] _is_ the [bind] of a monad [FFree E]. *)
Fixpoint seq {E X Y} (e : FFree E X) (k : X -> FFree E Y) : FFree E Y :=
  match e with
  | Ret x   => k x
  | Do op h => Do op (fun n => seq (h n) k)
  end.

#[export] Instance FFreeM {E} : Monad (FFree E) :=
{|
    ret := @Ret E
  ; bind := @seq E
|}.

(* ----------------------------------------------------------------- *)
(** *** Equivalence of [FFree E] computations *)

(** We define an appropriate notion of equivalence.

Note that the continuations are required to be _extensionally equivalent_.  *)

Inductive eq_FFree {E X} : FFree E X -> FFree E X -> Prop :=
| eq_Ret : forall (x:X), eq_FFree (Ret x) (Ret x)
| eq_Do  : forall {Y} (op : E Y) (k1 k2 : Y -> FFree E X)
             (Heq: forall (y1 y2:Y), y1 = y2 -> eq_FFree (k1 y1) (k2 y2)),
    eq_FFree (Do op k1) (Do op k2).

(** Use straightforward induction to prove that [eq_FFree] is an equivalence relation.

    The only wrinkle is that, due to the existential type for the return
of [op] in the [Do] constructor, we need to use [inj_pair2], which lets us extract
information about the equality of the components of types of the form [existT P X v].  *)
#[export]
Instance eq_FFree_reflexive : forall {E X}, Reflexive (@eq_FFree E X).
Proof.
  intros E X e.
  induction e; constructor; auto.
  intros; subst. apply H.
Qed.

#[export]
Instance eq_FFree_symmetric : forall {E X}, Symmetric (@eq_FFree E X).
Proof.
  intros E X e.
  induction e; intros f HF; inversion HF; subst; auto.
  apply inj_pair2 in H2. subst.
  apply inj_pair2 in H3. subst.
  constructor. intros y1 y2 EQ. subst.
  eapply H in Heq. apply Heq. reflexivity.
Qed.

#[export]
Instance eq_FFree_transitive : forall {E X}, Transitive (@eq_FFree E X).
Proof.
  intros E X e1.
  induction e1; intros e2 e3 HF HF2.
  - inversion HF. subst. inversion HF2. subst. constructor.
  - inversion HF. subst.
    apply inj_pair2 in H2. subst.
    apply inj_pair2 in H3. subst.
    inversion HF2. subst.
    apply inj_pair2 in H2. subst.
    apply inj_pair2 in H3. subst.
    constructor.
    intros y1 y2 EQ. subst.
    eapply H; auto.
Qed.

#[local] Instance eqM_FFree {E} : EqM (FFree E) :=
  fun A => (@eq_FFree E A).

#[local] Instance eqM_FFree_Equiv {E} : EqMEquivalence (FFree E).
Proof.
  constructor; typeclasses eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Monad Laws for [FFree E] : *)

(** Next we prove the monad laws, but they follow straightforwardly by
induction: *)
#[local]  Instance eqm_FFree_monad_laws {E} : MonadLaws (FFree E).
Proof.
  constructor.
  - intros A B C ma.
    induction ma; intros; simpl in *.
    + reflexivity.
    + constructor. intros. rewrite H.
      subst.
      reflexivity.
  - intros A B C ma.
    reflexivity.
  - intros.
    induction m; intros; simpl in *.
    + reflexivity.
    + constructor. intros. subst. rewrite H. reflexivity.
  - repeat red. intros A B x.
    induction x; intros y Heq k1 k2 HK.
    + inversion Heq. subst.
      simpl. apply HK.
    + inversion Heq.  subst.
    apply inj_pair2 in H2. subst.
    apply inj_pair2 in H3. subst.
    simpl.
    constructor.
    intros. subst.
    apply H. apply Heq0.
    simpl. reflexivity.
    assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Disjoint sum of Indexed Types *)

(** Now that our operation types are indexed by their return types, we need to
provide an appropriate notion of "disjoint union": *)

Inductive sumi (E1 E2 : Type -> Type) (X : Type) : Type :=
	| inli (_ : E1 X)
	| inri (_ : E2 X).
Arguments inli {E1 E2} [X].
Arguments inri {E1 E2} [X].

Notation "Op1 +' Op2" := (sumi Op1 Op2) (at level 10).

(** We can also "sum" _handlers_: *)

Definition hpure_sum {Op1 Op2} (h1 : forall X, Op1 X -> X) (h2 : forall X, Op2 X -> X)
	: forall X, (Op1 +' Op2) X -> X :=
	fun _ op => match op with
	| inli op => h1 _ op
	| inri op => h2 _ op
	end.

(* ----------------------------------------------------------------- *)
(** *** Implicit injections

    And, using similar typeclass machinery to what we saw previously,
use inference to [inject] an [op : E X] into, e.g., a sum [(E +' F) X].    *)

Class SubE (Op1 Op2 : Type -> Type) := inject : forall X, Op1 X -> Op2 X.
Arguments inject {Op1 Op2 SubE} [X].

#[export] Instance subop_refl Op : SubE Op Op := fun X x => x.
#[export] Instance subop_left Op1 Op2 : SubE Op1 (Op1 +' Op2) := inli.
#[export] Instance subop_right Op1 Op2 Op3 `{SubE Op1 Op3} : SubE Op1 (Op2 +' Op3) :=
	fun X e => inri (inject e).

(** Which allows us to define a generic [trigger] operation: *)

Definition trigger_ {E X} (e : E X) :=
	Do e (fun x => Ret x).
Notation trigger e := (trigger_ (inject e)).

(* ----------------------------------------------------------------- *)
(** *** Putting it all together: *)

Example e1 : FFree (Plus +' BoolOp) nat :=
  b <- trigger (or true false);;
  if (b : bool)
  then trigger (add 10 10)
  else trigger (add 2 2).

Eval compute in fold_pure (hpure_sum hplus hbool) e1.
(** ==> [20 : nat] *)

(* ----------------------------------------------------------------- *)
(** *** Recap: *)

(**
 - Use the [FFree E] monad to define computations parameterized by "syntax" for operations like [Plus].

 - Define the semantics of those operations separately using _handlers_

 - Use [fold_pure] as an _interpreter_ to evaluate the handlers
*)

(** Aside: Technically, [FFree E] is a _freer_ monad, not the "Free" monad. *)

(* ----------------------------------------------------------------- *)
(** *** Impure Interpretations *)

(** Now imagine that we want to extend our language so that it manipulates a memory cell.
We can continue and follow our line of intuitions so far: we define the signature of
the operations interacting with this cell: one can either read it, or write to it.
Notice the different types of each operations:
  - When reading, one expects to receive a [nat] back
  - When writing, all one expects is for the write to happen, the use does not wait for
    a meaningful answer: the return type is hence simply [unit].
*)

Inductive Cell : Type -> Type :=
| Rd : Cell nat
| Wr (n : nat) : Cell unit.

(** We can, of course, write computations much in the same way as before over
this signature, and combine it with the previous ones if we wish so.  *)

Example double : FFree (Plus +' Cell) unit :=
  x  <- trigger Rd;;
  xx <- trigger (add x x);;
  trigger (Wr xx).

(** However, we are stuck when it comes to implement our Cell operations.
    The [fold_pure] function is expecting us to essentially provide two functions:

	 - h_read  : nat

	 - h_write : nat -> unit

    But this seems nonsensical: we need access to the cell itself in order to
implement these operations. This comes from the fact that we are now seeking to
model an _impure_ operations: we will bring monads to the rescue to do so.  *)

(* ----------------------------------------------------------------- *)
(** *** Monadic [fold], or Monadic Interpreters *)

(** First: some handy notation for "polymorphic" functions: *)
Notation "E ~> F" := (forall X, E X -> F X) (at level 30).

(** We can now redefine our folding function over monadic implementations of our effects *)

Fixpoint fold {E M} `{Monad M} (h : E ~> M) [R] (t : FFree E R) : M R :=
  match t with
  | Ret x => ret x
  | Do op k => x <- h _ op;; fold h (k x)
  end.

(** The type of this handler returns a computation in the [state] monad: *)
Definition hcell : Cell ~> state nat :=
  fun _ e =>
    match e with
    | Wr n => put n
    | Rd   => get
    end.

(** Intuitively, this means that we can _interpret_ the operations [Wr] and [Rd]
by their semantic counterpart. *)

(* ----------------------------------------------------------------- *)
(** *** Lifting computations

    We do have to _lift_ the pure handler [hplus] into the [state] monad. *)

(** But, this can be alleviated with an additional piece of technology that we will introduce later. *)

Definition hplusS : Plus ~> state nat :=
  fun _ e => ret (hplus _ e).

Definition hsum {Op1 Op2 M : Type -> Type} (h1 : Op1 ~> M) (h2 : Op2 ~> M) : Op1 +' Op2 ~> M :=
  fun _ op => match op with
	   | inli op => h1 _ op
	   | inri op => h2 _ op
	   end.

Notation "h1 ⊕ h2" := (hsum h1 h2) (at level 10).

(**  Recalling our example from earlier:

Example double : FFree (Plus +' Cell) unit :=
  x  <- trigger Rd;;
  xx <- trigger (add x x);;
  trigger (Wr xx).
*)

(** We can now run it in the [state] monad: *)

Eval compute in fold (hplusS ⊕ hcell) double 16.
(** ==> [(32, tt) : nat * unit] *)

Eval compute in (fold (hplusS ⊕ hcell) (double ;; trigger Rd) 42).
(** ==> [(84, 84) : nat * unit] *)

Lemma bind_trigger {E X Y} (op : E X) (k : X -> FFree E Y):
  x <- trigger op ;; k x ≈ Do op k.
Proof.
  reflexivity.
Qed.

Section Fold_Theory.
  Context {E M : Type -> Type}.
  Context {MM : Monad M} {eqM : EqM M} {equivM : @EqMEquivalence M eqM} {ML : MonadLaws M}.
  Variable (h : E ~> M).

  Lemma fold_ret {X} (x : X) :
    fold h (ret x) ≈ ret x.
  Proof.
    now reflexivity.
  Qed.

  Lemma fold_trigger {X} (op : E X) :
    fold h (trigger_ op) ≈ h _ op.
  Proof.
    cbn.
    now rewrite bind_ret_r.
  Qed.

  Lemma fold_bind {X Y} (m : FFree E X) (k : X -> FFree E Y) :
    fold h (bind m k) ≈ bind (fold h m) (fun x => fold h (k x)).
  Proof.
    induction m.
    cbn; now rewrite bind_ret_l.
    cbn.
    rewrite bind_associativity.
    apply Proper_bind.
    reflexivity.
    intros ?.
    apply H.
  Qed.

End Fold_Theory.

Module FreeInstances.
  #[export] Existing Instance eqM_FFree.
  #[export] Existing Instance eqM_FFree_Equiv.
  #[export] Existing Instance eqm_FFree_monad_laws.
End FreeInstances.

End Free.

(* ================================================================= *)
(** ** Next: [ITrees] *)

(** At this point, are we ready to tackle  [ITrees] *)

(* 2024-06-13 11:26 *)
