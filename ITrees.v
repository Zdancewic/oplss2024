Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From RIP Require Import Utils Monads.

Notation "E ~> F" := (forall X, E X -> F X) (at level 99, right associativity, only parsing).

Variant sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
| inl1 (_ : E1 X)
| inr1 (_ : E2 X).
Arguments inr1 {E1 E2} [X].
Arguments inl1 {E1 E2} [X].

(** An infix notation for convenience. *)
Notation "E1 +' E2" := (sum1 E1 E2)
  (at level 60, right associativity) : type_scope.

(* ----------------------------------------------------------------- *)
(** *** Note

    NOTE This file recapitulates definitions that are given in the [coq-itree]
library. If you want to prove things about itrees use [Import ITree] instad. *)

(* ----------------------------------------------------------------- *)
(** *** Introduction *)

(** We define in this section the type of *interaction trees*.  Elements of
this type will intuitively each model a computation.  The computations we
consider are dubbed as potentially *interactive*: they may, during their
execution, trigger certain *events*, requesting the environment to process such
events, and return a value in exchange.  Our data-type of interaction trees is
hence parameterized by two pieces of data: *)

(**
	- the set [E] of events that the computation may perform the type [R] of
	- values that the computation may return

  Events are a *family of types*, a parameter of type [Type -> Type].  The reason
  for this slightly complexe type is that each event will specify the kind of
  answer it expects from the environment.  An event [e] may therefore for
  instance be of type [E nat] if it expects the environment to answer it with a
  [nat].

  As an early intuition, imagine that you want to model a computation with
  Input/Output interaction, i.e. that may print integers in your terminal, and
  may stop and request from the user to input an integer.  You would hence use a
  domain of interaction [E] that would contain: - an [Ouput n] event that would
  take a [nat] as argument. Since we don't expect any particular answer in
  exchange, a simple acknowledgement that the effect has been performed will do:
  it will be of type [E unit] - an [Input] event. This time, we are waiting for
  a meaningful answer, this event would have type [E nat].
*)

(* ----------------------------------------------------------------- *)
(** *** The [Free] monad: *)

(** Recall the definition of [FFree]:

Inductive FFree (E : Type -> Type) (R : Type) : Type :=
| Ret (x : R)
| Do {X} (op : E X) (k : X -> FFree E R).
*)

Module ITreeAlternative.

(* ----------------------------------------------------------------- *)
(** *** A Coinductive Version of FFree *)

  CoInductive itree (E : Type -> Type) (R : Type) :=
  | Ret (r:R)
  | Tau (t : itree E R)
  | Vis  {X:Type} (e: E X) (k : X -> itree E R).

(** Represents computations that can:
  - Terminate by returning a value of type [R]
  - Perform an internal step of computation, before continuing to compute
  - _Trigger_ an event [e] expecting a certain answer of type [X]. It then continues to compute, but must
    be ready to do so no matter what is the environment's answer: it therefore takes
    a continuation indexed by [X]
*)

End ITreeAlternative.

Section itree.

  (** *** (ASIDE) The "real" Interaction Trees data-structure *)

(** In practice, we use a slightly different definition, where
the type [itree] is defined as the final coalgebra ("greatest fixed point") of
the functor [itreeF]:
*)

(** Our two parameters, domain of events and return type *)
  Context {E : Type -> Type} {R : Type}.

  Variant itreeF (itree : Type) :=
    | RetF (r : R)
    | TauF (t : itree)
    | VisF {X : Type} (e : E X) (k : X -> itree)
  .

  (** Note: this is a _coinductive_ definition *)
  CoInductive itree : Type := go
  { _observe : itreeF itree }.

(** A primitive projection, such as [_observe], must always be
      applied. To be used as a function, wrap it explicitly:
      [fun x => _observe x] or [observe] (defined below).
*)

End itree.

Arguments itree : clear implicits.
Arguments itreeF : clear implicits.

Definition observe {E R} (t : itree E R) : itreeF E R (itree E R) := @_observe E R t.

Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Notation itree' E R := (@itreeF E R (itree E R)).
Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

Ltac genobs x ox := remember (observe x) as ox.
Ltac desobs x    := destruct (observe x).

(* ----------------------------------------------------------------- *)
(** *** First examples of [itree] computations *)
Section FirstExamples.

(**  We don't have much facilities yet to define our computations,
     but we can already program a few clumsy examples. *)

  (** We first define the Input/Output events informally described above *)
  Variant IOE : Type -> Type :=
    | Output (n : nat) : IOE unit
    | Input            : IOE nat.

  (** Here is a very boring computation that simply returns 1789 *)
  Definition aux_armes : itree IOE nat := Ret 1789.

  (** And one that requests a value from the user and doubles it *)
  Definition double : itree IOE nat :=
    Vis Input (fun n => Ret (2 * n)).

  (** Of course, we can reap the benefits of coinductives: our computations
    do not need to terminate! Here is a computation that repeatedly asks for integers before
    printing them back
   *)
    CoFixpoint echo : itree IOE void :=
    Vis Input (fun n => Vis (Output n) (fun _ => echo)).

  (** *** Silent Divergence *)

  (** And finally, an important: the silently diverging computation *)
  CoFixpoint spin_spec : itree IOE void :=
    Tau spin_spec.

  (**
     We have typed these last two computations with the empty type
     [void] as return type.
     What do you think of the set of computations of type [itree IOE void]?
     Note that [echo] and [spin] can actually be defined at arbitrary return types.
   *)
    CoFixpoint spin {E R} : itree E R := Tau spin.

  (** *** Failure *)
  (** Consider now an event whose return type is empty *)

  Variant Empty : Type -> Type :=
  | empty : Empty void.

  (** This event corresponds to requesting an impossible task from the
    environment, and can be used to model failure.
    In particular, it can be cast at any return type, so that we can
    sneak in failure in lieu of any computation!
   *)
    Definition fail {R} : itree Empty R :=
    Vis empty (fun x : void => match x with end).

End FirstExamples.

(** If we are to write ambitious computations, we would like to
   have a little bit of support to help us code in this strange
   programming language that itrees make.
   First, we are going to define facilities for *sequencing*
   computations: for any fixed domain of events [E], the type
   of computations [itree E] is a *monad*, and hence support
   a [bind] operation.
*)

(** The definition is intuitively quite straightforward:
   we traverse the first tree, and when we reach a leaf,
   we feed the value we find to the continuation and attach
   the resulting leaf.

   We are going to allow ourself one slight subtlety: we can
   notice that the continuation argument remains untouched in
   the co-recursive calls we are planning to make.
   We make this fact more apparent by switching the order of
   the arguments so that it does not even need to be an argument
   of the [cofix].
   For this particular definition it would not be important
   (try yourself!), but it will help soothe the guard condition
   when we will write other [cofix] whose body use [bind] themselves.
*)
(* ----------------------------------------------------------------- *)
(** *** Sequential Composition: *)

(** As with the [FFree] monad, we can define a sequential composition
operation, which looks for all the [Ret x] leaves of the tree and applies a
continuation [k] to build a bigger tree : *)

Definition seq {E : Type -> Type} {T U : Type} (k : T -> itree E U)
  : itree E T -> itree E U :=
    cofix _seq (u : itree E T) : itree E U :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_seq t)
    | VisF e h => Vis e (fun x => _seq (h x))
    end.

(* ----------------------------------------------------------------- *)
(** *** Monad operations *)

(** These ingredients give us all we need to define a monad. *)

(** Return is just [Ret]  *)

(** Bind is just [seq] with the arguments reordered: *)
Definition bind {E : Type -> Type} {T U : Type} (u : itree E T) (k : T -> itree E U)
  : itree E U := seq k u.

(** An elementary [itree] computation emits an event: *)
Definition trigger {E : Type -> Type} {A : Type} (e : E A) : itree E A :=
  Vis e (fun x => Ret x).

Module ITreeNotations.
  Open Scope itree_scope.

  Notation "t1 >>= k2" := (bind t1 k2)
    (at level 58, left associativity) : itree_scope.
  Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))
    (at level 61, t1 at next level, right associativity) : itree_scope.
  Notation "' p <- t1 ;; t2" :=
    (bind t1 (fun x_ => match x_ with p => t2 end))
    (at level 61, t1 at next level, p pattern, right associativity) : itree_scope.
  Notation "t1 ;; t2" := (bind t1 (fun _ => t2))
    (at level 61, right associativity) : itree_scope.
End ITreeNotations.
Import ITreeNotations.

Section MoreExamples.

  (** A computation quadrupling an input *)
  Definition quadruple : itree IOE nat :=
    n <- double;; Ret (2 * n).

  (** Question:
     Define the [fmap] function over itrees: it should apply a pure function
     to the outputs of the computation.
       [fmap {E A B} (t : itree E A) (f : A -> B) : itree E B]
  *)
  Definition fmap {E A B} (f : A -> B) (t : itree E A) : itree E B :=
    x <- t;; Ret (f x).

  (** Question:
      Use your [fmap] to define [ignore], the combinator that
      simply discards the value computed by an itree.
  *)
  Definition ignore {E A} : itree E A -> itree E unit :=
    fun t => fmap (fun _ => tt) t.

  (** Question:
      Define [forever], a combinator taking a computation as
      argument and repeating it infinitely often.
  *)
  Definition forever {E A B} (t : itree E A) : itree E B :=
    cofix forever_t :=
      t;; Tau (forever_t).

End MoreExamples.

(* ================================================================= *)
(** ** Iteration *)

Module Iter.

(** In order to write infinite computations, we write a fixed-point combinator [iter].
  [iter step init] runs [step init], analyses the result and either feeds the new value back
  to the loop body, or terminates with the result.
*)
Definition iter {E : Type -> Type} {R I: Type}
           (step : I -> itree E (I + R)) : I -> itree E R :=
  cofix iter_ init :=
    (* one step of the loop *)
    lr <- step init;;

    match lr with
    (* got updated state => jump back into loop *)
    | inl updated => Tau (iter_ updated)

    (* got a final result => terminate *)
    | inr result => Ret result
    end.

(** Note: the backwards jump is guarded by [Tau] *)

(* ----------------------------------------------------------------- *)
(** *** Example: *)

(** Define the factorial [fact n] using the [iter] combinator. *)
Definition fact (n : nat) : itree voidE nat :=
 iter  (fun '(acc,n) =>
          match n with
          | O => Ret (inr acc)
          | S m => Ret (inl (n * acc, m))
end) (1,n).

(* ----------------------------------------------------------------- *)
(** *** "Running" an itrees computation *)

(** As we have seen, we cannot "run" our cofix-points directly inside of Coq.
  We could however extract them to OCaml to obtain potentially diverging computations.
  Alternatively, we can use some fuel to force their finite unfolding.

    But, we can provide "fuel" that can be burned to force it: *)

Fixpoint burn (n : nat) {E R} (t : itree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | TauF t' => burn n t'
    end
  end.

(** You can test that your factorial computes what it should: *)
Eval compute in burn 10 (fact 6).
(** ==> [Ret 720 : itree voidE nat] *)

(**  Imperative loops are particular patterns of iteration: they do not
carry any accumulator.  We can capture this pattern with a [repeat]
combinator.  *)

Definition repeat {E} (step : itree E (unit + unit)) : itree E unit :=
  iter (fun _ => step) tt.

(* ----------------------------------------------------------------- *)
(** *** Mutual recursion *)

(** Although [iter] is sufficient to write tail-recursive functions like factorial, we can also define general recursion operators. *)

(** Interpret an itree in the context of a mutually recursive
    definition ([ctx]). *)
Definition interp_mrec {D E : Type -> Type}
    (ctx : D ~> itree (D +' E)) : itree (D +' E) ~> itree E :=
fun R =>
iter (fun t : itree (D +' E) R =>
 match observe t with
 | RetF r => Ret (inr r)
 | TauF t => Ret (inl t)
 | VisF (inl1 d) k => Ret (inl (ctx _ d >>= k))
 | VisF (inr1 e) k => Vis e (fun x => Ret (inl (k x)))
 end).

Arguments interp_mrec {D E} ctx [X].

(** Unfold a mutually recursive definition into separate trees,
resolving the mutual references. *)
Definition mrec {D E : Type -> Type}
      (ctx : D ~> itree (D +' E)) : D ~> itree E :=
fun R d => interp_mrec ctx (ctx _ d).

Arguments mrec {D E} ctx [X].

Inductive callE (A B : Type) : Type -> Type :=
  | Call : A -> callE A B B.

Arguments Call {A B}.

Definition calling' {A B} {F : Type -> Type}
             (f : A -> itree F B) : callE A B ~> itree F :=
    fun _ e =>
      match e with
      | Call a => f a
      end.

(** Interpret a single recursive definition. *)
Definition rec {E : Type -> Type} {A B : Type}
           (body : A -> itree (callE A B +' E) B) :
  A -> itree E B :=
  fun a => mrec (calling' body) (Call a).

Definition call {E A B} (a:A) : itree (callE A B +' E) B := trigger (inl1 (Call a)).

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

Definition rec_fix {E : Type -> Type} {A B : Type}
            (body : (A -> itree (callE A B +' E) B) -> (A -> itree (callE A B +' E) B))
  : A -> itree E B
   := rec (body call).

Notation "'rec-fix' f a := g" := (rec_fix (fun f a => g))
   (at level 200, f name, a pattern).

Definition fact_body (x : nat) : itree (callE nat nat +' voidE) nat :=
  match x with
  | 0 => Ret 1
  | S m =>
    y <- call m ;;  (** Recursively compute [y := m!] *)
    Ret (x * y)
  end.

(** The factorial function itself is defined as an ITree by "tying
    the knot" using [rec].
 *)
Definition factorial (n : nat) : itree voidE nat :=
  rec fact_body n.

Eval compute in burn 10 (factorial 6).

End Iter.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Indexed.Relation.

Import Monads.

(* ================================================================= *)
(** ** Interpretations *)

(** An event handler [E ~> M] defines a monad morphism
    [itree E ~> M] for any monad [M] with a loop operator. *)

(** This is just the monadic "fold" operation specialized to
   itree. *)

Definition interp {E M : Type -> Type}
           {MF : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : E ~> M) :
  itree E ~> M := fun R =>
  iter (fun t =>
    match observe t with
    | RetF r => ret (inr r)
    | TauF t => ret (inl t)
    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
    end).

(* ================================================================= *)
(** ** Stateful Interpretations *)

(** Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

Definition interp_state {E M S}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter M} (h : E ~> stateT S M) :
  itree E ~> stateT S M := interp h.

(* 2024-06-13 11:26 *)
