Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith Lia Program.Basics.
From Coq Require Import Logic.FunctionalExtensionality Morphisms RelationClasses.
From Coq Require Import List FunctionalExtensionality.
Import ListNotations.


(* ================================================================= *)
(** ** Introduction to Monads *)

(** One of the most common ways to combine computational behaviors is
_sequencing_ them one after another.  As programmers, we are so familiar with
this notion of composition that it almost doesn't deserve a second thought.
However, as we will see below, it is very useful to _generalize_ the idea of
sequential composition -- doing so will give us a framework for defining a wide
class of computational behaviors, all of which share the basic idea of "doing
something and then doing something afterwards".

This common abstraction is called a [Monad].  A [Monad] is just a datatype that
can represent some kind of computational behavior that supports a well-behaved
notion of sequential composition. In this chapter, we will explore the basic
ideas behind the [Monad] abstraction and see how they can be used to model
several kinds of computational behavior: imperative state, exceptions, and
nondeterminism.  *)


(* TODO: Add a bit more background and pointers to the literature.

- monads have an "air of mystery"
- they are extensively used in Haskell, but other FPs too (OCaml)

*)

(* ================================================================= *)
(** ** Modeling Imperative Programs *)

(** As a warmup, let's start with the idea familiar from imperative programming.
Recall the Imp language semantics from [Imp], which builds sequential
composition into the syntax of the programming language. In the command [c1;c2],
the semicolon '[;]' means to first do [c1] and then do [c2].  It is given
meaning by the following rule of the operational semantics:

Inductive ceval : com -> mem -> mem -> Prop :=
  ...
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
*)
(** This rule says that, starting from memory [st], if [c1] runs to produce memory
[st'] and we run [c2] starting in [st'], the result of the sequential
composition will be [st''].  This style of (large-step) operational semantics
defines the computational behavior of an Imp program as a "step" relation, which
is a Coq proposition about syntax.

Looking at the type of [ceval] suggests that we could, instead of describing the
behavior of a command as a _relation_ among a command and two memories, simply try
to model the semantics of an Imp program as a _function_ from [mem] to
[mem].  That is, we could replace [ceval] with a function, called [denote],
that takes in the syntax of an Imp command and gives back a function on memories.
Then [denote c : mem -> mem] and we can "run" the command [c] starting from
an initial mem [st] by doing [denote c st].  Note that, in contrast to the
relational operational semantics, the meaning of a command is defined in terms
of a Coq function.  Here, we use the term "denote" as an allusion to
"denotational semantics", a style of semantics that builds a mathematical model
of a programming language _compositionally_ by induction on the syntax.

If we could make this approach work, then the meaning of sequential composition
can be defined as shown below:*)

(**

Fixpoint denote (c:com) : mem -> mem :=
   match c with
   | ... (* omitted *)

   | c1 ; c2 => fun st =>
                let st'  := denote c1 st in
                let st'' := denote c2 st' in
                st''
   end.
*)
(** In the code above, we have used [let] to name the intermediate results [st']
and [st''] -- keep this in mind as we proceed, since one of the key ideas of
Monads is generalizing this [let]-binding operation.  However, it is also
enlightening to see that we could have written the case more succinctly as

   | c1 ; c2 => fun st => (denote c2 (denote c1 st))

Or, recalling that [∘] stands for function composition, even as:

   | c1 ; c2 => (denote c2) ∘ (denote c1)
*)
(** There are a couple nice properties of this way of defining the semantics of
Imp.  First, like the large-step operational semantics, we see that the
sequential composition of Imp commands is given by induction on the structure of
the term, i.e., the meaning of [c1; c2] is defined from the meaning of [c1] and
[c2] separately.  This enables easy proofs by induction on the structure of the
syntax.  (In contrast, small step semantics often don't have this property,
since, for example, the semantics for [while b do c end] is not defined purely
in terms of the body [c].) Second, and unlike the large-step operational
semantics, since the command semantics are _functions_, they can be manipulated
as any other Coq function, including evaluating them using [Eval compute in ...]
or by extracting them to OCaml code.  That means that this style of semantics is
_executable_, a useful property for testing semantics or even implementing real
systems.  Finally, we will see throughout the rest of this Volume that this
style of semantics is easily extensible and can deal with many kinds of effects.
*)
(** Unfortunately, there is also a glaring problem for defining the full Imp
semantics this way: it doesn't work!  The problem is that an Imp program can
diverge, which means that, since Coq functions of type [mem -> mem] are
_total_ (i.e., defined everywhere), it is not possible to use the type [mem ->
mem] to give a correct account of possibly looping programs; for some Imp
programs there is no final [mem] that is produced.  The relational model
sidesteps the issue by exploiting _partiality_ of the relation (it isn't defined
for all programs), but for large-step operational semantics, this comes at a the
cost of not (easily) being able to simultaneously model divergence and other
effects like I/O.  The denotational/monadic approach does have a good solution
to these issues, which we will see later in [ITrees].

For now, however, the idea of using Coq functions of type [mem -> mem] to
represent imperative programs that can modify memory is still appealing.
Moreover, thinking about how to generalize the situation above, which uses
[let]-binding in conjunction with function composition, will lead us to monads,
a general mechanism for representing many different kinds of effects, including
state, divergence, and I/O.  So let us continue to dive into modeling imperative
programs by functions that update mem.  *)

(* ================================================================= *)
(** ** Simple States *)
Module SimpleStates.

  (** As a first step, let us move away from the "complex" states of Imp, which
are maps from (global) program variables to their values.  Instead, let us think
about how to model a single mutable cell that stores a natural number.  The
"state transformer" semantics of Imp is a function of type [state -> state], and
we can think of such a function as respresing an stateful computation.  With
just one cell, a computation that (possibly) updates the cell can be represented
simply as a function of type [nat -> nat].  For example, a computation that
increments the value of the cell is: *)

  Definition inc_cell : nat -> nat :=
    fun (cell_value:nat) => 1 + (cell_value).

(** Because this stateful computations are modeled as Coq functions, we can
"run" it by applying the function to the initial value for the
cell.  For instance, if cell initially holds the value [2], we have: *)

  Eval compute in (inc_cell 2).
  (** ==> [3 : nat] *)

  (** Now suppose we want to model an imperative function that, in addition to
potentially mutating the cell contents, also takes in some extra input.  For
example, we can implement a function that increments the cell contents only if
an extra input of type [bool] is [true] as follows: *)
  Definition inc_cell_cond : bool -> (nat -> nat) :=
    fun b cell_value => if b then inc_cell cell_value else cell_value.

  Eval compute in (inc_cell_cond true 2).
  (** ==> [3 : nat] *)
  Eval compute in (inc_cell_cond false 2).
  (** ==> [2 : nat] *)

  (** (Aside) Note that the type [bool -> (nat -> nat)] is isomorphic to [(bool * nat) -> nat],
which makes it clear that this computation takes an extra input.  We prefer the
former, "Curried", form because it will more smoothly generalize to other
situations later. Currying takes a function of type [A * B -> C] and turns it in
to a function of type [A -> (B -> C)]. As an enlightening exercise, you might wish
to write, in Coq, a generic function of type [forall A B C, (A * B -> C) -> (A -> (B ->
C))] to see how that works. *)

  (** Similarly, by adding an extra output, we can model a computation that
inspects the cell contents and returns [true] if the stored value is less than
2: *)
  Definition cell_lt_two : nat -> (nat * bool) :=
    fun '(cell_value) => (cell_value, cell_value <? 2).

  Eval compute in (cell_lt_two 1).
  (** ==> [(1, true) : nat * bool] *)
  Eval compute in (cell_lt_two 2).
  (** ==> [(2, false) : nat * bool] *)

  (** Note that [cell_lt_two] returns [cell_value] _unchanged_ as
part of its result.  This detail is crucial because it enable sequential
composition of "stateful" functions -- because [cell_lt_two] yields the
(unchanged) state, we can use that state in subsequent computations.  For
example, we can sequence a call to the [inc_cell_cond] after [cell_lt_two] like
this: *)
Definition sequence_cell_example : nat -> nat :=
  fun cell_value =>
    let '(intermediate_cell_value, b) := cell_lt_two cell_value in
    let final_cell_value := inc_cell_cond b intermediate_cell_value in
    final_cell_value.

(** We can see here that the result of [cell_lt_two] includes the
[intermediate_cell_value], which is then fed in to [inc_cell_cond] to continue
the computation. Note also that [b], the boolean result from [cell_lt_two], is also
available for use in [inc_cell_cond]. As we will see, setting up this kind of
"plumbing" is common for defining [Monads].

Here, the resulting computation behaves as expected: if we run the example
starting with cells holding values less than 2, the cell is incremented, and
otherwise it is untouched.
*)

Eval compute in (sequence_cell_example 0).
(** ==> [1 : nat] *)
Eval compute in (sequence_cell_example 1).
(** ==> [2 : nat] *)
Eval compute in (sequence_cell_example 2).
(** ==> [2 : nat] *)

End SimpleStates.

(* ----------------------------------------------------------------- *)
(** *** Making the types more uniform. *)
Module NatCell.

(** In the examples above, [inc_cell_cond] and [cell_lt_two] had types of
different shapes: [inc_cell_cond] is an imperative computation with an extra [bool]
_input_, and so has type [bool -> (nat -> nat)] whereas [cell_lt_two] has an extra [bool]
_output_, and so has type [nat -> (nat * bool)].  We can make the situation more uniform
by always taking into account the possibility of an extra input and output and,
at the same time, allowing the input and output to be types other than [bool].  If
a computation _doesn't_ need the extra input or output, we can just use the
trivial [unit] type, whose only value is [tt], instead.

These obeservations lead us to the following definition for a type of
"imperative functions" with access to a mutable [nat] cell: *)

Definition nat_cell_fun A B := A -> (nat -> (nat * B)).

(** We can think of the type [nat_cell_fun A B] as representing an imperative
function of type [A -> B] that also has access to and can modify a mutable cell
of type [nat].  Note that the type [nat_cell_fun A B] itself only mentions [A] and
[B], which is why we can think of this as an "imperative function with input [A]
and output [B]".  *)

(** With a bit of refactoring, we can re-implement [inc_cell], [inc_cell_cond],
and [cell_lt_two] so that they fit this new type: *)

(** [inc_cell_value] only modifies the state, so its input and output types are
both [unit]: *)
Example inc_cell_value : nat_cell_fun unit unit :=
  fun (_:unit) (cell_value:nat) => (1+cell_value, tt).

(** Note that [inc_cell_value] still takes in the [cell_value] as its second
argument -- the [nat_cell_fun] type "hides" the presence of the [nat] input and
output.  This detail is important because it means that, from the outside, the
type [nat_cell_fun] will look more like a function of type [A -> B].  Hiding the
details about how the state is implemented is a step towards generalizing to
other implementations of the same functionality.  For instance, we could have
defined a variant of [nat_cell_fun] as [A -> (nat -> (B * nat))], which swaps the
order of the result tuple.  That variant is equally expressive, but would
require slightly different code. *)

(** The function [inc_cell_cond] takes a [bool] input and produces no output. To
fit it into our new form, we instantiate [nat_cell_fun] so that the input type
is [A = bool] and the output type [B = unit], where [unit] is the "trivial type"
and thus can stand for "no" output. Note that after refactoring
[inc_cell_value], we need to do a bit more work to use it in [inc_cell_cond] --
we again use [let] binding to explicitly "plumb" the current value of the state
through the computation.  *)

Example inc_cell_cond : nat_cell_fun bool unit :=
  fun (b:bool) (cell_value:nat) =>
    if b
    then
      let '(intermediate_cell_value, _) := inc_cell_value tt cell_value in
      (intermediate_cell_value, tt)
    else (cell_value, tt).

(** [cell_lt_two] takes no input and leaves the cell state untouched, but
returns a [bool] based on the value of the cell: *)
Example cell_lt_two : nat_cell_fun unit bool :=
  fun _ (cell_value:nat) =>
    (cell_value, cell_value <? 2).

(** Finally, we can rewrite the [sequence_cell_example] using the new types.
Note that its body has the same structure as the original; the only difference
is to account for the [unit] types. *)

Example sequence_cell_example : nat_cell_fun unit unit :=
  fun (_:unit) cell_value =>
    let '(intermediate_cell_value, b) := cell_lt_two tt cell_value in
    let '(final_cell_value, _) := inc_cell_cond b intermediate_cell_value in
    (final_cell_value, tt).

Eval compute in (sequence_cell_example tt 0).
(** ==> [(1, tt) : nat * unit] *)

Eval compute in (sequence_cell_example tt 1).
(** ==> [(2, tt) : nat * unit] *)

Eval compute in (sequence_cell_example tt 2).
(** ==> [(2, tt) : nat * unit] *)

(** At this point, you might wonder what we have gained by introducing this
extra complexity to the types of these "imperative" functions.  The answer can
be seen in the structure common to the examples above, where we see that an
imperative function of type [A -> B] is represented by [nat_cell_fun A B = A -> nat -> (nat * B)].  By slightly shifting our perspective, we can say that such a
function takes an input of type [A] and produces a _computation_ as a result,
here represented as a function of type [nat -> (nat * B)].  Moreover, the state of
the cell is "plumbed through" a sequential composition of such computations by
[let]-binding the intermediate states along with the intermediate values
produced by the earlier computations (such as the [bool] produced by
[cell_lt_two]).  Finally, note that the computations above end by "returning"
the result of the imperative function paired with the current state of the cell
value.

The idea behind monads is to _abstract_ over these two operations, which, among
other things, will allow us to hide the "plumbing" and write the
[sequence_cell_value] example using notation that is much closer to standard
imperative code.

A monad is just a type that represents a compuation in such a way that it
supports at least these two operations: (1) a [let]-binding sequencing
operation, called [bind], and, (2) the ability to end a sequence by returning a
result, using an operation called [ret].  (These operations also have to behave
well together--i.e., they have to satisfy the "monad laws"--but we defer that
discussion until after we consider some more examples.)

For [nat] cell computations, this leads us to define the following type, which is
describes just the "computation" part of the [nat_cell_fun] definition: *)
Definition nat_cell B := nat -> (nat * B).

(** We can read [nat_cell B] as "an imperative computation that can modify a cell
storing a [nat] and that produces a result of type [B]". This type is our first example
of a monad. *)

(* ----------------------------------------------------------------- *)
(** *** Generalizing [let] *)

(** First, let us see how to generalize [let]-binding.  Consider the use of
  [cell_lt_two] in the composition found in [sequence_cell_example]:*)
(**

    fun cell_value =>
      let (intermediate_cell_value, b) := cell_lt_two tt cell_value in ...body...
*)

(** We see that when we run [cell_lt_two] starting from the initial [cell_value]
it results in an [intermediate_cell_value] along with a result [b].  The
[...body...] of the computation is also a [nat_cell] computation, and we have
[intermediate_cell_value] in hand to pass as the starting value for the cell
when it runs, but it is also, in general, a function of [b].  Therefore, if we
abstract over [cell_lt_two], calling it [m] (for "monadic computation") and
express [...body...] as a [nat_cell] computation that is a function of [b],
calling it [k] (for "continuation") we arrive at this [bind] operation for
[nat_cell] is defined as: *)
Definition nat_cell_bind {A B} (m : nat_cell A) (k:A -> nat_cell B) : nat_cell B :=
  fun cell_state =>
    let '(new_cell_value, returned_a) := m cell_state in
    k returned_a new_cell_value.

(** Here, [bind] takes a [nat_cell] computation [m] that computes an
intermediate result of type [A], along with a continuation, which is just a
function from [A] to a [nat_cell] computation of type [B], and composes them
sequentially.
*)

(** The correspondence with [let] binding can be made more apparent by
introducing some notation (which is relatively standard for monads).  The code
[x <- m ;; body] can be read as "bind the result of running computation [m] as
[x] in the [body] of the computation."  *)
#[local]
Notation "x <- m ;; body" := (nat_cell_bind m (fun x => body))
                              (at level 61, m at next level, right associativity).

(** This notation lets us illustrate the parallels between the standard Coq [let]-form (left),
the version for [nat_cell] that makes the state plumbing explicit (center), and
the monadic version, which again hides the state plumbing (right):

                 +----------------- Equal by Unfolding Definitions --------------+
                 |                                                               |
STANDARD COQ:    EXPLICIT STATE PLUMBING:   BIND:                MONADIC NOTATION:
let x := m in    let (σ', x) := m σ in      bind m (fun x =>     x <- m ;;
  rest x           rest x σ'                  rest x)             rest x
*)

(** Already we can rewrite the [sequence_cell_example] much more cleanly as follows,
where the input type [unit] means that it takes no (interesting) input and the
output type [nat_cell unit] indicates that it produces no interesting output, but
may update the [nat_cell] state:
*)
Example sequence_cell_example2 : unit -> nat_cell unit :=
  fun (_:unit) =>
    b <- cell_lt_two tt;;
    inc_cell_cond b.

(** To see that this presentation does indeed "thread" the [cell_state] through,
the computation, we can unfold the definitions to see how it it is used "under the hood":
*)
Lemma sequence_cell_example2_unfolded: sequence_cell_example2 =
             (fun (_ : unit) (cell_state : nat) => inc_cell_cond (cell_state <? 2) cell_state).
  unfold sequence_cell_example2. unfold nat_cell_bind.
  simpl.
  reflexivity.
Qed.

(** As before, we can run such a computation, but, in addition to the [tt]
input, we must also supply the initial state of the nat cell.  Note that we
get out the [unit] result as well: *)

Eval compute in (sequence_cell_example2 tt 0).
(** ==> [(1, tt) : nat * unit] *)

Eval compute in (sequence_cell_example2 tt 1).
(** ==> [(2, tt) : nat * unit] *)

Eval compute in (sequence_cell_example2 tt 2).
(** ==> [(2, tt) : nat * unit] *)

(* ----------------------------------------------------------------- *)
(** *** Generalizing return *)

(** Abstracting over the ability to "return" a value from a computation is
(usually) more straightforward than abstracting over [let]-binding. For
[nat_cell] computations, this amounts to just pairing the result with the
current cell state, so we have: *)
Definition nat_cell_ret {A} : A -> nat_cell A :=
  fun (result:A) (cell_state:nat) => (cell_state, result).

(** We introduce the (standard) monadic notation, [ret], as a useful
abbreviation.*)

#[local]
 Notation "'ret' a" := (nat_cell_ret a) (at level 50).

(** For example, to define a function takes in a [b:bool] and returns a "pure"
computation that negates [b], we write: *)
Example neg_nat_cell (b:bool) : nat_cell bool :=
  ret (negb b).

(** Although [ret] is "pure" (the cell value doesn't change and isn't accessed),
we still need to supply the initial state of the nat cell when we run the
computation: *)

Eval compute in (neg_nat_cell true 3).
(** ==> [(3, false) : nat * bool] *)

Eval compute in (neg_nat_cell false 17).
(** ==> [(17, true) : nat * bool] *)

(* ----------------------------------------------------------------- *)
(** *** Recap *)

(** [nat_cell] is the first example of a monad that we have seen so far.  To
recap, the key ideas are: (1) a monad is a type that represents "computations"
returning some value. (2) a monad has a natural notion of "sequential"
composition, given by [bind], that says what it means to perform one computation
after computing another; the behavior of the second computation can depend on
the result of the first. (3) a monad has a natural noation of what it means to
"return" a value, given by [ret].

We will define more precisely below what it means for these operations to be
"natural", after we have seen some other examples of monads in action.  But
before doing that, let us explore what we can do with [nat_cell] a bit further.
*)

(* ================================================================= *)
(** ** More state operations *)

(** We have already seen that we can, by hand, write Coq functions like
[cell_lt_two], which are [nat_cell] compuations that do (somewhat) interesting
manipulations of the state to produce a result.  However to do that by hand, we
had to know about the details of how the [nat_cell] monad is implemented, i.e.,
that it is defined as a type [nat -> (nat * B)] (and not, for instance, as the
isomorphic type [nat -> (B * nat)]). It would be cleaner if we could program such
computations without having to work with the monad definition explicitly.

Fortunately, most monads support notions of "effects", which are simply
"primitive" computations of monad type.  These effects can be implemented
concretely once-and-for-all, by exploiting the details of the type defining the
monad, but then they can be re-used in many applications without resorting to
looking "under the covers" of the monad abstraction.

For [nat_cell] the two effects are [get], which simply returns the current state
of the cell and [put n], which updates the state to be [n] and returns only the
[unit] value. These are simple enough to implement: *)

Definition get : nat_cell nat :=
  fun cell_state => (cell_state, cell_state).

Definition put (n:nat) : nat_cell unit :=
  fun cell_state => (n, tt).

(** With those two primitive operations in hand, we can now revisit the
examples from before.  Now, however, we can use a mixture of [nat_cell]
computations and functions that that return [nat_cell] computations to achieve a
much cleaner organization of the code.  Our new notations for [bind] and [ret]
also help.
*)

(** A computation that increments the current cell value: (Note that [get] is
already of type [nat_cell], so it doesn't take any "visible" inputs. Of course,
the underlying implementation does take a [cell_state] as input, but that is
"hidden" by the type of [nat_cell].)*)
Definition inc : nat_cell unit :=
  n <- get ;;
  put (1+n).

(** A generalization of [cell_lt_two] that compares the cell value to a provided [nat]: *)
Definition lt (m:nat) : nat_cell bool :=
  n <- get;;
  ret (n <? m).

(** The sequence example can now be written as: *)
Example sequence_cell_example3 : nat_cell unit :=
  b <- lt 2;;
  if b
  then inc
  else ret tt.

(** Although not using [lt] yields code that is more similar to a standard imperative program: *)
Example sequence_cell_example4 : nat_cell unit :=
  n <- get ;;
  if (n <? 2)
  then inc
  else ret tt.

(** We can still run the results, again by providing the initial state. *)
Eval compute in (sequence_cell_example4 0).
(** ==> [(1, tt) : nat * unit] *)

Eval compute in (sequence_cell_example4 1).
(** ==> [(2, tt) : nat * unit] *)

Eval compute in (sequence_cell_example4 2).
(** ==> [(2, tt) : nat * unit] *)

Example put_get_example : nat_cell bool :=
  _ <- put 4 ;;
  x <- get ;;
  ret (x =? 4).

Eval compute in (put_get_example 0).
(** ==> [(4, true) : nat * bool] *)

End NatCell.

Module State.


  (** ** Generalizing from [nat] to arbitrary states *)

  (** We saw how to define the sequencing ([bind]) and return operations for the
simple case of a mutable cell containing a natural number.  It is easy to
parametrize [nat_cell] to one that can work on arbitrary state. We call this new
definition [state] because it will be the basis for our generic state monad
operations. *)

  (** A stateful computation that returns a value of type [B] takes a state [S] as
  input and produces a (possibly updated state) along with the value of type [B].*)
  Definition state (S : Type) (B:Type) : Type :=  S -> S * B.

  (** For any [S], the type [state S] is a _monad_. *)

  (** Denotation for Imp commands that produce no value:

  state mem unit = mem -> mem * unit
*)

(**    Denotation for Imp-like programs that produce a [nat] value:

  state mem nat = mem -> mem * nat
*)
(* ----------------------------------------------------------------- *)
(** *** Sequential composition of commands *)

  (** The state monad's [bind] operation explicitly "plumbs" the state
  through the computation. It generalizes [let].*)
  Definition state_bind {S A B} (m : state S A) (k:A -> state S B)
    : state S B :=
    fun σ => let '(σ', a) := m σ in
          k a σ'.

  (** We introduce some notation to make using [bind] more palatable. *)
  #[local]
   Notation "x <- m ;; body" := (state_bind m (fun x => body))
        (at level 61, m at next level, right associativity).



  (** [ret] pairs a value [a:A] along with the initial state [σ] -- it is
  a [pure] computation that doesn't affect the state [σ] *)
  Definition state_ret {S A} : A -> state S A :=
    fun (a:A) (σ:S) => (σ, a).

  (** We introduce some handy notation for returning values. *)
  #[local]
    Notation "'ret' a" := (state_ret a)
                            (at level 50).


  (** For the [state] monad, the [get] and [put] operations work generically on any state. *)

  (** [get] returns the current value of the state, leaving the state unchanged. *)
  Definition get {S} : state S S :=
    fun σ => (σ, σ).

  (** [put] updates the state, returning the trivial [unit] value. *)
  Definition put {S} (σ:S) : state S unit :=
    fun _ => (σ, tt).

    (** Our state monad can work on any state type, for example [bool] state.
      Below, [b] is the result of reading the state via [get], we use
      [_] because the result of the [put] operation is the trivial [unit] value,
      and the computation returns [3] if [b] is [true] and [17] otherwise.
   *)
  Example boolean_state_example : state bool nat :=
    b <- get ;;
    _ <- put (negb b) ;;
    if b then ret 3 else ret 17.

  Eval compute in (boolean_state_example true).
  (** ==> [(false, 3) : bool * nat] *)

  Eval compute in (boolean_state_example false).
  (** ==> [(true, 17) : bool * nat] *)

End State.

(* ================================================================= *)
(** ** Options as a monad. *)
Module OptionMonad.

  (** As we saw with mutable state, above, the key ingredients needed to define
  a monad are a notion of "sequential" composition and a notion of "returning" a
  value.  As another example, let us see how [option] satisfies these
  requirements. *)

  (** Recall that the values of type [option B] include [Some b], where [b] is a
  value of type [B], and [None].  We can think of [option B] as a type that
  represents a computation of type [B] that might fail (producing [None] instead
  of a value).
  *)

  (** *** Generalizing Return *)

  (** For [option] it is easy to see what it means for a computation to "return" a value [b]:
  it is simply [Some b]:
  *)

  Definition option_ret {B} (b:B) : option B := Some b.

  (** As before, we can introduce some handy notation for "returning" a value. *)
  #[local]
   Notation "'ret' a" := (option_ret a) (at level 50).

  (** This lets us define a successful computation as returning a result.  *)
  Example returns_three : option nat := ret 3.

  Eval compute in (returns_three).
  (** ==> [Some 3 : option nat] *)

  (** (You might wonder, given the definition above, why we don't just use [Some].
  That would be type correct, but introducing consistent notation for monads will
  make it easier to write general-purpose code that works for _any_ monad.  We
  will introduce such a typeclass shortly.)  *)

  (** As another example, the following function, given [n:nat], produces a
  computation that always succeeds, returning a [bool] indicating whether [n] ia
  equal to [3]: *)

  Example is_three_succeeds (n:nat) : option bool :=
    if n =? 3 then ret true else ret false.

  Eval compute in (is_three_succeeds 0).
  (** ==> [Some false : option bool] *)

  Eval compute in (is_three_succeeds 3).
  (** ==> [Some true : option bool] *)

  (** Because we want to think of [None] as a "failing" computation, we also
  introduce some notation that makes that point of view clear: *)

  Notation "'fail'" := None.

  (** Now we can define a function the sometimes fails and sometimes succeeds,
  depending on its input: *)

  Example fail_if_zero (n:nat) : option nat :=
    if n =?0 then fail else ret n.

  Eval compute in (fail_if_zero 0).
  (** ==> [fail : option nat] *)

  Eval compute in (fail_if_zero 3).
  (** ==> [Some 3 : option nat] *)

  (** *** Generalizing [let]: [bind] for [option] *)

  (** Now suppose that we have a computation [m] of type [option nat] and we want
  to sequence it before one of the two examples above. If [m] fails, the
  whole sequenced computation should also fail--there is no result to feed
  to the next step.  *)

    Example seq_is_three_succeeds (m : option nat) : option bool :=
    match m with
    | None => fail
    | Some n => is_three_succeeds n
    end.

  (** When we run [seq_is_three_succeeds] on a successful computation that
  returns [3] we get: *)
  Eval compute in (seq_is_three_succeeds returns_three).
  (** ==> [Some true : option bool] *)

  (** When we run it on a successful computation that returns [0] we get: *)
  Eval compute in (seq_is_three_succeeds (ret 0)).
  (** ==> [Some false : option bool] *)

  (** On the other hand, running it on a failing computation we get: *)
  Eval compute in (seq_is_three_succeeds fail).
  (** ==> [fail : option bool] *)

    (** As with state, we can define [bind] to be the general, sequential
  composition of operation:*)

  Definition option_bind {A B} (m:option A) (k : A -> option B) : option B :=
    match m with
    | None => fail
    | Some a => k a
    end.

  (** And re-use the [let]-inspired notation from earlier: *)
  #[local]
   Notation "x <- m ;; rest" := (option_bind m (fun x => rest))
         (at level 61, m at next level, right associativity).
  (** Now we can write some examples more cleanly: *)

  Example seq_is_three_succeeds' (m : option nat) : option bool :=
    n <- m ;;
    is_three_succeeds n.

  Eval compute in (seq_is_three_succeeds' returns_three).
  (** ==> [Some true : option bool] *)

  Eval compute in (seq_is_three_succeeds' (ret 0)).
  (** ==> [Some false : option bool] *)

  Eval compute in (seq_is_three_succeeds' fail).
  (** ==> [fail] *)

  (** This notation really shines when there are several operations in sequence,
  because each [bind] expands to (nested) pattern matches.  For instance: *)
  Example bigger_sequence (m : option nat) : option bool :=
    n <- m ;;
    n' <- fail_if_zero n ;;
    is_three_succeeds n'.

  (** Is much easier to read than this :*)
  Example bigger_sequence_desugared (m : option nat) : option bool :=
    match m with
    | None => fail
    | Some n =>
        match fail_if_zero n with
        | None => fail
        | Some n' => is_three_succeeds n'
        end
    end.

  Eval compute in (bigger_sequence returns_three).
  (** ==> [Some true : option bool] *)

  Eval compute in (bigger_sequence (ret 0)).
  (** ==> [fail : option bool] *)

  Eval compute in (bigger_sequence (ret 17)).
  (** ==> [Some false : option bool] *)

  (** EX1 (example_option_and ) *)

  (** Write an [option] monad computation that returns the logical "and" of
      the two values returned by [m1] and [m2] and fails if either [m1] or
      [m2] fails. You can use [andb : bool -> bool -> bool] to compute the result.
      Your version should pass all the tests below.
  *)
  Example example_option_and (m1 : option bool) (m2 : option bool) : option bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Example test_example_option_and1: example_option_and (ret true) (ret true) = ret true.
  Proof. (* FILL IN HERE *) Admitted.

  Example test_example_option_and2: example_option_and (ret true) (ret false) = ret false.
  Proof. (* FILL IN HERE *) Admitted.

  Example test_example_option_and3: example_option_and (ret false) (ret true) = ret false.
  Proof. (* FILL IN HERE *) Admitted.

  Example test_example_option_and4: example_option_and (ret false) (ret false) = ret false.
  Proof. (* FILL IN HERE *) Admitted.

End OptionMonad.

(* ================================================================= *)
(** ** Monads, generally *)
Module Monad.

(** So far we have seen three instances of monads: [nat_cell], [state S], and
[option]. Note that each of these is a _parameterized type_, they have kind
[Type -> Type].  The common abstraction linking them is that they represent
computations that can be composed in sequence.  In general, a monad [M : Type -> Type]
is a parameterized type for which we think of [M A] as representing "(potentially)
impure computations that return an [A]".  Moreover, [M] must support:
  - [ret], a way to embed _pure_ computations, and
  - [bind], a way to _sequence_ computations.
*)

(** We also saw that each of our example monads supported additional operations that
are unique to their types--they each represent a specific kind of "impure"
computation. The [nat_cell] and [state S] monads support [get] and [put]
operations that access the state.  The [option] monad supports [fail], a computation
that fails.  The [bind] operation propagates the monad-specific information through
the sequencing.*)

(** Because all monads support [ret] and [bind], we can define those operations
as a typeclass, which will allow us to overload those operations and (soon)
to define lemmas that work generically for _any_ monad. *)
  Class Monad (M : Type -> Type) := {
      ret  : forall A, A -> M A;
      bind : forall A B, M A -> (A -> M B) -> M B;
    }.
  #[global]
  Arguments ret  {M _} {A}.

  #[global]
  Arguments bind {M _} {A B}.

(** For an arbitrary monad [M], [M nat] is an effectful computation computing a
    [nat], [ret (3 + 4)] is the pure computation computing [3 + 4], and [bind m k]
    performs [m], gets its result, feeds it to [k] and continues. *)

(* ----------------------------------------------------------------- *)
(** *** Monad Notations *)

(** We can recapitulate our helpful notations from earlier, along with a couple
variants that make programming with monads more natural. *)

Module MonadNotation.

  #[export]
  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  (** The standard monadic sequencing operation in terms of [bind]. *)
  Notation "x <- m ;; k" := (@bind _ _ _ _ m (fun x => k))
    (at level 61, m at next level, right associativity) : monad_scope.

  (** A version that ignores the result from the first computation. Useful
   when [m : M unit] *)
  Notation "m ;; k" := (@bind _ _ _ _ m%monad (fun _ => k%monad))%monad
    (at level 61, right associativity) : monad_scope.

  (** A version that allows Coq's pattern matching notation to be used
   for the binder.  Useful when the computation returns a tuple.
  *)
  Notation "' pat <- m ;; k" :=
    (@bind _ _ _ _ m (fun x => match x with pat => k end))
    (at level 61, pat pattern, m at next level, right associativity) : monad_scope.

End MonadNotation.

(* ================================================================= *)
(** ** Monad Instances *)

(* ----------------------------------------------------------------- *)
(** *** Option

    Computations that may fail can be modeled using the option monad *)
#[export] Instance OptionM : Monad option :=
{|
  ret := fun A (a : A) => Some a;
  bind := fun A B m k =>
	    match m with
	    | Some x => k x
	    | None => None
	    end
|}.

Notation "'fail'" := None.

(** And the one that initiated our exploration: stateful computations can use the state monad *)

(* ----------------------------------------------------------------- *)
(** *** State instance of the Monad Typeclass *)
Definition state (S:Type) : Type -> Type := fun A => S -> (S * A).

#[export]
  Instance stateM S : Monad (state S) :=
  {|
    ret  := fun A (a : A) σ => (σ, a);
    bind := fun A B (m : state S A) (k : A -> state S B) =>
            fun σ => let '(σ', a) := m σ in
		  k a σ'
  |}.

Definition get {S} : state S S :=
  fun σ => (σ, σ).

Definition put {S} (σ:S) : state S unit :=
    fun _ => (σ, tt).

(* ----------------------------------------------------------------- *)
(** *** Identity

    Pure computations can be seen as computations in the _identity monad_, in which
[bind] is just function application.  (This is a useful "base case" for some
constructions involving maps between monads.)
 *)
Definition id : Type -> Type := fun X => X.
#[export] Instance IdM : Monad id :=
{|
  ret := fun A (a : A) => a;
  bind := fun A B a f => f a;
|}.

(* ----------------------------------------------------------------- *)
(** *** Nondeterminism

    We can define a "nondeterminism" monad whose computation type is given by [list].
   We can think of a computation in this monad as (nondeterministically) exploring
   all possible combinations of values in the list.
 *)

Definition nondet : Type -> Type := list.
#[export] Instance NonDetM : Monad nondet :=
{|
  ret  := fun A (a : A) => [a];
  bind := fun A B (m : nondet A) (k : A -> nondet B) =>
          List.flat_map k m
|}.

(** The "effectful" operation of this monad is an operation that chooses
nondeterministically from among a list of possibilities. *)
Definition choose {A} (choices : list A) : nondet A := choices.

Import MonadNotation.
Open Scope monad_scope.

Example decode_bits_example : nondet nat :=
  b0 <- choose [0; 1] ;;
  b1 <- choose [0; 1] ;;
  match (b1, b0) with
  | (0, 0) => ret 0
  | (0, 1) => ret 1
  | (1, 0) => ret 2
  | (1, 1) => ret 3
  | _ => choose []
  end.

Eval compute in decode_bits_example.
(** ==> [ [0; 2; 1; 3] : list nat]*)
End Monad.

(* ================================================================= *)
(** ** Monad Laws *)
Module MonadLawsEq.

  Import Monad.
  Import MonadNotation.
  Open Scope monad_scope.
(** When we introduced the idea of generalizing sequential composition above, we
noted that [ret] and [bind] should be "well-behaved".  What, exactly, does that
mean?

In the case of sequential composition of imperative code, one property we would
expect is that the way in which we group commands with [';'] doesn't matter,
namely we expect that [(c1 ; c2) ; c3] and [c1 ; (c2 ; c3)] should mean the same
thing.  That is, seqencing is an _associative_ operation.

In the case of [let]-binding, the idea of "associativity" needs to be slightly
generalized to account for the scope of the variable bindings.  But we can still
see the same structure.  Consider the following two Gallina terms:
*)



Example nested_lets1 :=
  let x :=
    (let y := 3 in y + y)
  in x * 2 .

Example nested_lets2 :=
  let y := 3 in
  let x := y + y in
  x * 2.

(** Both of these expressions evaluate to the _same_ value: *)
Eval compute in nested_lets1.
(** ==> [12 : nat] *)

Eval compute in nested_lets2.
(** ==> [12 : nat] *)

(** Using the identity [id] monad, we can even write these examples using our
monad notation directly: *)
Example nested_lets_monadic1 : id nat :=
  x <-
    (y <- ret 3 ;; ret (y+y)) ;;
  ret (x * 2).

Example nested_lets_monadic2 : id nat :=
  y <- ret 3 ;;
  x <- ret (y + y) ;;
  ret (x * 2).

Eval compute in nested_lets_monadic1.
(** ==> [12 : nat] *)

Eval compute in nested_lets_monadic2.
(** ==> [12 : nat] *)

(** Thus, the first property that we expect to hold of a "well-behaved" monad is
that [bind] is _associative_. For [let]-bindings, this means that we can
"un-nest" them, floating inner bindings outward.  For other monadic
computations, it means that the the behavior truly is sequential.  In words:
"doing [a] before doing [b] and then [c]" is the _same_ as "doing [a] then [b]
before doing [c]".

We can write this down as a (first attempt at a) general law about monads as
follows: *)

Definition bind_associativity_law {M} `{Monad M} {A B C} :=
  forall (ma : M A) (kb : A -> M B) (kc : B -> M C),
    x <- (y <- ma ;; kb y) ;; kc x
    =
    y <- ma ;; x <- kb y ;; kc x.

(** Taking a closer look at the examples above suggest another property that we
would expect to hold.  If we think about the operational behavior of a
[let]-binding, we expect to have a _substitution_ property, namely, that we an
replace the [let]-bound variable with its definition. For example, consider
what happens if we substitute [3] for [y] when evaluating [nested_lets2]. We get: *)

Example nested_lets_monadic2' :=
  let y := 3 in
  let x := y + y in
    x * 2.

Example nested_lets2_subst :=
  let x := 3 + 3 in    (* n.b. substitute [3] for [y] in  [y + y] *)
  x * 2.

(** After the substitution, we still obtain the same result: *)
Eval compute in (nested_lets2_subst).
(** ==> [12 : nat] *)

(** Looking at the same computation expressed using the [id] monad gives us: *)
Example nested_lets_monadic2_subst : id nat :=
  x <- ret (3 + 3) ;;  (* n.b. substitute [3] for [y] in [ret (y + y)] *)
  ret (x * 2).

(** For an arbitrary monad [M], we think of [ret a] as a _pure_ computation that
simply yields a value of type [A].  That means we can "substitute" the returned
value directly into the body of the continuation.  That gives us this second
monad law "[ret] is the left-identity of [bind]".  (Here we use the word
"identity" in the same sense that [1] is the identity of multiplication and [0]
is the identity of addition; it leaves the result unchanged.) *)
Definition bind_ret_l_law {M} `{Monad M} {A B} :=
  forall (a : A) (kb : A -> M B),
    x <- ret a ;; kb x
    =
    kb a.

(** To see what the last monad law means, consider this following example,
again, stated with [let] notation: *)

Example let_return (m : nat) :=
  let x := m in
  x.

(** For any specific choice of [m], this trivial [let] binding is simply
equivalent to [m] itself.  Note that this is true only because we are returning
exactly [x] and not building some more complex computation using [x]. Moreover,
we aren't duplicating [m] (which would cause its effects to occur multiple times). *)

(** Rewriting this example using monadic notation we have: *)
Example let_return_monadic (m : nat) :=
  x <- m ;;
  ret x.

(** But both of those are just equivalent to [m] itself. *)

(** Here again, this trivial use of [m] by naming it [x] should be exactly the
same as just running the computation [m] (the answer, [x], will always be
exactly what [m] returns.

These observations give us the final monad law, which states that "[ret] is the
right-identity of [bind]": *)
Definition bind_ret_r_law {M} `{Monad M} {A} :=
  forall (m : M A),
    x <- m ;; ret x
    =
    m.

(* ----------------------------------------------------------------- *)
(** *** Monad Laws

    Collecting these requirements together, we can define a typeclass that
    captures the requirements that a monad [M] satisfies these laws: *)
Class MonadLaws {M} `{Monad M} := {
    bind_associativity :
    forall A B C (ma : M A) (kb : A -> M B) (kc : B -> M C),
      x <- (y <- ma ;; kb y) ;; kc x
      =
      y <- ma ;; x <- kb y ;; kc x

  ; bind_ret_l :
    forall A B (a : A) (kb : A -> M B),
      x <- ret a ;; kb x
      =
      kb a

  ; bind_ret_r :
    forall A (m : M A),
      x <- m ;; ret x
      =
      m
  }.
Arguments bind_associativity {_ _ _ _ _ _}.
Arguments bind_ret_l {_ _ _ _}.
Arguments bind_ret_r {_ _ _}.

(* ----------------------------------------------------------------- *)
(** *** Monadic Reasoning

    As an example. we can show that a generic version of [nested_lets_monadic1]
is equal to [ret 12] by explicitly using rewriting with these laws. *)

Example nested_lets_generic {M} `{Monad M} : M nat :=
  x <-
    (y <- ret 3 ;; ret (y+y)) ;;
  ret (x * 2).

(** In the proof below, notice how the state of the monadic computation evolves
as we proceed -- rewriting by this sequence of equivalences "steps" the
computation forward, substituting the returned values through the continuation.
(The connection to evaluation is best observed by stepping through the proof interactively.)
*)

Example monadic_proof {M} `{Monad M} `{MonadLaws M} :
  nested_lets_generic = ret 12.
Proof.
  unfold nested_lets_generic.
  rewrite bind_associativity.
  rewrite bind_ret_l.
  rewrite bind_ret_l.
  reflexivity.
Qed.

(** EX1 (monad_laws1)

    Use the monad laws and [simpl], ending with [reflexivity] to complete the
following proof.*)
Lemma monad_laws1 {M} `{Monad M} `{MonadLaws M} :
  x <- (y <- ret true ;; if y then ret 3 else ret 0) ;;
  z <- (w <- ret x ;; if x =? 0 then ret 17 else ret 42) ;;
  ret (z + 5)
  = ret 47.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** EX2 (monad_laws2)

    Use the monad laws and [simpl], ending with [reflexivity] to complete the
following proof.*)
Lemma monad_laws2 {M} `{Monad M} `{MonadLaws M} :
  forall (m : M nat),
    z <- (x <- (y <- m ;; ret y) ;; ret (x + 2)) ;; ret z
    = x <- m ;; ret (x + 2).
Proof.
  intros m.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** EX2 (monad_laws2)

    Use the monad laws and [simpl], ending with [reflexivity] to complete the
following proof.*)
Lemma monad_laws3 {M} `{Monad M} `{MonadLaws M} :
  forall (m : M nat),
    z <- m ;; y <- ret z ;; ret (y + 2)
    = x <- m ;; ret (x + 2).
Proof.
  intros m.
  (* FILL IN HERE *) Admitted.
(** [] *)

End MonadLawsEq.

Module MonadLawsEqM.

  Import Monad.
  Import MonadNotation.
  Open Scope monad_scope.

(* ----------------------------------------------------------------- *)
(** *** Monad Equivalences *)

(** There is one important question that this discussion about well-behaved
monads has swept under the rug, namely: What does it mean for two monadic
computations to be "the same"?  In the monad laws as stated above, we chose
Coq's default [=] as "the" equality for computations of monadic type [M A].
That choice is appropriate in many situations--it works for [option], for
example--but it is not correct in all cases; the notion of what it means for
two, potentially impure, computations to be "the same" can be quite subtle.

We can already start to see the issue if we try to prove the monad laws for
[state S]: *)

Lemma bind_associativity_state_problematic :
  forall S A B C (ma : state S A) (kb : A -> state S B) (kc : B -> state S C),
    x <- (y <- ma ;; kb y) ;; kc x
    =
      y <- ma ;; x <- kb y ;; kc x.
Proof.
  intros. unfold bind. simpl.
Abort.

(** Because [state S A] is defined as [S -> (S * A)], to say what it means for
two stateful computations to be the same means that we have to say what it means
for two _functions_ to be the same.  To proceed from here, we could use
_functional extensionality_, which is safe to add as an axiom to Coq, but we
can't prove this directly. *)

Module AXIOM.
Axiom functional_extensionality : forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.
End AXIOM.

(** For [state], it would suffice to adopt functional extensionality to express
its notion of equivalence.  Other monads, however, might require different
notions of "equivalence".  For example, consider a variant of the [nondet] monad
where we think of underlying [list] as representing a _set_ of values.  In that
case we would want two monadic computations to be considered equal if the lists
representing them contain the _same_ elements, possibly repeated or in different
orders. That notion of equality would allows us to justify more program
optimizations while preserving computation "equivalence".  See the exercises
below where we explore that topic.

As related example, we might want to _implement_ the state [S] of the [state S]
type using some data structure that itself has a non-trivial equivalence.  We
might implement [S] as a finite map of variable to values or as a [heap] with a
complicated set of invariants.  In that case, using Coq's [=] to compare two
states for equality would not work out, so functional extensionality would again
not be appropriate.

To address this issue, it is helpful to state the monad laws parametrically in a
notion of equivalence that can be specified per monad instance.  We therefore
introduce a new typeclass, [eqM], and ask that it be an [Equivalence] relation.

The price is that we will have to provide such an equivalence for each new monad
that we work with, but, as we shall see later, generalizing this notion of
equivalence even further will give us powerful tools for reasoning about monadic
computations. *)

Class EqM (M : Type -> Type) : Type :=
  eqM : forall A, M A -> M A -> Prop.
#[export]
Arguments eqM {M _ _}.

(** We also require a proof that [eqM] is an equivalence relation. *)
Class EqMEquivalence (M : Type -> Type) `{EqM M} :=
  eqM_equiv : forall A, Equivalence (eqM (A := A)).
#[global]
Existing Instance eqM_equiv.

(** Because the notion of monadic equivalence is so prevalant, we introduce
[≈] as a succinct, infix version. *)

Infix "≈" := eqM (at level 70) : monad_scope.

(** Having introduced the appropriate typeclasses for working with monadic
equivalences, we can no recapitulate the monad laws using [≈] rather than [=].
For rewriting to work correctly, we also need to ask that the [bind] operation
respect [≈], i.e., that it is [Proper] with respect to the underlying monad
equivalence.*)

Class MonadLaws M `{Monad M} `{EqM M} := {
    bind_associativity :
    forall A B C (ma : M A) (kb : A -> M B) (kc : B -> M C),
      x <- (y <- ma ;; kb y) ;; kc x
      ≈                                 (* <---- NEW! *)
      y <- ma ;; x <- kb y ;; kc x

  ; bind_ret_l :
    forall A B (a : A) (kb : A -> M B),
      x <- ret a ;; kb x
      ≈
      kb a

  ; bind_ret_r :
    forall A (m : M A),
      x <- m ;; ret x
      ≈
        m

  (* NEW! *)
  ; Proper_bind : forall {A B},
      @Proper (M A -> (A -> M B) -> M B)
              (eqM ==> pointwise_relation _ eqM ==> eqM) bind
  }.
#[global] Existing Instance Proper_bind.
#[export] Arguments bind_associativity {M _ _ _}.
#[export] Arguments bind_ret_l {M _ _ _}.
#[export] Arguments bind_ret_r {M _ _ _}.
#[export] Arguments Proper_bind {M _ _ _}.

(* ================================================================= *)
(** ** Properness: a logical relation *)

(** The requirement that [bind] be [Proper] says that [bind] "respects" the
  monad equivalence.  Alternatively, that [bind] is in the _logical relation_
  associated with its type:
*)
Lemma Proper_bind_def : forall M `{Monad M} `{EqM M} `{MonadLaws M} A B,

    (@Proper (M A -> (A -> M B) -> M B)
            (eqM ==> pointwise_relation _ eqM ==> eqM) bind) <->
  forall (m1 m2 : M A),
    m1 ≈ m2 ->
    forall k1 k2 : A -> M B,
      (forall a1 a2 : A, a1 = a2 -> k1 a1 ≈ k2 a2)
    ->
    (x <- m1;; k1 x) ≈ (x <- m2;; k2 x).
Proof.
  split; intros.
  - apply H4; auto.
    repeat red. intros. apply H6. auto.
  - repeat red. intros. apply H4; auto. intros. subst. apply H6.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Important! *)

(** This generalization from [=] to [eqM] is the stepping stone
to even more powerful _relational reasoning_ principles that
will naturally extend the _computational equivalence_ to
_relational specifications_.
*)

Section StateLaws.
  (** *** Monad Laws for [state S] *)

(** With the extra bit of flexibility offered by [eqM], we can now choose an
appropriate notion of equivalence for each monad instance.  For [state], one
simple option is to use [=] but then exploit functional extensionality. When
proving the instance of the monad laws. *)

  (** First, we define [eqM] for [state S]: *)

  (** For expediency (and compatibility with SF) we use [=] and
  restort to _functional_extensionality_. *)
  #[export]
  Instance eqM_state {S} : EqM (state S) := fun A => (@eq (state S A)).

  #[export]
  Instance eqM_state_equiv {S} : EqMEquivalence (state S).
  Proof.
    constructor; unfold eqM, eqM_state; typeclasses eauto.
  Qed.

  (** Next we prove the monad laws: *)
  #[export]
  Instance eqm_state_monad_laws {S} : MonadLaws (state S).
  Proof.
    constructor.
    - intros. unfold eqM, eqM_state.
      (* use functional extensionality(!) *)
      apply functional_extensionality.
      intro σ.
      simpl.
      destruct (ma σ).
      reflexivity.
    - intros. unfold eqM, eqM_state.
      apply functional_extensionality.
      intro σ.
      reflexivity.
    - intros. unfold eqM, eqM_state.
      apply functional_extensionality.
      intro σ.
      simpl.
      destruct (m σ).
      reflexivity.
    - repeat red.
      intros A B m1 m2 EQ a1 a2 HP.
      apply functional_extensionality.
      intro σ.
      simpl.
      rewrite EQ.
      destruct (m2 σ).
      rewrite HP.
      reflexivity.
  Qed.

    (** Recall that the [state S] monad supports [get] and [put] as specific
  effectful computations.  Now that we have defined what it means for two state
  monad computations to be equivalent, we can justify equational reasoning
  principles that are specific to [state] monad and that take advantage of the
  semantics of stateful operations. *)

  (** One example of such an equivalence is given by the following lemma, which
  states that two [put] operations in a row is equivalent to doing just the
  second. This lemma explicitly captures the idea that a later store to the
  state overwrites an earlier one.  *)

  Lemma put_put {S} : forall (σ1 σ2 : S),
      put σ1 ;; put σ2 ≈ put σ2.
  Proof.

    intros σ1 σ2.
    apply functional_extensionality.
    intros σ0.
    reflexivity.
  Qed.

    (** Similarly, if we [put] a value and then immediately [get] the state,
      we could have equally just returned the value, rather than using [get]:
  *)
  Lemma put_get {S A} : forall (σ : S) (k : S -> state S A),
      put σ ;; get ≈ put σ ;; ret σ.
  Proof.

    intros σ1 k.
    apply functional_extensionality.
    intros σ0.
    reflexivity.
  Qed.

    (** Overwriting the state with the value that it already contains is a no-op. *)
  Lemma get_put {S} :
    s <- get ;; put s ≈ (ret tt : state S unit).
  Proof.
    apply functional_extensionality.
    intros σ0.
    reflexivity.
  Qed.

    (** When we do two [get]s without any intervening [put], the value in the state
  does not change. *)
  Lemma get_get {S A} : forall (k : S -> S -> state S A),
    s1 <- get ;; s2 <- get ;; k s1 s2 ≈ s1 <- get ;; k s1 s1.
  Proof.
    intros k.
    apply functional_extensionality.
    intros σ0.
    reflexivity.
  Qed.

  (** These lemmas are the "equational theory" for this simple [state] monad.
  We can think of them as defining "algebraic" laws let us replace one sequence
  of stateful operations with another.  Such a theory can be used to prove the
  correctness of program optimizations.

  Of course, with this model of state, which has only a single mutable cell, the
  equational theory is fairly simple.  More complex models of mutable state, for
  instance, one modeling a more realistic program memory, would justify
  correspondingly more complex reasoning principles.  Moreover, once other
  computational effects, like concurrency, are involved, such laws might no
  longer be valid.  Each of the laws above is justifiable only if the state
  cannot be modified between the two operations.
  *)

End StateLaws.

Module StateLaws2.
  (* TODO: Make this into an exercise *)

  (** An alternative definition of [eqM] for [state], not taking functional extensionality
as an axiom. *)

  #[local]
   Instance eqM_state {S} : EqM (state S) :=
  fun A (m1 m2 : state S A) =>
    forall (s1 s2 : S), s1 = s2 -> m1 s1 = m2 s2.

  #[local]
  Instance eqM_state_equiv {S} : EqMEquivalence (state S).
  Proof.
    constructor; unfold eqM, eqM_state.
    - repeat red. intros. subst; auto.
    - repeat red. intros. subst; auto. symmetry. apply H. reflexivity.
    - repeat red. intros. subst; auto. eapply transitivity. apply H. reflexivity. apply H0. reflexivity.
  Qed.

  (** Next we prove the monad laws: *)
  #[local]
  Instance eqm_state_monad_laws {S} : MonadLaws (state S).
  Proof.
    constructor.
    - intros. unfold eqM, eqM_state.
      intros σ1 σ H. subst.
      simpl.
      destruct (ma σ).
      reflexivity.
    - intros. unfold eqM, eqM_state.
      intros σ1 σ H. subst.
      reflexivity.
    - intros. unfold eqM, eqM_state.
      intros σ1 σ H. subst.
      simpl.
      destruct (m σ).
      reflexivity.
    - repeat red.
      intros A B m1 m2 EQ a1 a2 HP σ1 σ H.
      subst.
      simpl.
      specialize (EQ σ σ eq_refl).
      rewrite EQ.
      destruct (m2 σ).
      erewrite HP; reflexivity.
  Qed.

End StateLaws2.

  (** *** Monad Laws for [id] and [option] *)

(** We can give a similar instantation of the monad laws for [id] and [option],
but in both of those cases we simple use [=] as the instance of [eqM]. *)

Section IdLaws.

    (** First, we define [eqM] for [id]: *)

  #[export] Instance eqM_id : EqM id := fun A => (@eq (id A)).

  #[export] Instance eqM_id_equiv : EqMEquivalence id.
  Proof.
    constructor;
      unfold eqM, eqM_id; typeclasses eauto.
  Qed.

  (** Next we prove the monad laws. The only slightly nontrivial case is
[Proper], which needs a bit of rewriting.  *)
  #[export] Instance eqM_id_monad_laws : MonadLaws id.
  Proof.
    constructor; try reflexivity.
    - repeat red; intros.
      rewrite H.
      simpl.
      rewrite H0.
      reflexivity.
  Qed.

End IdLaws.

Section OptionLaws.
  Import Monad.
  (** Next, we define [eqM] for [option] as just [=]: *)

  #[export] Instance eqM_option : EqM option := fun A => (@eq (option A)).

  #[export] Instance eqM_option_equiv : EqMEquivalence option.
  Proof.
    constructor; unfold eqM, eqM_option; typeclasses eauto.
  Qed.

  (** Next we prove the monad laws. By destructing the [option] value and using
  rewriting for the [Proper] case, the laws follow straightforwardly.  *)

  #[export]
  Instance eqM_option_monad_laws : MonadLaws option.
  Proof.
    constructor.
    - intros.
      destruct ma; simpl; reflexivity.
    - reflexivity.
    - intros.
      destruct m; simpl; reflexivity.
    - repeat red; intros.
      rewrite H.
      simpl. destruct y.
      + rewrite H0. reflexivity.
      + reflexivity.
  Qed.

  (** As with the [state S] monad, [option] also supports a monad-specific
  equational theory. There is only one interesting law, which states that
  the [fail] operation terminates the computation: *)

  Lemma fail_exits : forall {A B} (m : option B),
      (fail : option A) ;; m ≈ fail.
  Proof.
    intros.
    reflexivity.
  Qed.

End OptionLaws.

  (** *** Monad Laws for [nondet] *)

Section NonDetLaws.
  (** As an example of a non-trivial definition of [eqM], let's use this notion
  of equivalence for the list representing a (set) of nondeterministic
  computation. This definition considers the two lists to be equal whenever
  their elements are the same, regardless of order or number of occurrences: *)

  #[export] Instance eqM_nondet : EqM nondet :=
  fun A m1 m2 => (forall x, In x m1 -> In x m2) /\ (forall x, In x m2 -> In x m1).

  (** It is easy enough to prove that this is an equivalence relation on lists. *)

  #[export] Instance eqM_nondet_equiv : EqMEquivalence nondet.
  Proof.

    constructor; unfold eqM, eqM_nondet; repeat red; intuition.
  Qed.

  (** Now it remains to see that the monad laws are satisfied up to this notion. *)

  (** **** Exercise: 4 stars, standard (eqM_nondet_monad_laws) *)
  (** Complete the following proof that demonstrates that the monad laws hold for [nondet]
  with the notion of equivalence defined above.  Hint: you will need to use the List library
  facts about [In] and [flat_map].  A key lemma is: [in_flat_map_Exists].
  *)
  #[export] Instance eqM_nondet_monad_laws : MonadLaws nondet.
  Proof.
    (* FILL IN HERE *) Admitted.
  (** [] *)

  (** Observe that we can also prove that [nondet] satisfies the monad laws with
  [=] as the notion of equivalence. That means that there is more than one way
  in which a type can be a monad, and the difference depends on what we consider
  to be "the same". *)

End NonDetLaws.
End MonadLawsEqM.

(* ================================================================= *)
(** ** Deep vs. Shallow Embeddings *)



(** In programming language foundations (PLF) the approach we took to
verification was to define a syntax and semantics for a language, then prove key
correctness theorems with regards to those semantics -- for example, the
progress and preservation lemmas for STLC. Then use those lemmas to verify
programs.

    One question you might ask is, why do we need to define a new language to
    verify programs? In other words, could we encode programs using Coq's
    Gallina semantics? Gallina is a pure functional programming language with
    syntactic termination constraints; so the programs we can define are limited
    -- there is no support for mutable state, errors, threads, network events,
    non-determinism and other common features of general purpose programming. In
    this chapter we will discover how to work around those limitations --
    starting with state and errors.  *)

(** In [Imp.v] we implemented a language with basic control flow operators and
mutable state. Gallina is pure functional so it does not support mutable state
-- every function can only mutate its return value. This is not realistic,
modern applications access databases with terabytes of data and the absence of
mutable state means every time the program wants to change a value in the
database it must return a copy of the entire database.

    So how do we go about adding mutable state to Gallina? Let's start with
    something simple, we would like our functional programs to [load] and
    [store] a single register of type [nat]. *)

(* 2024-06-10 14:53 *)
