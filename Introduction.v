(** * Introduction *)

(* ================================================================= *)
(** ** Motivation: Reasoning about Program Behaviors *)

(** A program is a way of describing the behavior of some kind of computational
process.  Familiar computational behaviors include things like: performing an
arithmetic calculation, storing some data (perhaps a bitmap image or other data
structure) in the computer's memory, printing an output to the terminal, or
reading the user's keystrokes.  Other behaviors describe the interactions that
occur when we decompose a larger computational process into smaller ones. For
instance, when a client exchanges messages with a server following some
communication protocol, or when a program module invokes a OS system call or a
function provided by another module.  Still other behaviors, which are sometimes
not very desirable but still necessary to describe, have to do with the ways in
which a computational system might misbehave, for instance by halting, raising
an error, or going into an infinite loop.  A computation might behave
nondeterministically or probabilistically.

Because there are so many different ways that a computational process might
behave, there are many different programming language features (and programming
languages!) that we use to describe them.  A programming language semantics
gives a precise mathematical characterization of these behaviors so that
programmers can reason about what their programs do.  Such semantics are useful
not only for programmers, who need to understand the language semantics to
predict what their code will do, they also inform programming language
implementors. A compiler should faithfully translate the behaviors of the source
semantics into behaviors of the target semantics, and tools like static
analyzers and debuggers should respect the abstractions provided by the
language.  A language semantics is a _specification_ for the programs written in
that language.

To account for the rich variety of computational phenomena, programming
languages researchers have developed a host of mathematical tools and techniques
that can be used to define semantics.  Earlier volumes in this series showed how
to define operational semantics for Imp and the Simply-Typed Lambda Calculus,
two prototypical programming languages with relatively simple computational
behaviors.  This volume explores how to define semantics for the richer kinds of
behaviors described above.

*)

(* 2024-06-07 10:32 *)
