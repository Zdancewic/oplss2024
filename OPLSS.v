(** ** Formal Verification of Monadic Computations *)

(** Steve Zdancewic

    University _of_ Pennsylvania

    OPLSS 2024
 *)

(* ================================================================= *)
(** ** Many thanks to: *)

(**

Yannick Zakowski         Li-yao Xia
Paul He                  Irene Yoon
Lucas Silver             Lef Ioannidis
Jessica Shi              Gary Chen
Eduardo Gonzalez         Nathan Sobotka
Zak Sines                ...
*)

(* ================================================================= *)
(** ** Motivation *)

(** Software _mostly_ works, but there are many critical systems for which the
effort of formal verification can warranted:

- operating systems, web servers
- mission-critical code (flight-control, autopilot, ...)
- infrastructure & tools like compilers
- medical devices / control software
- cryptography / cryptocurrencies / banking
*)

(* ================================================================= *)
(** ** Challenges *)

(** Verifying systems of the kind mentioned above is non-trivial:

- complex specifications
- complex behaviors: state, I/O, nontermination, nondeterminism
- scale & cost
- ...

*)

(* ================================================================= *)
(** ** Programming Languages *)

(** PL lays the foundations needed to build reliable software:

- abstractions for describing rich computational systems
- proof techniques for reasoning about them
- concepts of modularity & compositionality that are important for scale

Success stories:

     CompCert       CakeML
     CertiKOS       Bedrock2
     sel4           IronFleet
     FSCQ           RustBelt
     Vellvm         Iris
     ...            ...
*)

(* ================================================================= *)
(** ** These Lectures *)

(** Reasoning about _monadic_ (effectful) programs in Coq.

One approach that touches on many recurring themes at OPLSS and in
formalizations in dependent type theory.  *)

(* ================================================================= *)
(** ** Lecture Plan *)

(**
- Formalizing Imperative Program Semantics in Coq: [Imp]
- Monads, Equivalences, Monad Laws
- Free Monads
- ITrees: Nontermination & Loops
- [Imp] Semantics, Denotationally
- Relational Reasoning
- Hoare Logic via Relational Reasoning
- [Imp] Optimizations
- Going Further: Vellvm ... Related Work
*)

(* ================================================================= *)
(** ** Coq Code *)

(** These lecture slides are extracted from a literate Coq development in the
style of Pierce et al.'s _Software Foundations_.

- link to the source in the OPLSS slack
- assumes background of SF Volume 1 (and some parts of Volume 2)
- contains extended versions of much of the content
- is _work-in-progress_:  feedback welcome!

*)

(* ================================================================= *)
(** ** OPLSS Connections *)

(**
- Coq _is_ a dependent type theory
- Logical Relations & Relational Reasoning
- Foundations of proof theory
- Algebra of Programming
- Program Verification
- Monads: Information Flow & Probabilistic Programming
*)

(* 2024-06-13 11:26 *)
