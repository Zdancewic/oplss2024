(** *** Verified Compilers *)

(**

           Imp          ======[compile]======>        Asm
            |                                          |
            V                                          V
        itree MemE                            itree (RegE +' MemE)
            |                                          |
            |                                          V
            |                                stateT reg (itree MemE)
            |                                          |
            V                                          V
   stateT mem (itree voidE)     ≈[R]    stateT reg (stateT mem (itree voidE))

Where R is the relationship between source "memory" and target "memory".

See the Interaction Trees library tutorial.
*)

(* ----------------------------------------------------------------- *)
(** *** Vellvm - LLVM IR Semantics in Coq *)

(** Large-scale formal semantics for the LLVM IR programming language.*)

(* ----------------------------------------------------------------- *)
(** *** Pointers to Related Work *)

(**
Interaction Trees & Their Uses:

- Interaction Trees [POPL 2020]
- C4: Verified Transactional Objects [OOPSLA 2022]
- Vellvm [ICFP 2021]
- DeepSpec WebServer / Network Testing

Monadic Reasoning:

- Dijkstra Monads (For All / For Free / Forever / ...)  _Maillaird, Hrițcu, et al._

- Formal Reasoning About Layered Monadic Interpreters  _Yoon, Zakowski, Zdancewic_ [ICFP 22]

Relational Reasoning:

- Simple relational correctness proofs for static analyses and program transformations [Benton]

- The Next 700 Relational Program Logics  _Maillaird, Hrițcu, et al._

*)

(* 2024-06-07 10:32 *)
