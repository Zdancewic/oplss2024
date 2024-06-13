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
- Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq [POPL 2023]
- Semantics for Noninterference with Interaction Trees [ECOOP 2023]

Free Monads / Algebraic Effects:

- Papers by Matija Pretnar, Plotkin, Power (especialy Handling Algebraic Effects [CCS 2012]

Monadic Reasoning:

- Dijkstra Monads (For All / For Free / Forever / ...)  _Maillaird, Hrițcu_ et al.

- Formal Reasoning About Layered Monadic Interpreters  _Yoon, Zakowski, Zdancewic_ [ICFP 22]

Relational Reasoning:

- Simple relational correctness proofs for static analyses and program transformations [Benton POPL 2004]

- The Next 700 Relational Program Logics  _Maillaird, Hrițcu_ et al

Coinduction:

- The power of parameterization in coinductive proof, _Hur_ et al. [POPL 13]

- Anything by _Damien Pous_, but especially: Coinduction All the Qay Up

*)

(* 2024-06-13 11:26 *)
