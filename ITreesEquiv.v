From Paco Require Import paco.
From Coq Require Import Nat String RelationClasses Morphisms Psatz.
From RIP Require Import Imp Utils Maps ImpDenotation.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts HeterogeneousRelations.
Import ITreeNotations.

(* ================================================================= *)
(** ** [itree E] as a Monad *)

(** We saw that [itree E] supports the monad operations, but to be a valid
instance we  must also define [eqM] and prove the [MonadLaws]. *)

(** What is the right notion of "equivalence" for itrees [t1] and [t2 : itree E R]?

             t1 ≈ t2 : itree E R
*)

(* ----------------------------------------------------------------- *)
(** *** Strong Bisimulations *)

(** Because [itree] is a _coinductive_ data structure, it can represent
"infinite" trees. The intuitive notion of equivalence is also _coinductive_.*)

(** _Strong Bisimulation_:

- intuitively, _unroll_ the two trees and compare them structurally for equality.
- we write this as [t1 ∼ t2]

We can prove the monad laws up to strong bisimulation.
*)


(* ----------------------------------------------------------------- *)
(** *** Weak Bisimulation *)

(** We want to treat [Tau] as an "internal" step of computation, which means
that we should (mostly) ignore them for the purposes of determining whether
two trees are equivalent. *)

(** _Weak Bisimulation_:

- intuitively, _unroll_ the two trees
- "ignore" [Tau] nodes on each side, then check for equality



We write this as [t1 ≈ t2].

This justifies the following equivalence:

- [Tau t ≈ t]
- "equivalent up to Tau" (or, [eutt])

*)



(* ----------------------------------------------------------------- *)
(** *** Laws for Iteration *)

(** Using weak bisimulation, we can define laws that show that iteration behaves
well with sequential composition. *)

Section IterLaws.

  Context {E : Type -> Type}.
  Context {I R : Type}.
  Context (step : I -> itree E (I + R)).

  Example iter_unroll_law : forall i,
      iter step i
           ≈
      x <- step i ;;
      match x with
      | inl i => iter step i
      | inr v => ret v
      end.
  Proof.
    intros i.
    rewrite unfold_iter_ktree.
    (* NOTE: We'll see this theorem later... *)
    eapply eutt_clo_bind. reflexivity.
    intros. subst.
    destruct u2.
    rewrite tau_eutt. reflexivity. reflexivity.
  Qed.

  (** *** Iter laws, more abstractly *)

  (** If we work with the so-called Kleisli category where "functions"
  (morphisms) have type [A -> M B] and we write [f >>> g] for function
  composition and ⩯ for pointwise equivalence, we have these rules: *)

(**

●    iter step ⩯ step >>> case (iter step) id

●   (iter step >>> k) ⩯ iter (step >>> bimap k id)

●    iter (iter step) ⩯ iter (step >>> case inl id)
*)


End IterLaws.


(* 2024-06-13 11:26 *)
