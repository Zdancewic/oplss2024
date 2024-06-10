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
  (morphisms) are of the type [A -> M B] and we write [f >>> g] for function
  composition and ⩯ for pointwise equivalence, we have these rules: *)

(**

●    iter step ⩯ step >>> case (iter step) id

●   (iter step >>> k) ⩯ iter (step >>> bimap k id)

●    iter (iter step) ⩯ iter (step >>> case inl id)
*)


End IterLaws.

(* ================================================================= *)
(** ** Relational Equivalence *)

Module EqMR.

(** Heterogeneous binary relations: *)

  Definition relationH (A B : Type) := A -> B -> Prop.

Section EqmR.

  (** We consider heterogeneous relations on computations parameterized by a
     relation on the return types *)
  Class EqmR (m : Type -> Type) : Type :=
    { eqmR : forall {A B : Type} (R : relationH A B), relationH (m A) (m B) }.

End EqmR.
Infix "≈{ R  }" := (eqmR R) (at level 30) : cat_scope.
Notation "t1 ≋ t2" := (eqmR eq t1 t2) (at level 40) : cat_scope.

Arguments eqmR {m _ A B}.

Import RelNotations.
Local Open Scope relationH_scope.

End EqMR.

(* 2024-06-07 10:32 *)
