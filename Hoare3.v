From Paco Require Import paco.
From Coq Require Import Nat String RelationClasses Morphisms Psatz FunctionalExtensionality.
From RIP Require Import Maps Imp Utils ImpDenotation ImpEquiv Hoare.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts HeterogeneousRelations.
Import ITreeNotations.

#[local]
Hint Rewrite aexp_pure_aeval bexp_pure_beval : opt.

(* ----------------------------------------------------------------- *)
(** *** Reasoning About Imp programs *)

(** We saw that we can use the equational theory of the monad laws, along with
  some monad-specific properties to prove program transformations.

  What if we want to prove other things about our programs?
*)

Section EqMR.


  (** *** Generalizing [EqM] *)

  (** Recall  [eqM : forall A, M A -> M A -> Prop] , in particular our insistance
   that bind be [Proper].
  *)

  (** Idea: generalize to a binary, heterogeneous relation:
      [eqMR : forall A B, M A -> M B -> Prop]
  *)

(* ----------------------------------------------------------------- *)
(** *** More General Typeclass of "Related" Computations *)
  (**

Definition relH A B := A -> B -> Prop

*)

Class EqMR (M : Type -> Type) : Type :=  {
    eqMR : forall {A B : Type} (R : relationH A B),
      relationH (M A) (M B)
}.

End EqMR.

(** Assuming [R : relationH A B] *)

Notation "t1 ≈[ R ] t2" := (eutt R t1 t2)
                             (at level 20).

(** [eutt R t1 t2] is weak bisimulation of trees whose leaves (i.e. the return nodes)
   are related by [R].

 *)

Example eutt_trees : (Vis (Read "X") (fun n => Ret n))
                       ≈[ lt ]
                     (Vis (Read "X") (fun n => Ret (1 + n))).
Proof.
  apply eqit_Vis.
  intros u.
  apply eqit_Ret.
  auto.
Qed.

(** Note: we can _recover_ the ordinary [eqM] by instantiating [R] with [eq]. *)

(* ----------------------------------------------------------------- *)
(** *** Intuition: [eqMR] *)

(** The [R] parameter lets us specify a kind of "postcondition" that
    lets is an assertion about the values returned by the computation.

    In particular, if a tree is related to _itself_ with a given [R], i.e.:

  t ≈[R] t

    then we can think of the _diagonal_ of [R] as a predicate on the
    returned values.
 *)

(* ----------------------------------------------------------------- *)
(** *** Logical relation for (itree) [ret] *)

Check (@eutt_Ret).

(** For [eqM], we didn't have to justify that [ret] was [Proper]. But
for this version, we have to show that it is.

    eqMR_Ret
     : forall (E : Type -> Type)
              (R1 R2 : Type)
              (RR : relationH R1 R2)
              (r1 : R1) (r2 : R2),

      RR r1 r2
      <->
      Ret r1 ≈[RR] Ret r2
*)

(* ----------------------------------------------------------------- *)
(** *** Logical relation for [bind] *)
Check (@eutt_clo_bind).

(** The generalization of [Proper] for [bind] looks like this:

eqMR_bind
     : forall (E : Type -> Type)
              (R1 R2 : Type) (RR : relationH R1 R2)
              (U1 U2 : Type) (UU : relationH U1 U2)

              (t1 : itree E U1)
              (t2 : itree E U2)

              (k1 : U1 -> itree E R1)
              (k2 : U2 -> itree E R2),

       (* logically-related initial trees *)
       t1 ≈[UU] t2 ->

       (* logically-related continuations *)
       (forall (u1 : U1) (u2 : U2), UU u1 u2 -> k1 u1 ≈[ RR] k2 u2) ->

       (* yield logically-related computations built with bind *)
       (x <- t1;; k1 x) ≈[RR] (x <- t2;; k2 x)
*)

(* ----------------------------------------------------------------- *)
(** *** Expected Properties Of [EqMR] *)

(** [EqMR]

- If [R] is a an equivalence then so is [≈[R]]

- Monotonicity: if [R1 ⊆ R2] then [≈[R1] ⊆ ≈[R2]]

- General notion of the "image" of a monadic computation (useful for inversion principles).

Definition imageH m a1 a2 := forall R, PER R -> m ≈[R] m -> R a1 a2.
Definition image m a := imageH m a a.
Notation "a ∈ m" := (image m a)
*)



(* ----------------------------------------------------------------- *)
(** *** Semantic Definition of Hoare Triples *)

(** Predicates on the Imp memory state:

Definition Assertion := mem -> Prop.
*)

Definition hoare_itree_triple (P:Assertion) (c:com) (Q:Assertion) :=
  forall σ, P σ ->
       (ℑ ⟦c⟧ σ)
         ≈[(fun '(σ1,_) '(σ2,_) => σ1 = σ2 /\ Q σ1)]
       (ℑ ⟦c⟧ σ).

Notation "⦃ P ⦄  c  ⦃ Q ⦄" :=
  (hoare_itree_triple P c Q)

    (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(* ----------------------------------------------------------------- *)
(** *** Proofs of Hoare Inference Rules *)

Theorem hoare_itree_skip : forall P,
     ⦃P⦄ skip ⦃P⦄.
Proof.
  intros P.
  unfold hoare_itree_triple.
  cbn.
  intros.
  rewrite interp_state_ret. apply eutt_Ret. intuition.
Qed.

Theorem hoare_itree_seq : forall P Q R c1 c2,
     ⦃Q⦄ c2 ⦃R⦄ ->
     ⦃P⦄ c1 ⦃Q⦄ ->
     ⦃P⦄ c1; c2 ⦃R⦄.
Proof.
  unfold hoare_itree_triple.
  intros P Q R c1 c2 H1 H2 st PRE.
  cbn.
  norm.
  eapply eutt_clo_bind. apply H2; auto.
  destruct u1, u2. intros [MEQ QM].
  subst. simpl.
  eapply H1; auto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Hoare rules for Assignment *)

Theorem hoare_itree_asgn : forall Q X a,
  ⦃Q [X |-> a]⦄ X := a ⦃Q⦄.
Proof.
  unfold hoare_itree_triple.
  intros Q X a σ HQ.
  cbn.
  norm. cbn.
  apply eutt_Ret. intuition.
Qed.

(** An alternative formulation that works better for forward reasoning. *)

Theorem hoare_itree_asgn' : forall P X a,
    ⦃P⦄
      X := a
    ⦃ fun (σ:mem) => exists σ', σ = (X !-> (aeval σ' a) ; σ') /\ P σ' ⦄.
Proof.
  unfold hoare_itree_triple.
  intros P X a σ H.
  cbn.
  norm.
  apply eutt_Ret. simpl.
  split. reflexivity.
  exists σ. split. reflexivity. assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Hoare rules for Conditionals *)

Theorem hoare_itree_if : forall P Q (b:bexp) c1 c2,
  ⦃ P /\ b ⦄ c1 ⦃Q⦄ ->
  ⦃ P /\ ~ b⦄ c2 ⦃Q⦄ ->
  ⦃P⦄ if b then c1 else c2 end ⦃Q⦄.
Proof.
  intros P Q b c1 c2 H H0.
  unfold hoare_itree_triple.
  intros σ HS.
  cbn.
  norm.
  cbn.
  destruct (beval σ b) eqn:HB.
  - apply H. intuition.
  - apply H0. intuition. simpl in H1. rewrite HB in H1. inversion H1.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Hoare rules for While Loop *)

Theorem hoare_itree_while : forall P (b:bexp) c,
  ⦃P /\ b⦄ c ⦃P⦄ ->
  ⦃P⦄ while b do c end ⦃P /\ ~ b⦄.
Proof.
  intros P b c H.
  unfold hoare_itree_triple.
  einit.
  ecofix CIH.
  intros σ HS.
  cbn.
  rewrite unfold_repeat.
  rewrite bind_bind.
  (* TODO SAZ: [norm] loops here for some reason. *)
  rewrite interp_state_bind.
  ebind.
  apply pbc_intro_h with (RU := fun '(st1, b1) '(st2, b2) => st1 = st2 /\ st1 = σ /\ b1 = b2 /\ b1 = beval σ b).
  - norm.
    apply eqit_Ret. intuition.
  - intros.
    destruct u1, u2.
    destruct H0 as [? [? [? ?]]].
    subst.
    simpl.
    destruct (beval σ b) eqn:HB.
    + norm.
      unfold hoare_itree_triple in H.
      specialize (H σ (conj HS  HB)).
      ebind.
      econstructor. apply H.
      intros.
      destruct u1, u2.
      intuition. subst.
      norm.
      cbn. rewrite interp_state_tau. estep.
    + norm.
      estep. intuition.
      rewrite HB in H0. inversion H0.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Hoare rules for logical consequence *)

Theorem hoare_itree_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃P'⦄ c ⦃Q⦄ ->
  P ->> P' ->
  ⦃P⦄ c ⦃Q⦄.
Proof.
  intros P P' Q c Htriple Hpre.
  unfold hoare_itree_triple in *.
  intros σ H.
  apply Htriple.
  apply Hpre.
  assumption.
Qed.

Theorem hoare_itree_consequence_conj : forall (P Q Q' : Assertion) c,
  ⦃P⦄ c ⦃Q⦄ ->
  ⦃P⦄ c ⦃Q'⦄ ->
  ⦃P⦄ c ⦃Q /\ Q'⦄.
Proof.
  intros P Q Q' c H1 H2.
  unfold hoare_itree_triple in *.
  intros σ H.
  specialize (H1 σ H).
  specialize (H2 σ H).
  specialize (eutt_conj _ _ H1 H2).
  eapply eqit_mon; eauto.
  intros.
  destruct x0, x1. intuition.
Qed.

Theorem hoare_itree_consequence_post : forall (P Q Q' : Assertion) c,
  ⦃P⦄ c ⦃Q'⦄ ->
  Q' ->> Q ->
  ⦃P⦄ c ⦃Q⦄.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  unfold hoare_itree_triple in *.
  eapply eqit_mon with (RR := (fun '(σ1, _) '(σ2, _) => σ1 = σ2 /\ Q σ1) ); eauto.
  intros.
  destruct x0, x1.
  intuition.
  apply c. assumption.
Qed.

Theorem hoare_itree_consequence : forall (P P' Q Q' : Assertion) c,
  ⦃P'⦄ c ⦃Q'⦄ ->
  P ->> P' ->
  Q' ->> Q ->
  ⦃P⦄ c ⦃Q⦄.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_itree_consequence_pre with (P' := P').
  - apply hoare_itree_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Vacuous assertions *)
Theorem hoare_itree_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  ⦃P⦄ c ⦃Q⦄.
Proof.
  intros P Q c HQ. revert P.
  induction c.
  - intros P. eapply hoare_itree_consequence_post. apply hoare_itree_skip. red.
    intros. apply HQ.
  - intros P.
    unfold hoare_itree_triple. intros.
    cbn.
    norm.
    apply eutt_Ret. intuition.
  - intros P.
    eapply hoare_itree_seq. eapply IHc2. eapply IHc1.
  - intros P.
    eapply hoare_itree_if. apply IHc1.
    apply IHc2.
  - intros P.
    eapply hoare_itree_consequence_pre with (P' := Q).
    eapply hoare_itree_consequence_post.
    apply hoare_itree_while.
    apply IHc.
    intuition.
    intuition.
Qed.

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)
Theorem hoare_itree_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  ⦃P⦄ c ⦃Q⦄.
Proof.
  intros P Q c H. unfold hoare_itree_triple.
  intros st HP.
  unfold not in H. apply H in HP.
  contradiction.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Hoare logic respects the semantics *)
Lemma semantic_preservation : forall (P Q : Assertion) (c1 c2 : com),
    (forall σ, P σ -> ℑ⟦c1⟧σ ≈ ℑ⟦c2⟧σ) ->
    ⦃P⦄ c1 ⦃Q⦄ ->
    ⦃P⦄ c2 ⦃Q⦄.
Proof.
  intros P Q c1 c2 EQ HC1.
  unfold hoare_itree_triple in HC1.
  intros σ HS.
  specialize (EQ σ HS).
  rewrite <- EQ.
  apply HC1. assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** *** An Example *)
Example hoare_itree_if_example :
  ⦃True⦄
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  ⦃X <= Y⦄.
Proof.
  apply hoare_itree_if.
  - eapply hoare_itree_consequence_pre.
    + apply hoare_itree_asgn.
    + assertion_auto'.
  - eapply hoare_itree_consequence_pre.
    + apply hoare_itree_asgn.
    + assertion_auto'.
Qed.


(* 2024-06-13 11:26 *)
