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
(** *** More General Typeclass *)
  (**

Definition relationH A B := A -> B -> Prop

*)

  Class EqMR (M : Type -> Type) : Type :=  {
      eqMR : forall {A B : Type} (R : relationH A B), relationH (M A) (M B)
  }.

End EqMR.

(** Assuming [R : relationH A B] *)

Notation "t1 ≈[ R ] t2" := (eutt R t1 t2) (at level 20).

(** Note: we can _recover_ the ordinary [eqM] by instantiating [R] with [=] :

eqM := eqMR eq
*)

(* ----------------------------------------------------------------- *)
(** *** Logical relation for (itree) [ret] *)

Check (@eutt_Ret).

(** For [eqM], we didn't have to justify that [ret] was [Proper]. But
for this version, we have to show that it is.

    eqMR_Ret
     : forall (E : Type -> Type) (R1 R2 : Type) (RR : relH R1 R2) (r1 : R1) (r2 : R2),
      RR r1 r2 <-> Ret r1 ≈[ RR] Ret r2
*)

(* ----------------------------------------------------------------- *)
(** *** Logical relation for [bind] *)
Check (@eutt_clo_bind).
(** The generalization of [Proper] for [bind] looks like this:

eqMR_bind
     : forall (E : Type -> Type) (R1 R2 : Type) (RR : relH R1 R2) (U1 U2 : Type)
         (UU : relH U1 U2) (t1 : itree E U1) (t2 : itree E U2) (k1 : U1 -> itree E R1)
         (k2 : U2 -> itree E R2),
       t1 ≈[ UU] t2 ->
       (forall (u1 : U1) (u2 : U2), UU u1 u2 -> k1 u1 ≈[ RR] k2 u2) ->
       (x <- t1;; k1 x) ≈[ RR] (x <- t2;; k2 x)
*)

(* ----------------------------------------------------------------- *)
(** *** Expected Properties Of [EqMR] *)

(** [EqMR]

- If [R] is a an equivalence then so is [≈[RR]]

- Monotonicity: if [R1 ⊆ R2] then [≈[R1] ⊆ ≈[R2]]

- General notion of the "image" of a monadic computation (useful for inversion principles).

Definition imageH m a1 a2 := forall R, PER R -> m ≈[R] m -> R a1 a2.
Definition image m a := imageH m a a.
Notation "a ∈ m" := (image m a)
*)


(* ----------------------------------------------------------------- *)
(** *** Semantic Definition of Hoare Triples *)

Definition hoare_itree_triple (P:Assertion) (c:com) (Q:Assertion) :=
  forall σ, P σ -> eutt (fun '(σ1,_) '(σ2,_) => σ1 = σ2 /\ Q σ1) (ℑ ⟦c⟧ σ) (ℑ ⟦c⟧ σ).

Notation "⦃ P ⦄  c  ⦃ Q ⦄" :=
  (hoare_itree_triple P c Q) (at level 90, c custom com at level 99)
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
  ⦃P⦄ X := a ⦃ fun (σ:mem) => exists σ', σ = (X !-> (aeval σ' a) ; σ') /\ P σ' ⦄.
Proof.
  unfold hoare_itree_triple.
  intros P X a σ H.
  cbn.
  norm.
  apply eutt_Ret. simpl.
  split. reflexivity.
  exists σ. split. reflexivity. assumption.
Qed.

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

(* ================================================================= *)
(** ** Substitution *)

Fixpoint substitute_aexp (x:string) (ax:aexp) (a:aexp) : aexp :=
  match a with
  | ANum n => a
  | AId y => if String.eqb y x then ax else a
  | <{ a1 + a2 }> => <{ (substitute_aexp x ax a1) + (substitute_aexp x ax a2) }>
  | <{ a1 - a2 }> => <{ (substitute_aexp x ax a1) - (substitute_aexp x ax a2) }>
  | <{ a1 * a2 }> => <{ (substitute_aexp x ax a1) * (substitute_aexp x ax a2) }>
  end.

Eval compute in (substitute_aexp X (<{ Y + 2}>) (<{ X + Z }>)).

Lemma aexp_eval_semantics2 : forall a1 a2 σ,
    (aeval σ a1 = aeval σ a2) <->
      ℑ ⟦ a1 ⟧a σ ≈ ℑ ⟦ a2 ⟧a σ.
Proof.
  intros.
  split.
  - intros H.
    norm.
    rewrite H.
    reflexivity.
  - intros H.
    unfold aexp_equiv in H.
    do 2 rewrite aexp_pure_aeval in H.
    apply eutt_Ret in H.
    inversion H.
    reflexivity.
Qed.

Lemma substitute_aexp_aeval : forall (x:string) ax a,
  forall σ (EQ : aeval σ <{ x }> = aeval σ ax),
    aeval σ a = aeval σ (substitute_aexp x ax a).
Proof.
  intros x ax a σ EQ.
  induction a; simpl; auto.
  destruct (String.eqb_spec x0 x).
  - simpl in EQ. subst. assumption.
  - reflexivity.
Qed.

Lemma substitute_aexp_semantic : forall (x:string) ax a,
  forall σ (EQ: ℑ ⟦ <{ x }> ⟧a σ ≈ ℑ ⟦ ax ⟧a σ),
    ℑ ⟦ a ⟧a σ ≈ ℑ ⟦ substitute_aexp x ax a ⟧a σ.
Proof.
  intros x ax a σ HEQ.
  apply aexp_eval_semantics2.
  intros. apply substitute_aexp_aeval.
  apply aexp_eval_semantics2.
  assumption.
Qed.

Lemma bexp_eval_semantics : forall b1 b2 σ,
    (beval σ b1 = beval σ b2) <->
      ℑ ⟦ b1 ⟧b σ ≈ ℑ ⟦ b2 ⟧b σ.
Proof.
  intros.
  split.
  - intros H.
    norm.
    rewrite H.
    reflexivity.
  - intros H.
    unfold bexp_equiv in H.
    do 2 rewrite bexp_pure_beval in H.
    apply eutt_Ret in H.
    inversion H.
    reflexivity.
Qed.

Fixpoint substitute_bexp (x:string) (ax:aexp) (b:bexp) : bexp :=
  match b with
  | <{true}>      => b
  | <{false}>     => b
  | <{a1 = a2}>   => <{ (substitute_aexp x ax a1) = (substitute_aexp x ax a2) }>
  | <{a1 <> a2}>   => <{ (substitute_aexp x ax a1) <> (substitute_aexp x ax a2) }>
  | <{a1 <= a2}>  => <{ (substitute_aexp x ax a1) <= (substitute_aexp x ax a2) }>
  | <{a1 > a2}>   => <{ (substitute_aexp x ax a1) > (substitute_aexp x ax a2) }>
  | <{~ b1}>      => <{~ (substitute_bexp x ax b1) }>
  | <{b1 && b2}>  => <{ (substitute_bexp x ax b1) && (substitute_bexp x ax b2) }>
  end.

Lemma substitute_bexp_beval : forall (x:string) ax b,
  forall σ (EQ : aeval σ <{ x }> = aeval σ ax),
    beval σ b = beval σ (substitute_bexp x ax b).
Proof.
  intros x ax b σ EQ.
  induction b; simpl; try reflexivity.
  - repeat rewrite <- (substitute_aexp_aeval x ax); auto.
  - repeat rewrite <- (substitute_aexp_aeval x ax); auto.
  - repeat rewrite <- (substitute_aexp_aeval x ax); auto.
  - repeat rewrite <- (substitute_aexp_aeval x ax); auto.
  - rewrite IHb. reflexivity.
  - rewrite IHb1, IHb2. reflexivity.
Qed.

Lemma substitute_bexp_semantic : forall (x:string) ax b,
  forall σ (EQ: ℑ ⟦ <{ x }> ⟧a σ ≈ ℑ ⟦ ax ⟧a σ),
    ℑ ⟦ b ⟧b σ ≈ ℑ ⟦ substitute_bexp x ax b ⟧b σ.
Proof.
  intros x ax a σ HEQ.
  apply bexp_eval_semantics.
  intros. apply substitute_bexp_beval.
  apply aexp_eval_semantics2.
  assumption.
Qed.

Fixpoint contains (x:string) (a:aexp) : bool :=
  match a with
  | ANum n => false
  | AId y => String.eqb y x
  | <{ a1 + a2 }> => (contains x a1 || contains x a2)%bool
  | <{ a1 - a2 }> => (contains x a1 || contains x a2)%bool
  | <{ a1 * a2 }> => (contains x a1 || contains x a2)%bool
  end.

Lemma contains_false_equiv: forall (y:string) a,
    contains y a = false ->
    forall (σ:state) n, aeval σ a = aeval ( y !-> n ; σ ) a.
Proof.
  intros y.
  induction a; intros HC σ m; simpl in *; try reflexivity.
  - destruct (String.eqb_spec x y).
    + inversion HC.
    + rewrite t_update_neq; auto.
  - apply Bool.orb_false_elim in HC.
    destruct HC as [HA1 HA2].
    auto.
  - apply Bool.orb_false_elim in HC.
    destruct HC as [HA1 HA2].
    auto.
  - apply Bool.orb_false_elim in HC.
    destruct HC as [HA1 HA2].
    auto.
Qed.

(** Because commands are not pure, we can't blindly substitute. *)

Fixpoint substitute_com (x:string) (ax:aexp) (c:com) : (com * bool) :=
  match c with
  | <{ skip }> => (c, false)
  | <{ y := a }> =>
      let a' := substitute_aexp x ax a in
      (<{ y := a' }>, ((y =? x)%string || contains y ax)%bool)
  | <{ c1 ; c2 }> =>
      let '(c1', stop) := substitute_com x ax c1 in
      if stop
      then (<{ c1' ; c2 }>, stop)
      else
        let '(c2', stop) := substitute_com x ax c2 in
        (<{ c1' ; c2' }>, stop)
  | <{ if b then c1 else c2 end }> =>
      let '(c1', stop1) := substitute_com x ax c1 in
      let '(c2', stop2) := substitute_com x ax c2 in
      (<{ if (substitute_bexp x ax b) then c1' else c2' end }>, (stop1 || stop2)%bool)
  | <{ while b do c end }> =>
      let '(c', stop) := substitute_com x ax c in
      if stop then (<{ while b do c end }>, true)
      else (<{ while (substitute_bexp x ax b) do c' end}>, false)
  end.

(** Examples of when it is OK (or not) to substitute: *)
Eval compute in substitute_com X 0 <{ Z := 3; Y := X + X ; Y := X }>.
Eval compute in substitute_com X 0 <{ X := 3; X := X + X ; Y := X }>.

(** Define an invariant that says when we can safely substitute the
expression  <{ ax }> for <{ x }> in a state σ.  *)
Definition subst_invariant x ax σ :=
  aeval σ <{ x }> = aeval σ ax.

(** Define the relational post condition for reasoning about the
results of substitution. *)

Definition post_condition x ax b (σ:state) :=
  fun σ1 σ2 =>
    σ1 = σ2
    /\ (b = false -> (σ1 x = σ x /\ aeval σ ax = aeval σ1 ax /\ subst_invariant x ax σ1)).

#[local]
 Instance post_condition_refl : forall x ax σ,
    Reflexive (post_condition x ax true σ).
Proof.
  intros.
  red.
  intros.
  unfold post_condition.
  split. reflexivity. intros. inversion H.
Qed.

Lemma post_condition_mono : forall x ax σ st1 st2 b1 b2,
    (b1 = true -> b2 = true) ->
    post_condition x ax b1 σ st1 st2 ->
    post_condition x ax b2 σ st1 st2.
Proof.
  intros.
  unfold post_condition in *.
  intuition.
  - destruct b1.
    + rewrite H in H0. inversion H0. reflexivity.
    + apply H2. reflexivity.
  - destruct b1.
    + rewrite H in H0. inversion H0. reflexivity.
    + apply H2. reflexivity.
  - unfold subst_invariant in *. destruct b1.
    + intuition. subst.  inversion H3.
    + intuition.
Qed.

Lemma substitute_com_correct1 :
  forall x ax c c' b
    (HS: substitute_com x ax c = (c', b)),
    forall σ (P: subst_invariant x ax σ),
        eutt (prod_rel (post_condition x ax b σ) eq)
             (ℑ ⟦c⟧ σ)
             (ℑ ⟦c'⟧ σ).
Proof.
  intros x ax c.
  induction c; intros; simpl in HS; inversion HS; subst; simpl; norm.
  - apply eutt_Ret. unfold post_condition. auto.
  - apply eutt_Ret.
    simpl.
    constructor; auto.
    split; simpl; auto.
    + rewrite <- substitute_aexp_aeval; auto.
    + intros H.
      destruct (String.eqb_spec x0 x).
      * subst. simpl in H. inversion H.
      * repeat split.
       -- rewrite Bool.orb_false_l in H.
          unfold subst_invariant in P.
          apply t_update_neq.
          assumption.
       -- simpl in H.
          erewrite contains_false_equiv. reflexivity.
          assumption.
       -- rewrite Bool.orb_false_l in H.
          unfold subst_invariant in *.
          erewrite <- contains_false_equiv.
          erewrite <- contains_false_equiv; assumption.
          cbn. apply eqb_neq. auto.
  - destruct (substitute_com x ax c1).
    specialize (IHc1 c b0 eq_refl σ P).
    destruct b0.
    + inversion HS. subst.
      cbn.
      norm.
      eapply eutt_clo_bind.
      apply IHc1.
      intros u1 u2 HP.
      destruct u1, u2, u, u0.
      cbn.
      destruct HP as [HM _].
      destruct HM. simpl in H.
      subst.
      reflexivity.
    + destruct (substitute_com x ax c2).
      inversion HS. subst.
      cbn.
      norm.
      eapply eutt_clo_bind.
      apply IHc1.
      intros u1 u2 HP.
      destruct u1, u2, u, u0.
      cbn.
      destruct HP as [[HM H]].
      simpl in HM.
      subst.
      specialize (H eq_refl).
      destruct H as [HM HE].
      simpl in *.
      destruct HE as [HE H].
      specialize (IHc2 c0 b eq_refl m0 H).
      eapply eutt_subrel.
      2: { apply IHc2. }
      intros. unfold post_condition in H1.
      inversion H1.
      destruct a, u, b0, u.
      constructor; auto.
      unfold post_condition.
      intuition.
  - destruct (substitute_com x ax c1).
    destruct (substitute_com x ax c2).
    cbn.
    inversion HS. subst.
    cbn.
    norm.
    cbn.
    rewrite <- substitute_bexp_beval; auto.
    destruct (beval σ b).
    + eapply eutt_subrel.
      2:{ apply IHc1; auto. }
      intros. constructor.
      eapply post_condition_mono.
      2: { apply H. }
      intros. intuition.
      inversion H; auto.
    + eapply eutt_subrel.
      2: { apply IHc2; auto. }
      intros.
      constructor.
      eapply post_condition_mono.
      2: { apply H. }
      intros. intuition.
      inversion H; auto.
  - destruct (substitute_com x ax c).
    destruct b1.
    + inversion HS. subst.
      reflexivity.
    + inversion HS.
      subst. clear HS H0.
      cbn.
      specialize (IHc c0 false eq_refl).
      eapply eutt_subrel.
      2 : { eapply eutt_interp_state_iter with (RS := post_condition x ax false σ)(RA := eq)(RB := eq).
            intros.
            unfold subst_invariant in *.
            intuition. subst.
            norm. cbn.
            rewrite <- substitute_bexp_beval.
            unfold post_condition in H.
            intuition.  subst.
            unfold subst_invariant in H3.
            destruct (beval s2 b).
            norm.
            eapply eutt_clo_bind.
            apply IHc. assumption.
            intros. norm.  destruct u1. destruct u2.
           apply eutt_Ret. cbn. apply prod_morphism. simpl.
           apply fst_rel in H0. simpl in H0. unfold post_condition in H0. intuition.
           subst.
           unfold post_condition.
           split; auto.
           intros. intuition.
           eapply snd_rel in H0. cbn. cbn in H0. subst. econstructor. reflexivity.
           norm. apply eutt_Ret. apply prod_morphism. simpl.
           unfold post_condition.
           split; auto. cbn.  constructor. reflexivity.
           unfold post_condition in H.
           intuition.  subst. unfold subst_invariant in H3. subst.
           intuition.
           unfold subst_invariant in *.
           unfold post_condition.
           split; auto.
           reflexivity. }
      intros.
      destruct a, b0.
      cbn in *.
      apply prod_morphism.
      cbn.  intuition.  cbn. intuition.
Qed.

Fixpoint com_append (c1 c2 : com) : com :=
  match c1 with
  | <{ skip }> => c2
  | <{ c11 ; c12}> => <{ c11 ; (com_append c12 c2) }>
  | _ => <{ c1 ; c2 }>
  end.

(* TODO: This proof can be cleaned up using ImpEquiv *)
Lemma com_append_correct : forall c1 c2,
    com_append c1 c2 ≡ <{ c1 ; c2 }>.
Proof.
  induction c1; intro c2; simpl; try reflexivity.
  - rewrite skipL_sound. reflexivity.
  - rewrite seqA_sound. rewrite IHc1_2. reflexivity.
Qed.

#[global]
 Instance Proper_com_append: Proper (com_eq ==> com_eq ==> com_eq) com_append.
Proof.
  intros c11.
  destruct c11; intros c12 EQ1 c21 c22 EQ2; simpl.
  - rewrite com_append_correct. rewrite <- EQ1. rewrite skipL_sound. assumption.
  - rewrite EQ1. rewrite com_append_correct. rewrite EQ2. reflexivity.
  - rewrite com_append_correct. rewrite com_append_correct. rewrite <- EQ1.
    rewrite seqA_sound. rewrite EQ2. reflexivity.
  - rewrite com_append_correct. rewrite <- EQ1. rewrite EQ2. reflexivity.
  - rewrite com_append_correct. rewrite <- EQ1. rewrite EQ2. reflexivity.
Qed.

Fixpoint com_assocR c : com :=
  match c with
  | <{ skip }> => c
  | <{ y := a }> => c
  | <{ c1 ; c2 }> =>
      let c1' := com_assocR c1 in
      let c2' := com_assocR c2 in
      com_append c1' c2'
  | <{ if b then c1 else c2 end }> =>
      let c1' := com_assocR c1 in
      let c2' := com_assocR c2 in
      <{ if b then c1' else c2' end }>
  | <{ while b do c end }> =>
      let c' := com_assocR c in
      <{ while b do c' end }>
  end.

Lemma com_assocR_correct : forall c,
    c ≡ com_assocR c.
Proof.
  induction c; simpl; try reflexivity.
  - rewrite <- IHc1. rewrite <- IHc2.
    rewrite com_append_correct.
    reflexivity.
  - rewrite <- IHc1. rewrite <- IHc2.
    reflexivity.
  - rewrite <- IHc. reflexivity.
Qed.

Fixpoint propagate_com (c:com) : com :=
  match c with
  | <{ skip }> => c
  | <{ y := a }> => c
  | <{ y := a ; c2 }> =>
      let c2' := propagate_com c2 in
      if contains y a
      then <{ y := a ; c2' }>
      else <{ y := a;  fst (substitute_com y a c2') }>
  | <{ c1 ; c2 }> =>
      let c1' := propagate_com c1 in
      let c2' := propagate_com c2 in
      <{ c1' ; c2' }>
  | <{ if b then c1 else c2 end }> =>
      let c1' := propagate_com c1 in
      let c2' := propagate_com c2 in
      <{ if  b then c1' else c2' end }>
  | <{ while b do c end }> =>
      let c' := propagate_com c in
      <{ while b do c' end }>
  end.

Lemma subst_invariant_good : forall (x:string) a σ,
    contains x a = false ->
    subst_invariant x a (x !-> aeval σ a; σ).
Proof.
  intros.
  unfold subst_invariant.
  eapply contains_false_equiv in H.
  rewrite <- H.
  symmetry.
  simpl.
  rewrite t_update_eq.
  reflexivity.
Qed.

Lemma substitute_com_subst : forall c x a σ,
    contains x a = false ->
    ℑ ⟦ c ⟧ (x !-> aeval σ a; σ) ≈ ℑ ⟦ fst (substitute_com x a c) ⟧ (x !-> aeval σ a; σ).
Proof.
  intros.
  destruct (substitute_com x a c) eqn:HS.
  simpl.
  apply substitute_com_correct1 with (σ := (x !-> aeval σ a; σ)) in HS.
  eapply eutt_subrel.
  2: { apply HS. }
  intros.
  destruct a0, u, b0, u.
  inversion H0; clear H0.
  unfold post_condition in fst_rel.
  simpl in *.
  intuition. subst. tauto.
  apply subst_invariant_good.
  assumption.
Qed.

Lemma propagate_com_sound : forall c,
    c ≊ (propagate_com c).
Proof.
  induction c.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    destruct c1.
    + simpl. rewrite <- IHc2. reflexivity.
    + destruct (contains x a) eqn:H.
      * rewrite <- IHc2. reflexivity.
      * intro.
        cbn.
        norm.
        cbn.
        eapply transitivity.
        apply IHc2.
        apply substitute_com_subst.
        assumption.
    + rewrite <- IHc1. rewrite <- IHc2. reflexivity.
    + simpl in *.
      rewrite IHc1.
      rewrite <- IHc2.
      reflexivity.
    + simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl. rewrite <- IHc. reflexivity.
Qed.

Definition example : com :=
  <{ X := 4 + 5;
     Y := X;
     if ((X - Y) = (2 + 4)) then skip
     else Y := X end;
     if (0 <= (4 - (2 + 1))) then Y := 0
     else skip end;
     while (Y = 0) do
             X := X + 1
             end
    }>.

Eval compute in fold_constants_com (propagate_com example).

Example correct: example ≊ (fold_constants_com (propagate_com example)).
Proof.
  rewrite fold_constants_com_sound.
  apply propagate_com_sound.
Qed.

Fixpoint loop_unroll_while (n:nat) (b:bexp) (c:com) : com :=
  match n with
  | 0 => <{ while b do c end }>
  | S n => <{ if b then c ; (loop_unroll_while n b c) else skip end }>
  end.

Lemma loop_unroll_sound : forall (n:nat) (b:bexp) (c:com),
    <{ while b do c end }> ≡ loop_unroll_while n b c.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite <- IHn.
    apply loop_unroll1_sound_strong.
Qed.

Fixpoint loop_unroll_com n (c:com) : com :=
  match c with
  | <{ skip }> => c
  | <{ y := a }> => c
  | <{ c1 ; c2 }> =>
      let c1' := loop_unroll_com n c1 in
      let c2' := loop_unroll_com n c2 in
      <{ c1' ; c2' }>
  | <{ if b then c1 else c2 end }> =>
      let c1' := loop_unroll_com n c1 in
      let c2' := loop_unroll_com n c2 in
      <{ if  b then c1' else c2' end }>
  | <{ while b do c end }> =>
      loop_unroll_while n b c
  end.

Lemma loop_unroll_com_sound : forall n c,
    c ≊ (loop_unroll_com n c).
Proof.
  induction c.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl. unfold com_equiv. intros σ.
    apply com_eq_subrel_equiv.
    apply loop_unroll_sound.
Qed.

Fixpoint iterate_opt (n:nat) (opt : com -> com) c :=
  match n with
  | 0 => c
  | S n => iterate_opt n opt (opt c)
  end.

Lemma iterate_opt_sound :
  forall n (opt : com -> com)  (OPTSOUND: forall c, c ≊ opt c) c,
    c ≊ iterate_opt n opt c.
Proof.
  intros n opt OPTSOUND.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite <- IHn.
    apply OPTSOUND.
Qed.

Definition optimize (n:nat) (c:com) : com :=
  let c' := com_assocR (loop_unroll_com n c) in
  iterate_opt n (fun c => fold_constants_com (propagate_com c)) c'.

Lemma optimize_sound : forall n c,
    c ≊ optimize n c.
Proof.
  intros n c.
  unfold optimize.
  rewrite <- iterate_opt_sound.
  rewrite <- com_assocR_correct.
  apply loop_unroll_com_sound.
  intros c0.
  rewrite fold_constants_com_sound.
  apply propagate_com_sound.
Qed.

Opaque optimize_sound.

(** Imp code for [factorial] for a specific number: *)
Definition fact_n n := <{ X := n ; fact_in_coq }>.

Definition fact_opt n :=
  optimize (n+1) (fact_n n).

Definition fact_opt8 := fact_opt 8.
Eval compute in com_assocR fact_opt8.

Definition fact_opt5 := fact_opt 5.

Eval compute in fact_n 5.
Eval compute in fact_opt5.

Lemma fact_opt_correct : forall (n:nat),
    <{ X := n ; fact_in_coq }> ≊ fact_opt n.
Proof.
  intros n.
  unfold fact_in_coq.
  apply optimize_sound.
Qed.

Lemma store_store_elimination_correct : forall x a1 a2,
    (contains x a2 = false) ->
    <{ x := a1 ; x := a2 }> ≊ <{ x := a2 }>.
Proof.
  intros x a1 a2 H σ.
  simpl.
  norm.
  cbn.
  apply eutt_Ret.
  specialize (contains_false_equiv x a2 H) as EQ.
  rewrite <- EQ.
  rewrite t_update_shadow.
  reflexivity.
Qed.

Lemma asgn_commutes : forall (x y:string) a1 a2,
    (contains x a2 = false) ->
    (contains y a1 = false) ->
    x <> y ->
    <{ x := a1 ; y := a2 }> ≊ <{ y := a2; x := a1 }>.
Proof.
  intros x y a1 a2 C1 C2 NEQ σ.
  simpl.
  norm.
  cbn.
  apply eutt_Ret.
  simpl.
  specialize (contains_false_equiv x a2 C1) as EQ1.
  rewrite <- EQ1.
  specialize (contains_false_equiv y a1 C2) as EQ2.
  rewrite <- EQ2.
  rewrite t_update_permute; auto.
Qed.

Eval compute in fact_opt5.

(**

x1 = a1 ; x2 = a2 ; x3 = a3 ; c
x1 = x3
x1 = a1 ; x2 = a2 ; x1 = a3 ; c   // x1 <> x2 /\ not (contains x1 a2)  /\ not (contains x2 a3)
x1 = a1 ; x1 = a3 ; x2 = a2 ; c
x1 = a3 ; x2 = a2 ; c             // not contains x1 a3
*)

Fixpoint dead_store_elimination (c:com) : com :=
  match c with
  | <{ skip }> => c
  | <{ x := a }> => c
  | <{ x1 := a1; c2 }> =>
      let c2' := dead_store_elimination c2 in
      match c2' with
      | <{ x2 := a2 }> =>
          if ((String.eqb x1 x2)
              && negb (contains x1 a2))%bool
          then
            <{ x2 := a2 }>
          else
            <{ x1 := a1 ; c2' }>
      | <{ x2 := a2 ; c3' }> =>
          match c3' with
          | <{ x3 := a3 }> =>
              if (String.eqb x1 x3
                  && negb (String.eqb x2 x3)
                  && negb (contains x3 a2)
                  && negb (contains x2 a3)
                  && negb (contains x1 a3))%bool
              then <{ x3 := a3 ; x2 := a2 }>
              else <{ x1 := a1 ; c2' }>
          | <{ x3 := a3 ; c4' }> =>
              if (String.eqb x1 x3
                  &&  negb (String.eqb x2 x3)
                  && negb (contains x3 a2)
                  && negb (contains x2 a3)
                  && negb (contains x1 a3))%bool
              then <{ x3 := a3 ; x2 := a2 ; c4' }>
              else if ((String.eqb x1 x2)
                       && negb (String.eqb x2 x3)
                       && negb (contains x1 a2))%bool
                   then <{ x2 := a2 ; x3 := a3 ; c4' }>
                   else <{ x1 := a1 ; c2' }>
          | _ =>
              if ((String.eqb x1 x2)
                  && negb (contains x1 a2))%bool
              then
                <{ x2 := a2 ; c3' }>
              else
                <{ x1 := a1 ; c2' }>
          end
      | _ => <{ x1 := a1 ; c2' }>
      end
  | <{ c1 ; c2 }> =>
      let c2' := dead_store_elimination c2 in
      <{ c1 ; c2' }>
  | <{ if b then c1 else c2 end }> =>
      let c1' := dead_store_elimination c1 in
      let c2' := dead_store_elimination c2 in
      <{ if  b then c1' else c2' end }>
  | <{ while b do c end }> =>
      let c' := dead_store_elimination c in
      <{ while b do c' end }>
  end.

Eval compute in (dead_store_elimination <{ X := 0 ; Y := 1 ; Y := 2 ; skip }>).
Eval compute in (dead_store_elimination (com_assocR fact_opt5)).
Eval compute in (dead_store_elimination <{ Y := 120; Z := 0; skip }>).
Eval compute in (dead_store_elimination <{ Y:= 0; Y := 120; Z := 0; skip }>).

Lemma dead_store_elimination_correct :
  forall c,
    c ≊ (dead_store_elimination c).
Proof.
  induction c; simpl; try reflexivity.
  - destruct c1; simpl; try (rewrite <- IHc2; try reflexivity).
    + destruct (dead_store_elimination c2); simpl; try (rewrite <- IHc2; try reflexivity).
      * destruct (String.eqb_spec x x0); subst; simpl.
        2: { rewrite IHc2. reflexivity. }
        destruct (contains x0 a0) eqn : HC; simpl.
        1: { rewrite IHc2. reflexivity. }
        rewrite IHc2. apply store_store_elimination_correct; auto.
      * destruct c1; simpl; try (rewrite <- IHc2; try reflexivity).
        destruct c3.
        -- destruct (String.eqb_spec x x0); subst; simpl.
           2:{ rewrite IHc2. reflexivity. }
           destruct (contains x0 a0) eqn : HC; simpl.
           rewrite IHc2. reflexivity.
           rewrite IHc2. rewrite <- seqA_sound. rewrite store_store_elimination_correct; auto.
           reflexivity.
        -- destruct (String.eqb_spec x x1); subst; simpl.
           2: { rewrite IHc2. reflexivity. }
           destruct (String.eqb_spec x0 x1); subst; simpl.
           1: { rewrite IHc2. reflexivity. }
           destruct (contains x1 a0) eqn : HC1; simpl.
           1: { rewrite IHc2. reflexivity. }
           destruct (contains x0 a1) eqn : HC2; simpl.
           1: { rewrite IHc2. reflexivity. }
           destruct (contains x1 a1) eqn : HC3; simpl.
           1: { rewrite IHc2. reflexivity. }
           rewrite IHc2. rewrite asgn_commutes; auto.
           rewrite <- seqA_sound.
           rewrite store_store_elimination_correct; auto.
           reflexivity.
        -- destruct c3_1; simpl.
           ** destruct (String.eqb_spec x x0); subst; simpl.
              2 : { rewrite IHc2. reflexivity. }
              destruct (contains x0 a0) eqn : HC1; simpl.
              1 : { rewrite IHc2.  reflexivity. }
              rewrite IHc2. rewrite <- seqA_sound.
              rewrite store_store_elimination_correct; auto.
              reflexivity.
           ** destruct (String.eqb_spec x x1); subst; simpl.
              1: { destruct (String.eqb_spec x0 x1); subst; simpl.
                   destruct (String.eqb_spec x1 x1); subst; simpl.
                   2: { contradiction. }
                   rewrite IHc2. reflexivity.
                   destruct (contains x1 a0) eqn : HC; simpl.
                   destruct (String.eqb_spec x1 x0); subst; simpl.
                   destruct (contains x0 a) eqn : HC1; simpl.
                   contradiction.
                   contradiction.
                   rewrite <- IHc2. reflexivity.
                   destruct (contains x0 a1) eqn : HC1; subst; simpl.
                   destruct (String.eqb_spec x1 x0); subst.
                   contradiction.
                   simpl.
                   rewrite <- IHc2. reflexivity.
                   destruct (contains x1 a1) eqn : HC2; subst; simpl.
                   destruct (String.eqb_spec x1 x0); subst; simpl.
                   contradiction.
                   rewrite IHc2. reflexivity.
                   rewrite <- seqA_sound in IHc2.
                   rewrite asgn_commutes in IHc2; auto.
                   rewrite seqA_sound in IHc2.
                   rewrite IHc2.
                   rewrite <- seqA_sound.
                   rewrite store_store_elimination_correct; auto.
                   reflexivity. }
              destruct (String.eqb_spec x x0); subst; simpl.
              2: { rewrite <- IHc2. reflexivity. }
              destruct (String.eqb_spec x0 x1); subst; simpl.
              rewrite IHc2. reflexivity.
              destruct (contains x0 a0) eqn : HC; simpl.
              rewrite IHc2. reflexivity.
              rewrite IHc2.
              rewrite <- seqA_sound.
              rewrite store_store_elimination_correct; auto.
              reflexivity.
           ** destruct (String.eqb_spec x x0); simpl; subst.
              destruct (contains x0 a0) eqn : HC; simpl.
              rewrite IHc2. reflexivity.
              rewrite IHc2.
              rewrite <- seqA_sound.
              rewrite store_store_elimination_correct; auto.
              reflexivity.
              rewrite IHc2. reflexivity.
           ** destruct (String.eqb_spec x x0); simpl; subst.
              destruct (contains x0 a0) eqn : HC; simpl.
              rewrite IHc2. reflexivity.
              rewrite IHc2.
              rewrite <- seqA_sound.
              rewrite store_store_elimination_correct; auto.
              reflexivity.
              rewrite IHc2. reflexivity.
           ** destruct (String.eqb_spec x x0); simpl; subst.
              destruct (contains x0 a0) eqn : HC; simpl.
              rewrite IHc2. reflexivity.
              rewrite IHc2.
              rewrite <- seqA_sound.
              rewrite store_store_elimination_correct; auto.
              reflexivity.
              rewrite IHc2. reflexivity.
        -- destruct (String.eqb_spec x x0); simpl; subst.
           destruct (contains x0 a0) eqn : HC; simpl.
           rewrite IHc2. reflexivity.
           rewrite IHc2.
           rewrite <- seqA_sound.
           rewrite store_store_elimination_correct; auto.
              reflexivity.
              rewrite IHc2. reflexivity.
        -- destruct (String.eqb_spec x x0); simpl; subst.
           destruct (contains x0 a0) eqn : HC; simpl.
           rewrite IHc2. reflexivity.
           rewrite IHc2.
           rewrite <- seqA_sound.
           rewrite store_store_elimination_correct; auto.
              reflexivity.
              rewrite IHc2. reflexivity.
  - rewrite <- IHc1, <- IHc2. reflexivity.
  - rewrite <- IHc. reflexivity.
Qed.










(** Example: using verified optimizations to prove an
equivalence between Imp programs. *)

Example opt_fact_sound :
  <{ X := 5;
     Z := X;
     Y := 1;
     while Z <> 0 do
        Y := Y * Z;
        Z := Z - 1
     end }>
    ≊
  <{ X := 5; Z := 0; Y := 120 }>.
Proof.
  rewrite (optimize_sound 6).
  cbn.
  rewrite dead_store_elimination_correct.
  cbn.
  rewrite skipR_sound.
  reflexivity.
Qed.

(* 2024-06-10 19:33 *)
