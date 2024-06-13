From Paco Require Import paco.
From Coq Require Import Nat String RelationClasses Morphisms Psatz FunctionalExtensionality.
From RIP Require Import Maps Imp Utils ImpDenotation ImpEquiv Hoare.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts HeterogeneousRelations.
Import ITreeNotations.

Notation "t1 ≈[ R ] t2" := (eutt R t1 t2) (at level 20).

#[local]
Hint Rewrite aexp_pure_aeval bexp_pure_beval : opt.

(* ================================================================= *)
(** ** Example: Variable Renaming *)

Definition swapped (X Y : string) (σ1 σ2 : mem) : Prop :=
  (forall Z, Z <> X /\ Z <> Y -> σ1 Z = σ2 Z)
  /\ (σ1 X = σ2 Y)
  /\ (σ1 Y = σ2 X).

Example com1 := <{ X := X + Y; Z := X - Y }>.
Example com2 := <{ Y := Y + X; Z := Y - X }>.

Lemma swapped_correct :
  forall σ1 σ2,
    swapped X Y σ1 σ2 ->
    (ℑ ⟦com1⟧ σ1)
      ≈[ (prod_rel (swapped X Y) eq) ]
    (ℑ ⟦com2⟧ σ2).
Proof.
  intros.
  unfold com1, com2.
  cbn.
  norm.
  apply eutt_Ret.
  apply prod_morphism; cbn; auto.
  unfold swapped.
  destruct H as (H1 & H2 & H3).
  unfold t_update.
  split.
  - intros Z [HX HY].
    destruct (Imp.Z =? Z)%string.
    rewrite H2. rewrite <- H3. reflexivity.
    destruct (eqb_spec X Z).
    subst. contradiction.
    destruct (eqb_spec Y Z).
    subst. contradiction.
    apply H1. tauto.
  - destruct (eqb_spec Z X). inversion e.
    destruct (eqb_spec Z Y). inversion e.
    destruct (eqb_spec X X).
    destruct (eqb_spec Y Y).
    destruct (eqb_spec X Y).
    destruct (eqb_spec Y X).
    rewrite H2; rewrite <- H3; auto.
    inversion e1.
    destruct (eqb_spec Y X).
    inversion e1.
    rewrite H2; rewrite <- H3; auto.
    contradiction.
    contradiction.
Qed.


(* ================================================================= *)
(** ** Substitution *)

(**
  Substitutes an arbitary arithemetic expression for the variable [x] in
*)
Fixpoint substitute_aexp (x:string) (ax:aexp) (a:aexp) : aexp :=
  match a with
  | ANum n => a
  | AId y => if String.eqb y x then ax else a
  | <{ a1 + a2 }> =>
      <{ (substitute_aexp x ax a1) + (substitute_aexp x ax a2) }>

  | <{ a1 - a2 }> =>
      <{ (substitute_aexp x ax a1) - (substitute_aexp x ax a2) }>

  | <{ a1 * a2 }> =>
      <{ (substitute_aexp x ax a1) * (substitute_aexp x ax a2) }>
  end.

Eval compute in (substitute_aexp X (<{ Y + 2}>) (<{ X + Z }>)).
(** ==> [<{ Y + 2 + Z }>] *)

(* TODO: Move this to ImpEquiv *)
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

(* ----------------------------------------------------------------- *)
(** *** Correctness lemma *)

Lemma substitute_aexp_semantic : forall (x:string) ax a,
  forall σ (EQ: ℑ ⟦ <{ x }> ⟧a σ ≈ ℑ ⟦ ax ⟧a σ),
    ℑ ⟦ a ⟧a σ
      ≈
    ℑ ⟦ substitute_aexp x ax a ⟧a σ.
Proof.
  intros x ax a σ HEQ.
  apply aexp_eval_semantics2.
  intros. apply substitute_aexp_aeval.
  apply aexp_eval_semantics2.
  assumption.
Qed.

(* TODO: Move to ImpEquiv.v *)
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

(* ----------------------------------------------------------------- *)
(** *** Substitution in a command *)

(** Because commands are not pure, we can't blindly substitute. *)

Fixpoint substitute_com (x:string) (ax:aexp) (c:com) : (com * bool) :=
  match c with
  | <{ skip }> => (c, false)
  | <{ y := a }> =>
      let a' := substitute_aexp x ax a in
      (<{ y := a' }>, ((y =? x)%string || contains y ax)%bool)
  | <{ c1 ; c2 }> =>
      let '(c1', stop1) := substitute_com x ax c1 in
      if stop1
      then (<{ c1' ; c2 }>, stop1)
      else
        let '(c2', stop2) := substitute_com x ax c2 in
        (<{ c1' ; c2' }>, stop2)
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

(* ----------------------------------------------------------------- *)
(** *** Correctness of substition *)

(** Define an invariant that says when we can safely substitute the
expression  <{ ax }> for <{ x }> in a state σ.  *)

Definition subst_invariant x ax σ :=
  aeval σ <{ x }> = aeval σ ax.

(** Define the relational post condition for reasoning about the
results of substitution, relative to the initial state [σ]. *)

Definition post_condition x ax b (σ0:state) :=
  fun σ1 σ2 =>
    σ1 = σ2
    /\ (* If the substitution claims [x] and [ax] were _not_ modified... *)
      (b = false ->
       (σ1 x = σ0 x (* ...then [x] wasn't modified *)
        /\ (* ... and neither was [ax]  *)
          aeval σ0 ax = aeval σ1 ax
          (* ... and the invariant preserved *)
        /\ subst_invariant x ax σ1)).

(* ----------------------------------------------------------------- *)
(** *** Some properties of the predicates *)
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

(* ----------------------------------------------------------------- *)
(** *** A relational specification *)
Lemma substitute_com_correct :
  forall x ax c c' b
    (HS: substitute_com x ax c = (c', b)),
  forall σ (P: subst_invariant x ax σ),
      (ℑ ⟦c⟧ σ)
        ≈[ (prod_rel (post_condition x ax b σ) eq)]
      (ℑ ⟦c'⟧ σ).
(* TODO: Clean up this proof! *)
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

(** *)
Lemma substitute_com_subst : forall c x a σ,
    contains x a = false ->
    ℑ ⟦ c ⟧ (x !-> aeval σ a; σ)
      ≈
    ℑ ⟦ fst (substitute_com x a c) ⟧ (x !-> aeval σ a; σ).
Proof.
  intros.
  destruct (substitute_com x a c) eqn:HS.
  simpl.
  apply substitute_com_correct with (σ := (x !-> aeval σ a; σ)) in HS.
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

Fixpoint com_append (c1 c2 : com) : com :=
  match c1 with
  | <{ skip }> => c2
  | <{ c11 ; c12}> => <{ c11 ; (com_append c12 c2) }>
  | _ => <{ c1 ; c2 }>
  end.

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

(* ----------------------------------------------------------------- *)
(** *** Constant propagation as a function on syntax *)

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

(* ----------------------------------------------------------------- *)
(** *** An Exmple *)

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
(** ==>

<{ X := 9; Y := 9; Y := 9; Y := 0; while Y = 0 do X := X + 1 end }>.
Proof.
*)

Example correct: example ≊ (fold_constants_com (propagate_com example)).
Proof.
  rewrite fold_constants_com_sound.
  apply propagate_com_sound.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Loop unrolling *)

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

(* ----------------------------------------------------------------- *)
(** *** Run several passes of an optimization function *)

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

(* ----------------------------------------------------------------- *)
(** *** An Imp optimization pass *)

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

(* ----------------------------------------------------------------- *)
(** *** Back to our factorial example

    Imp code for [factorial] for a specific number: *)
Definition fact_n n := <{ X := n ; fact_in_coq }>.

Definition fact_opt n :=
  optimize (n+1) (fact_n n).

Definition fact_opt5 := fact_opt 5.

Lemma fact_opt_correct : forall (n:nat),
    <{ X := n ; fact_in_coq }> ≊ fact_opt n.
Proof.
  intros n.
  unfold fact_in_coq.
  apply optimize_sound.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Dead store elimination *)

(** We'll skip the full story, but see how we can justify: *)

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

(* 2024-06-13 11:26 *)
