From Coq Require Import String RelationClasses Morphisms.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts HeterogeneousRelations.
Import ITreeNotations.

Variant void : Type :=.
Variant voidE : Type -> Type :=.

Notation "'pred' A" := (A -> Prop)     (at level 10).
Notation "'rel' A"  := (A -> A -> Prop) (at level 10).
Notation "'relH' A B"  := (A -> B -> Prop) (at level 10).

(** Utilities to reason equationally *)
Ltac cut := apply eutt_eq_bind; intros ?.
Ltac ecut := eapply eutt_clo_bind.
Tactic Notation "cut" "with" uconstr(x) := apply eutt_clo_bind with (UU := x).
Ltac break :=
  repeat match goal with
    | b : bool |- _ => destruct b
    | x : unit |- _ => destruct x
    | p : _ * _ |- _ => destruct p
    | p : _ + _ |- _ => destruct p
    end.
Ltac ret := apply eutt_Ret.
Ltac break_match := match goal with |- context[match ?x with | _ => _ end] => destruct x eqn:?EQ end.

#[global] Hint Rewrite @interp_state_bind @interp_state_trigger @interp_state_ret @bind_ret_l @bind_bind : opt.
Ltac norm := autorewrite with opt.

(* Imperative loops are particular pattens of recursion: they do not carry any notion of accumulator.
	 We can capture this pattern with a [repeat] combinator.
*)
Definition repeat {E} (step : itree E (unit + unit)) : itree E unit :=
	ITree.iter (fun _ => step) tt.

(** Necessary generic material about [repeat] *)
#[global] Instance eutt_repeat {E : Type -> Type} :
  Proper (eutt eq ==> eutt eq) (@repeat E).
Proof.
  intros ? ? EQ.
  unfold repeat.
  apply eutt_iter.
  now intros ?.
Qed.

Lemma unfold_repeat :
  forall {E : Type -> Type} (step : itree E (unit + unit)),
    repeat step ≅
      flag <- step;; match flag with
                    | inl _ => Tau (repeat step)
                    | inr _ => Ret tt
                    end.
Proof.
  unfold repeat; intros.
  rewrite unfold_iter.
  eapply eq_itree_clo_bind.
  reflexivity.
  now intros; subst; break.
Qed.

(* TODO: define a generic [repeat] for iterative monads *)
Definition repeat_state {E S} :
  Monads.stateT S (itree E) (unit + unit) ->
  Monads.stateT S (itree E) unit :=
  fun step => Basics.iter (fun _ => step) tt.

Lemma unfold_repeat_state :
  forall {E : Type -> Type} {S} (step : Monads.stateT S (itree E) (unit + unit)) σ,
    repeat_state step σ ≅
      flag <- step σ;; match flag with
                    | (σ, inl _) => Tau (repeat_state step σ)
                    | (σ, inr _) => Ret (σ, tt)
                    end.
Proof.
  unfold repeat_state, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; intros.
  rewrite unfold_iter. cbn.
  rewrite !bind_bind.
  eapply eq_itree_clo_bind.
  reflexivity.
  intros ? ? <-.
  rewrite bind_ret_l.
  now break; cbn.
Qed.

#[global] Instance eq_itree_repeat_state {E : Type -> Type} {S} :
  Proper (pointwise_relation _ (eq_itree eq) ==> pointwise_relation _ (eq_itree eq)) (@repeat_state E S).
Proof.
  intros ? ? EQ σ.
  apply eq_itree_iter.
  intros [? []] [? []] eq; inv eq; cbn.
  rewrite EQ.
  eapply eq_itree_clo_bind.
  reflexivity.
  now intros [? ?] ? <-; cbn.
Qed.

#[global] Instance eutt_repeat_state {E : Type -> Type} {S} :
  Proper (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq)) (@repeat_state E S).
Proof.
  intros ? ? EQ σ.
  apply eutt_iter.
  intros [? []]; cbn.
  eapply eutt_clo_bind.
  apply EQ.
  now intros; subst; break.
Qed.

Definition eutt_repeat_state_gen {E : Type -> Type} {S: Type} (RS : rel S):
  Proper ((RS ==> (eutt (prod_rel RS eq))) ==> (RS ==> (eutt (prod_rel RS eq)))) (@repeat_state E S).
Proof.
  intros ? ? ? ? ? ?.
  apply (@eutt_iter_gen _ _ _ (prod_rel RS eq)).
  2:constructor; cbn; auto.
  intros [] [] []; cbn in *.
  ecut.
  now apply H.
  intros [] [] []; cbn in *; subst.
  ret.
  destruct s4; auto.
Qed.

Variant prod_sum_rel {S} (R1 R2 : rel S) : rel (S * (unit + unit)) :=
| prod_sum_rel_left  σ σ' : R1 σ σ' -> prod_sum_rel R1 R2 (σ, inl tt) (σ', inl tt)
| prod_sum_rel_right σ σ' : R2 σ σ' -> prod_sum_rel R1 R2 (σ, inr tt) (σ', inr tt).

Lemma eutt_repeat_state' {E S}
      (RI : S -> S -> Prop)
      (RR : S -> S -> Prop)
      body1
      body2
      (eutt_body : forall s1 s2, RI s1 s2 -> eutt (prod_sum_rel RI RR) (body1 s1) (body2 s2))
  : forall s1 s2 (RI_i : RI s1 s2),
    eutt (prod_rel RR eq) (@repeat_state E S body1 s1) (repeat_state body2 s2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body s1 s2 RI_i).
  do 2 rewrite unfold_repeat_state.
  ebind; econstructor; eauto with paco.
  intros [] [] ?.
  inv H.
  - etau.
  - eauto with paco.
Qed.

(* Annoyingly enough, we cannot leverage [eutt_iter_gen] to derive this schema: we return a prod of a sum, and not a sum *)
Definition eutt_repeat_state_gen' {E : Type -> Type} {S: Type} (RI RS : rel S):
  Proper ((RI ==> (eutt (prod_sum_rel RI RS))) ==> (RI ==> (eutt (prod_rel RS eq)))) (@repeat_state E S).
Proof.
  intros ? ? ? ? ? ?.
  eapply eutt_repeat_state'; eauto.
Qed.

Lemma interp_state_repeat {E F S} (t : itree E _)
  (h : forall T : Type, E T -> Monads.stateT S (itree F) T) σ
  :
  interp_state h (repeat t) σ ≅
    repeat_state (interp_state h t) σ.
Proof.
  unfold repeat.
  rewrite (interp_state_iter' _ h (fun _ : unit => t) tt σ).
  reflexivity.
Qed.

(* Ok the next section is a completely irrelevant tangent,
   but expressing the purity of expressions made me wonder:
   if I work with [void1], I should be able to prove that
   [t ;; t ≈ t] without knowing whether [t] diverges or not.
   But how do I prove it? Here's the simplest I found.
 *)
From ITree Require Import Props.HasPost.
Import HasPostNotations.

Section Tangent.

  Inductive subtree {E X} (t : itree E X) : itree E X -> Prop :=
  | sub_refl  v : v ≅ t -> subtree t v
  | sub_tau u v : v ≅ Tau u -> subtree t u -> subtree t v
  | sub_vis Y (e : E Y) y k v : v ≅ Vis e k -> subtree t (k y) -> subtree t v.
  Infix "⊑" := subtree (at level 70).

  #[global] Instance eq_itree_subtree {E X} : Proper (eq_itree eq ==> eq_itree eq ==> iff) (@subtree E X).
  Proof.
    intros t t' eqt u u' equ.
    split; intros sub.
    - revert u' equ. induction sub; intros.
      + apply sub_refl.
        rewrite <- equ, H, eqt.
        reflexivity.
      + eapply sub_tau.
        2:apply IHsub; reflexivity.
        rewrite <- equ, H; reflexivity.
      + eapply sub_vis.
        2:apply IHsub; reflexivity.
        rewrite <- equ, H; reflexivity.
    - revert u equ. induction sub; intros.
      + apply sub_refl.
        rewrite equ, H, eqt.
        reflexivity.
      + eapply sub_tau.
        2:apply IHsub; reflexivity.
        rewrite equ, H; reflexivity.
      + eapply sub_vis.
        2:apply IHsub; reflexivity.
        rewrite equ, H; reflexivity.
  Qed.

  #[global] Instance equiv_subtree {E X} : PreOrder (@subtree E X).
  Proof.
    split.
    - intros t; apply sub_refl; reflexivity.
    - intros t u v sub1 sub2; revert t sub1.
      induction sub2; intros t sub1.
      + rewrite H; auto.
      + rewrite H.
        eapply sub_tau.
        2: apply IHsub2; auto.
        reflexivity.
      + rewrite H.
        eapply sub_vis.
        2: apply IHsub2; auto.
        reflexivity.
  Qed.

  Lemma tau_subtree {E X} : forall (t u : itree E X),
      Tau t ⊑ u ->
      t ⊑ u.
  Proof.
    intros.
    induction H.
    - rewrite H; eapply sub_tau; [reflexivity | apply sub_refl; reflexivity].
    - rewrite H. eapply sub_tau; [reflexivity | eassumption].
    - rewrite H. eapply sub_vis; [reflexivity | eassumption].
  Qed.

  Lemma pure_div_or_ret_aux : forall {X} (t u : itree void1 X),
      t ⊑ u ->
      t ⤳ fun x => u ≈ Ret x.
  Proof.
    intros X t u; revert t.
    einit.
    ecofix CIH.
    intros * sub.
    rewrite (itree_eta t) in sub |- *.
    desobs t EQu.
    - estep.
      clear - sub.
      induction sub.
      + rewrite H; reflexivity.
      + rewrite H, IHsub, tau_eutt; reflexivity.
      + destruct e.
    - estep.
      ebase.
      right. apply CIHL.
      now apply tau_subtree.
    - destruct e.
  Qed.

  Lemma pure_div_or_ret : forall {X} (t : itree void1 X),
      t ⤳ fun x => t ≈ Ret x.
  Proof.
    intros X t.
    apply pure_div_or_ret_aux.
    reflexivity.
  Qed.

  Lemma twice_twice_almost_pure : forall {X} (t : itree void1 X),
      t ;; t ≈ t.
  Proof.
    intros.
    rewrite <- (bind_ret_r t) at 2.
    eapply eutt_post_bind.
    apply pure_div_or_ret.
    apply pure_div_or_ret.
    reflexivity.
    intros ?? <- H _; auto.
  Qed.

End Tangent.

(* 2024-06-07 10:32 *)
