From Paco Require Import paco.
From Coq Require Import Nat String RelationClasses Morphisms Psatz.
From RIP Require Import Imp Utils Maps ImpDenotation.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts HeterogeneousRelations.
Import ITreeNotations.

(* ================================================================= *)
(** ** Equivalence of Imp programs *)

(** Each piece of syntax can be given a meaning in two steps:

         syntax
           ->            (representation)
       itree MemE
           ->            (interpretation)
   stateT mem (itree ∅)
*)
(**
    This schema gives naturally rise to three notions of program equality, all defining
    relations on the syntax of programs.
    1. Syntactic equality, the program have equal syntax. One can consider relaxed
    notions, such as equality up-to alpha-renaming.
    2. Representation equality, the program have equivalent representations. Here the
    notion of equivalence is dictated by the monadic structure representations live in:
    they are itrees, we hence work w.r.t. [eutt]
    3. Semantic equality, the program have equivalent models. Since our imp programs
    are modelled as computations in [StateT mem (itree ∅)], equivalence will be defined
    as point-wise eutt. For simplicity, we will assume functional extensionality when
    working with this equivalence --- we will discuss later how to avoid this problem.

    This distinction can be used to defined equivalences of arithmetic expressions, of
    boolean expressions, and of commands.
 *)
(* ----------------------------------------------------------------- *)
(** *** Definitions and elementary properties *)

Definition aexp_equiv : rel aexp :=
  fun a1 a2 => forall σ, ℑ ⟦ a1 ⟧a σ ≈ ℑ ⟦ a2 ⟧a σ.
Definition bexp_equiv : rel bexp :=
  fun b1 b2 => forall σ, ℑ ⟦ b1 ⟧b σ ≈ ℑ ⟦ b2 ⟧b σ.
Definition com_eq : rel com :=
  fun c1 c2 => ⟦ c1 ⟧ ≈ ⟦ c2 ⟧.
Definition com_equiv : rel com :=
  fun c1 c2 => forall σ, ℑ ⟦ c1 ⟧ σ ≈ ℑ ⟦ c2 ⟧ σ.

Infix "≈ₐ" := aexp_equiv (at level 20).
Infix "≈ᵦ" := bexp_equiv (at level 20).
Infix "≡" := com_eq (at level 20).
Infix "≊" := com_equiv (at level 20).

(* ================================================================= *)
(** ** Elementary properties of program equivalences

    We establish the following central properties:
  - All equivalences of syntax considered are _equivalence relations_

  - Representation equality is strictly tighter than semantic equality

  - All equivalences are congruences: they are compatible with every construction of the language
 *)

Section Congruence.

  (** The relations are equivalence relations *)
  #[global] Instance com_eq_equiv : Equivalence com_eq.
  Proof.
    unfold com_eq; constructor.
    now intros ?.
    now intros ? ?.
    intros ? ? ? ? ?; etransitivity; eauto.
  Qed.

  #[global] Instance com_equiv_equiv : Equivalence com_equiv.
  Proof.
    unfold com_equiv; constructor.
    now intros ?.
    now intros ? ?.
    intros ? ? ? ? ?; etransitivity; eauto.
  Qed.

  #[global] Instance aexp_equiv_equiv : Equivalence aexp_equiv.
  Proof.
    unfold aexp_equiv; constructor.
    now intros ?.
    now intros ? ?.
    intros ? ? ? ? ?; etransitivity; eauto.
  Qed.

  #[global] Instance bexp_equiv_equiv : Equivalence bexp_equiv.
  Proof.
    unfold bexp_equiv; constructor.
    now intros ?.
    now intros ? ?.
    intros ? ? ? ? ?; etransitivity; eauto.
  Qed.

  (** ≡ is included in ≈ *)
  #[global] Instance com_eq_subrel_equiv : subrelation com_eq com_equiv.
  Proof.
    intros c1 c2 EQ σ.
    cbn.
    now apply eutt_interp_state_eq.
  Qed.

  (** The relations are congruences:  they respect all constructions of the language *)
  #[global] Instance aexp_equiv_plus : Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) (APlus).
  Proof.
    unfold aexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance aexp_equiv_minus : Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) (AMinus).
  Proof.
    unfold aexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance aexp_equiv_mult : Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) (AMult).
  Proof.
    unfold aexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance bexp_equiv_beq : Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BEq.
  Proof.
    unfold aexp_equiv, bexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance bexp_equiv_bneq : Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BNeq.
  Proof.
    unfold aexp_equiv, bexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance bexp_equiv_ble : Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BLe.
  Proof.
    unfold aexp_equiv, bexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance bexp_equiv_bgt : Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BGt.
  Proof.
    unfold aexp_equiv, bexp_equiv.
    intros a1 a1' eq1 a2 a2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance bexp_equiv_bnot : Proper (bexp_equiv ==> bexp_equiv) BNot.
  Proof.
    unfold bexp_equiv.
    intros b b' eq σ.
    cbn.
    norm.
    rewrite eq.
    now norm.
  Qed.

  #[global] Instance bexp_equiv_band : Proper (bexp_equiv ==> bexp_equiv ==> bexp_equiv) BAnd.
  Proof.
    unfold bexp_equiv.
    intros b1 b1' eq1 b2 b2' eq2 σ.
    cbn.
    norm.
    rewrite eq1.
    cut; norm.
    rewrite eq2.
    now cut.
  Qed.

  #[global] Instance com_equiv_asgn x : Proper (aexp_equiv ==> com_equiv) (CAsgn x).
  Proof.
    unfold aexp_equiv, com_equiv.
    intros e e' EQ σ.
    cbn.
    norm.
    rewrite (EQ σ).
    now cut.
  Qed.

  #[global] Instance com_eq_seq : Proper (com_eq ==> com_eq ==> com_eq) CSeq.
  Proof.
    unfold com_eq.
    intros c1 c1' EQ1 c2 c2' EQ2.
    cbn.
    rewrite EQ1.
    now cut.
  Qed.

  #[global] Instance com_equiv_seq : Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
  Proof.
    unfold com_equiv.
    intros c1 c1' EQ1 c2 c2' EQ2 σ.
    cbn.
    norm.
    rewrite (EQ1 σ).
    cut.
    cbn; apply EQ2.
  Qed.

  #[global] Instance com_eq_if b : Proper (com_eq ==> com_eq ==> com_eq) (CIf b).
  Proof.
    unfold com_eq.
    intros c1 c1' EQ1 c2 c2' EQ2.
    cut.
    now break.
  Qed.

  #[global] Instance com_equiv_if : Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
  Proof.
    unfold bexp_equiv, com_equiv.
    intros b b' EQb c1 c1' EQ1 c2 c2' EQ2 σ.
    cbn.
    norm.
    rewrite EQb.
    cut.
    break; cbn.
    apply EQ1.
    apply EQ2.
  Qed.

  #[global] Instance com_eq_while b : Proper (com_eq ==> com_eq) (CWhile b).
  Proof.
    unfold com_eq.
    intros c c' EQ.
    cbn.
    apply eutt_repeat.
    cut; break; [| reflexivity].
    rewrite EQ; reflexivity.
  Qed.

  #[global] Instance com_equiv_while : Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
  Proof.
    unfold bexp_equiv, com_equiv.
    intros b b' EQb c c' EQ σ.
    cbn.
    rewrite !interp_state_repeat.
    apply eutt_repeat_state.
    intros σ'.
    norm.
    rewrite EQb.
    cut; break; cbn; [| reflexivity].
    norm.
    rewrite (EQ m).
    reflexivity.
  Qed.

End Congruence.

(* ================================================================= *)
(** ** Syntactic contexts

    One way to cleanly capture the congruence property is to define
    the syntactic contexts for our language: these are ASTs with holes
    The [plug] function takes a context and plugs a program in its hole,
    resulting in a full program.
    Congruence exactly states that if we swap two equivalent programs in
    the hole of a context, we get two equivalent programs.
 *)
Inductive com_ctx : Set :=
| EmptyC : com_ctx
| SeqLC  : com_ctx -> com -> com_ctx
| SeqRC  : com -> com_ctx -> com_ctx
| IfLC   : bexp -> com_ctx -> com -> com_ctx
| IfRC   : bexp -> com -> com_ctx -> com_ctx
| WhileC : bexp -> com_ctx -> com_ctx.

(** Inserts a piece of syntax in a context *)
Definition plug (c : com) : com_ctx -> com :=
  fix plug C :=
    match C with
    | EmptyC     => c
    | SeqLC C c2 => <{ plug C ; c2 }>
    | SeqRC c1 C => <{ c1 ; plug C }>
    | IfLC b C c2 => <{ if b then plug C else c2 end }>
    | IfRC b c1 C => <{ if b then c1 else plug C end }>
    | WhileC b C => <{ while b do plug C end }>
    end.

(** Being a congruence exactly means that the relation respects [plug]
 *)
Theorem com_eq_plug : forall c1 c2 C,
    c1 ≡ c2 ->
    plug c1 C ≡ plug c2 C.
Proof.
  intros * EQ; induction C; cbn; first [easy | now rewrite IHC].
Qed.
#[global] Instance com_eq_plug' : Proper (com_eq ==> eq ==> com_eq) plug.
Proof.
  repeat intro; subst; now apply com_eq_plug.
Qed.

Theorem com_equiv_plug : forall (c1 c2 : com) C,
    c1 ≊ c2 ->
    plug c1 C ≊ plug c2 C.
Proof.
  intros * EQ; induction C; cbn; first [easy | now rewrite IHC].
Qed.
#[global] Instance com_equiv_plug' : Proper (com_equiv ==> eq ==> com_equiv) plug.
Proof.
  repeat intro; subst; now apply com_equiv_plug.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Semantically characterizing the MemE events *)

(** We start with two lemmas characterizing the semantics of
    the memory effects after interpretation, and add them to
    our normalization procedure.
 *)
Lemma interp_state_rd : forall x σ, ℑ (rd x) σ ≈ Ret (σ, σ x).
Proof.
  unfold rd; intros; now norm.
Qed.

Lemma interp_state_wr : forall x v σ, ℑ (wr x v) σ ≈ Ret (x !-> v ; σ, tt).
Proof.
  unfold wr; intros; now norm.
Qed.

#[global] Hint Rewrite @interp_state_rd @interp_state_wr : opt.

(* ================================================================= *)
(** ** Semantically Characterizing Evaluation  *)

(** Optimizations are complex, global, functions crawling complete ASTs.
    In order to help us tackle such constructions, we start by building
    tools for ourselves: we collect sets of rewriting rules over
    small, open, pieces of syntax, that we prove to always be equivalent.

    Because equivalences are congruences, we will be able to lift for free
    these results and use these elementary rewrite rules in complete programs.

    As a first step, we establish that evaluation of arithmetic expressions
    is _pure_:
 *)
Lemma aexp_pure_aeval : forall a σ,
    interp_state handle_Mem ⟦ a ⟧a σ ≈ Ret (σ, aeval σ a).
Proof.
  intros.
  induction a; cbn.
  - now norm.
  - now norm.
  - norm; rewrite IHa1.
    norm; rewrite IHa2.
    now norm.
  - norm; rewrite IHa1.
    norm; rewrite IHa2.
    now norm.
  - norm; rewrite IHa1.
    norm; rewrite IHa2.
    now norm.
Qed.

Lemma aexp_pure : forall a σ,
    exists v, interp_state handle_Mem ⟦ a ⟧a σ ≈ Ret (σ,v).
Proof.
  intros.
  exists (aeval σ a). apply aexp_pure_aeval.
Qed.

Lemma bexp_pure_beval : forall b σ,
    interp_state handle_Mem ⟦ b ⟧b σ ≈ Ret (σ, beval σ b).
Proof.
  intros.
  induction b; cbn.
  - now norm.
  - now norm.
  - norm.
    rewrite (aexp_pure_aeval a1 σ).
    norm.
    rewrite (aexp_pure_aeval a2 σ).
    now norm.
  - norm.
    rewrite (aexp_pure_aeval a1 σ).
    norm. rewrite (aexp_pure_aeval a2 σ).
    now norm.
  - norm.
    rewrite (aexp_pure_aeval a1 σ).
    norm. rewrite (aexp_pure_aeval a2 σ).
    now norm.
  - norm.
    rewrite (aexp_pure_aeval a1 σ).
    norm. rewrite (aexp_pure_aeval a2 σ).
    now norm.
  - norm. rewrite IHb.
    now norm.
  - norm.
    rewrite IHb1.
    norm.
    rewrite IHb2.
    now norm.
Qed.

Lemma bexp_pure : forall b σ,
    exists v, interp_state handle_Mem ⟦ b ⟧b σ ≈ Ret (σ,v).
Proof.
  intros.
  exists (beval σ b). apply bexp_pure_beval.
Qed.

(* ================================================================= *)
(** ** Universally valid static rewrite rules: an inventory *)

(**
    A first series of basic blocks for building verified optimizations are
    rewrite rules that can be applied in all contexts. We accumulate them into
    sets of reduction rules to construct a sort of static calculus.
    Not all interesting program transformations fall into this category of course:
    optimizations often gather specific information on the context before deciding
    whether they can perform an optimization. We will consider this question in
    subsequent chapters and focus for now on rewrite rules that are valid in all
    contexts.

    In the case of commands, we inventory these rules into two groups:
    - those that are validated by ≡
    - and those that are validated only by ≈
 *)

(* ----------------------------------------------------------------- *)
(** *** Rules for arithmetic expressions *)
Variant red_aexp : rel aexp :=
  | rplus (n m : val)  : red_aexp <{ n + m }> <{ aop_sem op_plus n m }>
  | rminus (n m : val) : red_aexp <{ n - m }> <{ aop_sem op_minus n m }>
  | rmult (n m : val)  : red_aexp <{ n * m }> <{ aop_sem op_mult n m }>
  | minus_inv e        : red_aexp <{ e - e }> <{ 0 }>
  | mult_zero e        : red_aexp <{ 0 * e }> <{ 0 }>
  | mult_one  e        : red_aexp <{ 1 * e }> <{ e }>
  | plus_zero a        : red_aexp <{ 0 + a }> <{ a }>
  | plus_comm a1 a2    : red_aexp <{ a1 + a2 }> <{ a2 + a1 }>
  | mult_comm a1 a2    : red_aexp <{ a1 * a2 }> <{ a2 * a1 }>
.

(* ----------------------------------------------------------------- *)
(** *** Rules on boolean expressions *)
Variant red_bexp : rel bexp :=
  | req (n m : nat) :
    red_bexp <{  n = m }> (if Nat.eqb n m then <{true}> else <{false}>)

  | rneq (n m : nat) :
    red_bexp <{ n <> m }> (if Nat.eqb n m then <{false}> else <{true}>)

  | rle (n m : nat) :
    red_bexp <{ n <= m }> (if Nat.leb n m then <{true}> else <{false}>)

  | rgt (n m : nat)  :
    red_bexp <{ n > m }> (if Nat.leb n m then <{false}> else <{true}>)

  | rnegt    : red_bexp <{ ~ true }> <{false}>
  | rnegf    : red_bexp <{ ~ false }> <{true}>
  | randtt   : red_bexp <{ true && true }> <{ true}>
  | randft   : red_bexp <{ false && true }> <{ false }>
  | randff   : red_bexp <{ false && false }> <{ false }>
  | and_comm b b' : red_bexp <{ b && b' }> <{ b' && b }>
.

(* ----------------------------------------------------------------- *)
(** *** Rules on commands (1) *)

(** These are straight-up validated by ≡ (strong equivalence) *)

Variant red_com1   : rel com :=
| skipL c          : red_com1 <{ skip ; c }> <{c}>
| skipR c          : red_com1 <{ c ; skip }> <{c}>
| iftrue c1 c2     : red_com1 <{ if true then c1 else c2 end }> c1
| iffalse c1 c2    : red_com1 <{ if false then c1 else c2 end }> c2
| whilefalse c     : red_com1 <{ while false do c end }> <{ skip }>
| seqA c1 c2 c3    : red_com1 <{ (c1 ; c2) ; c3 }> <{ c1 ; (c2 ; c3) }>

| ifComm b c1 c2   : red_com1
                     <{ if b then c1 else c2 end }>
                     <{ if ~b then c2 else c1 end }>

| ifDist b c1 c2 c : red_com1
                     <{ if b then c1 else c2 end ; c }>
                     <{ if b then c1 ; c else c2 ; c end }>

| loop_unroll1 b c : red_com1
                     <{ while b do c end }>
                     <{ if b then c ; while b do c end else skip end }>.

(* ----------------------------------------------------------------- *)
(** *** Rules on commands (2) *)

(** Rules on commands that are validated only by ≊ (weak equivalence) *)
Variant red_com2 : com -> com -> Prop :=
| whiletrue c      : red_com2
                     <{ while true do c end }>
                     <{ while true do skip end }>

| loop_unroll2 b c : red_com2
                     <{ while b do c end }>
                     <{ while b do c ; if b then c else skip end end }>.

(* ================================================================= *)
(** ** Semantic validity of our calculus *)

(** We have written authoritatively a long list of transformations. To back up
    our confidence, we now associate to each of them a Lemma expressing their
    soundness: both sides of the rewrite rule must be equivalent.

    This section culminate with the result we seek: each of the four reduction rules of this
    calculus define subrelations of the equivalences of the respective syntactic components.
    Combined with the fact that these relations are equivalence relations and congruence,
    this means that each of these reduction rules can be used to rewrite while proving that
    two programs are equivalent.
 *)

Lemma minus_inv_sound : forall e,
    <{ e - e }> ≈ₐ 0.
Proof.
  intros e σ.
  cbn.
  norm.
  pose proof aexp_pure e σ as [v EQ]. (* Note that if [e] was impure (if it diverged for instance), then the equation would be invalid *)
  rewrite EQ; norm.
  rewrite EQ; norm.
  cbn.
  now rewrite PeanoNat.Nat.sub_diag.
Qed.

Lemma mult_zero_sound : forall e,
    <{ 0 * e }> ≈ₐ 0.
Proof.
  intros e σ.
  rewrite aexp_pure_aeval.
  cbn.
  norm.
  reflexivity.
Qed.

Lemma mult_one_sound : forall e,
    <{ 1 * e }> ≈ₐ <{ e }>.
Proof.
  intros e σ.
  do 2 rewrite aexp_pure_aeval.
  cbn.
  rewrite PeanoNat.Nat.add_0_r.
  reflexivity.
Qed.

Lemma add_zero_sound : forall a,
    <{ 0 + a }> ≈ₐ <{ a }>.
Proof.
  intros a σ.
  do 2 rewrite aexp_pure_aeval.
  cbn.
  reflexivity.
Qed.

Lemma rplus_sound : forall (n m : val),
    <{ APlus n m }> ≈ₐ <{ aop_sem op_plus n m }>.
Proof.
  intros * σ.
  cbn.
  now norm.
Qed.

Lemma rminus_sound : forall (n m : val),
    <{ AMinus n m }> ≈ₐ <{ aop_sem op_minus n m }>.
Proof.
  intros * σ.
  cbn.
  now norm.
Qed.

Lemma rmult_sound : forall (n m : val),
    <{ AMult n m }> ≈ₐ <{ aop_sem op_mult n m }>.
Proof.
  intros * σ.
  cbn.
  now norm.
Qed.

Lemma plus_comm_sound : forall a1 a2,
    <{ a1 + a2 }> ≈ₐ <{ a2 + a1 }>.
Proof.
  intros * σ.
  cbn.
  norm.
  pose proof aexp_pure a1 σ as [v1 EQ1].
  pose proof aexp_pure a2 σ as [v2 EQ2].
  rewrite EQ1, EQ2; cbn; norm.
  rewrite EQ1, EQ2; cbn; norm.
  cbn; ret; f_equal; lia.
Qed.

Lemma mult_comm_sound : forall a1 a2,
    <{ a1 * a2 }> ≈ₐ <{ a2 * a1 }>.
Proof.
  intros * σ.
  cbn.
  norm.
  pose proof aexp_pure a1 σ as [v1 EQ1].
  pose proof aexp_pure a2 σ as [v2 EQ2].
  rewrite EQ1, EQ2; cbn; norm.
  rewrite EQ1, EQ2; cbn; norm.
  cbn; ret; f_equal; lia.
Qed.

#[local] Hint Resolve mult_zero_sound mult_one_sound add_zero_sound rplus_sound rminus_sound rmult_sound minus_inv_sound plus_comm_sound mult_comm_sound : opt.

(** Validity of [opt_red_bexp] *)
Lemma req_sound : forall (n m : val),
    <{ BEq (ANum n) (ANum m) }> ≈ᵦ if Nat.eqb n m then <{true}> else <{false}>.
Proof.
  intros * σ.
  cbn; norm.
  case PeanoNat.Nat.eqb_spec.
  - intros; cbn; now norm.
  - intros; cbn; now norm.
Qed.

Lemma rneq_sound : forall (n m : val),
    <{ BNeq (ANum n) (ANum m) }> ≈ᵦ if Nat.eqb n m then <{false}> else <{true}>.
Proof.
  intros * σ.
  cbn; norm.
  case PeanoNat.Nat.eqb_spec.
  - intros; cbn; now norm.
  - intros; cbn; now norm.
Qed.

Lemma rle_sound : forall (n m : val),
    <{ BLe (ANum n) (ANum m) }> ≈ᵦ if Nat.leb n m then <{true}> else <{false}>.
Proof.
  intros * σ.
  cbn; norm.
  case PeanoNat.Nat.leb_spec.
  - intros; cbn; now norm.
  - intros; cbn; now norm.
Qed.

Lemma rgt_sound : forall (n m : val),
    <{ BGt (ANum n) (ANum m) }> ≈ᵦ if Nat.leb n m then <{false}> else <{true}>.
Proof.
  intros * σ.
  cbn; norm.
  case PeanoNat.Nat.leb_spec.
  - intros; cbn; now norm.
  - intros; cbn; now norm.
Qed.

Lemma rnegt_sound :
    <{ ~ true }> ≈ᵦ <{ false }>.
Proof.
  intros σ; now cbn; norm.
Qed.

Lemma rnegf_sound :
    <{ ~ false }> ≈ᵦ <{ true }>.
Proof.
  intros σ; now cbn; norm.
Qed.

Lemma randtt_sound :
    <{ true && true }> ≈ᵦ <{ true }>.
Proof.
  intros * σ.
  cbn; now norm.
Qed.

Lemma randft_sound :
    <{ false && true }> ≈ᵦ <{ false }>.
Proof.
  intros * σ.
  cbn; now norm.
Qed.

Lemma randff_sound :
    <{ false && false }> ≈ᵦ <{ false }>.
Proof.
  intros * σ.
  cbn; now norm.
Qed.

Lemma and_comm_sound : forall (b b' : bexp),
    <{ b && b' }> ≈ᵦ <{ b' && b }>.
Proof.
  intros * σ.
  cbn; norm.
  pose proof bexp_pure b σ as [v1 eq1].
  pose proof bexp_pure b' σ as [v2 eq2].
  do 2 (rewrite eq1, eq2; norm).
  ret; cbn.
  now rewrite Bool.andb_comm.
Qed.

#[local] Hint Resolve and_comm_sound randft_sound randtt_sound randff_sound rnegt_sound rnegf_sound rle_sound rgt_sound req_sound rneq_sound: opt.

(* ----------------------------------------------------------------- *)
(** *** Proofs of equivalences of commands *)

(** And we can prove interesting semantic equivalenes of Imp programs.  *)

Lemma skipL_sound : forall c,
    <{ skip ; c }> ≡
    <{c}>.
Proof.
  intros; red; cbn; now norm.
Qed.

Lemma skipR_sound : forall c,
    <{ c ; skip }> ≡
    <{c}>.
Proof.
  intros; red; cbn.
  rewrite <- (bind_ret_r ⟦ c ⟧) at 2.
  cut; now break.
Qed.

Lemma iftrue_sound : forall c1 c2,
    <{ if true then c1 else c2 end }> ≡ c1.
Proof.
  intros; red; cbn; now norm.
Qed.

Lemma iffalse_sound : forall c1 c2,
    <{ if false then c1 else c2 end }> ≡ c2.
Proof.
  intros; red; cbn; now norm.
Qed.

Lemma whilefalse_sound : forall c,
    <{ while false do c end }> ≡ <{ skip }>.
Proof.
  intros ?.
  red; cbn; rewrite unfold_repeat.
  now norm.
Qed.

(* TODO :
  - Some notation formatting to better display equations. Notably
    t
    ≈
    u
    rather than t ≈ u
 *)
Lemma ifComm_sound : forall b c1 c2,
    <{ if b then c1 else c2 end }> ≡
    <{ if ~b then c2 else c1 end }>.
Proof.
  intros.
  red; cbn.
  cut with (fun b1 b2 => b1 = negb b2).
  - rewrite <- (bind_ret_r ⟦ b ⟧b) at 1.
    cut.
    ret.
    now rewrite Bool.negb_involutive.
  - now intros ? [] ->.
Qed.

Lemma ifDist_sound : forall b c1 c2 c,
    <{ if b then c1 else c2 end ; c }> ≡
    <{ if b then c1 ; c else c2 ; c end }>.
Proof.
  intros.
  red; cbn.
  norm.
  cut.
  now break.
Qed.

Lemma seqA_sound : forall c1 c2 c3,
    <{ (c1 ; c2) ; c3 }> ≡
    <{ c1 ; (c2 ; c3) }>.
Proof.
  intros.
  red; cbn; now norm.
Qed.

Lemma loop_unroll1_sound_strong : forall b c,
    <{ while b do c end }> ≡ <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros.
  red; cbn.
  rewrite unfold_repeat.
  norm.
  cut; break.
  - norm.
    cut.
    norm.
    now rewrite tau_eutt.
  - now norm.
Qed.

Lemma loop_unroll1_sound : forall b c,
    <{ while b do c end }> ≊ <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros.
  apply com_eq_subrel_equiv.
  apply loop_unroll1_sound_strong.
Qed.

#[global] Hint Resolve skipL_sound skipR_sound iftrue_sound iffalse_sound whilefalse_sound ifComm_sound ifDist_sound seqA_sound loop_unroll1_sound_strong loop_unroll1_sound : opt.

(* ----------------------------------------------------------------- *)
(** *** (Harder) Loop Equivalences

    [loop_unroll2_sound] turns out to be more interesting that it may seem.
First in terms of bisimulation:
   1. it cannot be proved equationally using the [Iterative] laws
   2. it does not fit the restricted bisimulation schema that [eutt_iter_gen] provides as it only covers lock-step bisimulation at the granularity of the bodies.
   Two solutions:
   - do a proof by coinduction locally (as done crudely below)
   - introduce an additional result about [iter] (or even better here, [repeat])
Second in terms of effects:
   3. it is true if and only if [bexp] are mostly pure: divergence is fine, but no other effect.
   Indeed, the right handside might evaluate a failing boolean expression an
   extra time compared to the left handside.
   This means that we can only prove the equation for [≈]. Furthermore, it turns
   out to be quite cumbersome to exploit the purity argument: I do it in the
   simpler case where boolean expressions are _really_ pure, i.e. also
   terminating. The tangent at the end of this file essentially proves why it
   also works with divergent computations, but I'm not sure I'd know how to
   incorporate this argument in the coinductive proof.
 *)

(** This equivalence is _not_ directly provable from the iter laws. *)
Lemma loop_unroll2_sound : forall b c,
    <{ while b do c end }> ≊
    <{ while b do (c ; if b then c else skip end) end }>.
Proof.
  intros. red.
  einit. ecofix CIH.
  intros σ.
  unfold model_com,compose; cbn.
  rewrite 2 interp_state_repeat.
  rewrite 2 unfold_repeat_state.

 (* The system can synch in three ways
     (1) [b] is immediately false, it exits on both side immediately
     (2) [b] is first true, then false, it exits on both side after one iteration
         However there is one tricky part to this: on the right hand-side, the
         failing [b] expression will be evaluated twice in a row, we need to
         remember that it was evaluating to false.
         Furthermore, since we evaluate b twice, it's only sound if b is pure,
         which it isn't at this level: we need to move this in opt_red2!
     (3) [b] is true at least twice, both system synch under a Tau, and conclude coinductively (the system on the left has dismissed a first tau earlier)
  *)
  norm.
  ebind; econstructor. reflexivity.
  intros tmp ? <-; destruct tmp as [? []]; cycle -1.
  - (* (1) *)
    cbn.
    now norm.
  - cbn. norm.
    ebind. econstructor. reflexivity.
    intros ? ? <-; break; cbn.
    norm.
    rewrite tau_euttge. (* The system on the left passes a lonely guard after one iteration, we dismiss it *)
    rewrite unfold_repeat_state.
    norm.
    (* There is something slightly interesting here:
       what is the best way to exploit the purity of [b]
       so that we can process its second evaluation in the
       right hand-side?
     *)
    pose proof bexp_pure b m0 as [vb eqb].
    ebind. unshelve econstructor.
    exact (fun '(m1,b1) '(m2,b2) => m1 = m2 /\ m1 = m0 /\ b1 = b2 /\ b1 = vb).
    rewrite eqb; ret; intuition.
    intros [? ?] [? ?] ?; intuition; subst.
    destruct vb; cbn; cycle -1.
    + (* (2) *)
      cbn; norm.
      rewrite tau_euttge.
      rewrite unfold_repeat_state.
      norm.
      pose proof (@bind_ret_l void1 _ _ (m0,false) (fun _ => Ret (m0,tt))) as EQ; cbn in EQ; rewrite <- EQ; clear EQ.
      ebind.
      unshelve econstructor.
      exact (fun '(m1,b1) '(m2,b2) => m1 = m2 /\ m1 = m0 /\ b1 = b2 /\ b1 = false).
      rewrite eqb; ret; intuition.
      intros [? ?] [? ?] ?; intuition; subst.
      now cbn; norm.
    + cbn; norm.
      ebind. econstructor. reflexivity.
      intros ? ? <-; break.
      cbn.
      norm.
      rewrite <- 2 interp_state_repeat.
      etau.
Qed.

(* Amusing, [whiletrue_sound] is also a bit tricky to prove *)
Lemma loop_unroll1_strong : forall c, ⟦ <{ while true do c end }> ⟧ ≅ ⟦ c ⟧;; Tau ⟦<{ while true do c end }> ⟧.
Proof.
    intros c; cbn. rewrite unfold_repeat; norm.
    eapply eq_itree_clo_bind; [reflexivity | intros ? ? <-; break].
    rewrite bind_ret_l.
    apply eqitree_Tau.
    reflexivity.
Qed.

Lemma whiletrue_sound_aux : forall (t : itree _ (mem * unit)) c, st <- t;; Tau (ℑ⟦<{ while true do c end}>⟧ (fst st)) ≈ ITree.spin.
Proof.
  einit.
  ecofix CIH.
  clear CIHH INCL INCH.
  intros.
  remember (<{while true do c end}>).
  rewrite (itree_eta ITree.spin).
  cbn.
  rewrite (itree_eta t).
  desobs t ot.
  - rewrite bind_ret_l; destruct r; cbn.
    subst c0; rewrite loop_unroll1_strong.
    rewrite interp_state_bind.
    setoid_rewrite interp_state_tau.
    etau.
  - subst; rewrite bind_tau.
    etau.
  - destruct e.
Qed.

Lemma while_true_skip_spin σ : ℑ⟦<{ while true do skip end}>⟧ σ ≈ ITree.spin.
Proof.
  einit; ecofix CIH.
  rewrite loop_unroll1_strong.
  cbn.
  rewrite interp_state_bind, interp_state_ret, bind_ret_l, interp_state_tau.
  rewrite (itree_eta ITree.spin); cbn.
  etau.
Qed.

Lemma whiletrue_sound c :
  <{ while true do c end }> ≊
  <{ while true do skip end}>.
Proof.
  intros σ.
  unfold model_com, compose.
  rewrite while_true_skip_spin.
  rewrite loop_unroll1_strong.
  rewrite interp_state_bind.
  setoid_rewrite interp_state_tau.
  rewrite whiletrue_sound_aux.
  reflexivity.
Qed.

#[local] Hint Resolve whiletrue_sound loop_unroll2_sound : opt.

(* ================================================================= *)
(** ** A sound static calculus *)

(** The elementary soundness lemmas characterizes that each set of reduction
    rule is a subrelation of the corresponding semantic equivalence.
*)

Theorem red_aexp_sound : forall a1 a2,
    red_aexp a1 a2 ->
    a1 ≈ₐ a2.
Proof.
  intros * RED; inversion RED; subst; eauto with opt.
Qed.

#[global] Instance red_aexp_sound' :
  subrelation red_aexp aexp_equiv.
Proof.
  exact red_aexp_sound.
Qed.

Theorem red_bexp_sound : forall b1 b2,
    red_bexp b1 b2 ->
    b1 ≈ᵦ b2.
Proof.
  intros * RED; inversion RED; subst; eauto with opt.
Qed.

#[global] Instance red_bexp_sound' :
  subrelation red_bexp bexp_equiv.
Proof.
  exact red_bexp_sound.
Qed.

Theorem red_com1_sound : forall c1 c2,
    red_com1 c1 c2 ->
    c1 ≡ c2.
Proof.
  intros * RED; inversion RED; subst; eauto with opt.
Qed.

#[global] Instance red_com1_sound' :
  subrelation red_com1 com_equiv.
Proof.
  intros c c' opt.
  apply red_com1_sound in opt.
  now rewrite opt.
Qed.
Theorem red_com2_sound : forall c1 c2,
    red_com2 c1 c2 ->
    c1 ≊ c2.
Proof.
  intros * RED; inversion RED; subst; eauto with opt.
Qed.

#[global] Instance red_com2_sound' :
  subrelation red_com2 com_equiv.
Proof.
  exact red_com2_sound.
Qed.

(* ================================================================= *)
(** ** Soundly lifting the calculus

    We can go further and build a full calculus by closing each reduction
    function under context, taking their join and closing the whole thing
    reflexively and transitively:
    → ≜ (C(→1) ∪ C(→2))^*

    The soundness is lifted through these closures.
*)

(** Relation combinators to extend the static calculus *)
Variant context_clo (R : rel com) : rel com :=
  | plug_clo C a b : R a b -> context_clo R (plug a C) (plug b C).

Variant join_rel {A : Type} (R S : rel A) : rel A :=
  | join_relL a b : R a b -> join_rel R S a b
  | join_relR a b : S a b -> join_rel R S a b.

Inductive trans_clo {A : Type} (R : rel A) : rel A :=
  | trans_clo_refl a    : trans_clo R a a
  | trans_clo_red a b c : R a b -> trans_clo R b c -> trans_clo R a c.

(** The full calculus *)
Definition opt_rel : rel com :=
  trans_clo (join_rel
               (context_clo red_com1)
               (context_clo red_com2)).

(** Lifting soundness through combinators *)
Lemma context_clo_lift (S R : rel com) :
  subrelation S R ->
  Proper (R ==> eq ==> R) plug ->
  subrelation (context_clo S) R.
Proof.
  intros sub resp ? ? EQ.
  inversion EQ; subst.
  now apply resp; [| reflexivity]; apply sub.
Qed.

Lemma join_rel_lift {A} (S R T : rel A) :
  subrelation S T ->
  subrelation R T ->
  subrelation (join_rel S R) T.
Proof.
  intros sub1 sub2 ? ? EQ.
  inversion EQ; subst.
  now apply sub1.
  now apply sub2.
Qed.

Lemma trans_clo_lift {A} (S R : rel A) :
  Reflexive R ->
  Transitive R ->
  subrelation S R ->
  subrelation (trans_clo S) R.
Proof.
  intros HR HT sub ? ? EQ.
  induction EQ.
  - reflexivity.
  - etransitivity; eauto.
Qed.

Lemma context_clo_red1 :
  subrelation (context_clo red_com1) com_eq.
Proof.
  apply context_clo_lift.
  exact red_com1_sound.
  exact com_eq_plug'.
Qed.

Lemma context_clo_red2 :
  subrelation (context_clo red_com2) com_equiv.
Proof.
  apply context_clo_lift.
  exact red_com2_sound.
  exact com_equiv_plug'.
Qed.

(** The whole calculus is sound *)
Theorem opt_rel_sound :
  subrelation opt_rel com_equiv.
Proof.
  unfold opt_rel.
  apply trans_clo_lift.
  1,2: typeclasses eauto.
  apply join_rel_lift.
  - etransitivity.
    apply context_clo_red1.
    typeclasses eauto.
  - apply context_clo_red2.
Qed.

(* ================================================================= *)
(** ** Proving program equivalences *)

(** We can use our static calculus to prove program equivalences.
 *)

(** Note what happens to justify this rewrite:
    -  red_aexp is a subrelation to ≈ₐ
    -  ≈ₐ is compatible with [Asgn x], leading to a ≈ relation
    -  ≈ is a congruence, hence being lifted to all the surrounding contexts
    -  ≈ is transitive, hence allowing the rewrite of the substituted program
   *)
Example congruence_example:
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }> ≊
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  rewrite minus_inv.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Constant folding as a tactic *)

(** Our set of rules can be used to define "proof-level optimizations".
    We can "run" constant folding in proofs of equivalences
    by picking out a set of rewrite rules to use.
 *)
#[global] Hint Rewrite
  (* these compute variable-free aexps: *)
  rplus rminus rmult PeanoNat.Nat.eqb_refl

  (* these compute variable-free bexps: *)
  req rle randft randtt randff rnegt rnegf

  (* these collapse trivial control flow: *)
  iftrue iffalse whiletrue whilefalse
  : cst_folding.

Ltac cst_fold := autorewrite with cst_folding; cbn.

(* ----------------------------------------------------------------- *)
(** *** Example

    And we can run it in proofs to simplify programs

    Examples from plf *)
Example fold_aexp_ex1 :
  <{ (1 + 2) * X }> ≈ₐ <{ 3 * X }>.
Proof.
  cst_fold.
  reflexivity.
Qed.

Example fold_aexp_ex2 :
  <{ X - ((0 * 6) + Y) }> ≈ₐ <{ X - (0 + Y) }>.
Proof.
  cst_fold.
  reflexivity.
Qed.

Example fold_bexp_ex1 :
  <{ true && ~(false && true) }> ≈ᵦ <{ true }>.
Proof.
  cst_fold.
  reflexivity.
Qed.

Example fold_bexp_ex2 :
  <{ (X = Y) && (0 = (2 - (1 + 1))) }> ≈ᵦ <{ (X = Y) && true }>.
Proof.
  cst_fold.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** More interesting example *)

Example fold_com_ex1 :
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  ≊ (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof.
  cst_fold.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Constant folding as a sound optimization *)

(** How does this tactic-based, semantic, constant folding relates to
    constant-folding as a syntactic optimization?
    The tactic relies on a set of rewriting rules satisfying a certain semantic
    equivalence, and this equivalence being a congruence.

    If we write the optimization, we will use exactly those facts to justify its correctness.
    The optimization on [aexp]...
*)
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x

  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (aop_sem op_plus n1 n2)
    | (a1', a2') => <{ APlus a1' a2' }>
    end

  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (aop_sem op_minus n1 n2)
    | (a1', a2') => <{ AMinus a1' a2' }>
    end

  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (aop_sem op_mult n1 n2)
    | (a1', a2') => <{ AMult a1' a2' }>
    end
  end.

(** And its proof of correctness *)
Lemma fold_constants_aexp_sound a :
  fold_constants_aexp a ≈ₐ a.
Proof.
  induction a; try rewrite <- IHa1, <- IHa2; try reflexivity; cbn.
  -
  destruct (fold_constants_aexp a1).
  2,3,4,5: now rewrite IHa1, IHa2. (* These rewrites rely on ≈ₐ being a congruence *)
  destruct (fold_constants_aexp a2); try rewrite <- IHa1, <- IHa2; try reflexivity.
  rewrite rplus. (* The optimization in this case corresponds exactly to [raop] *)
  reflexivity.

  -
  destruct (fold_constants_aexp a1).
  2,3,4,5: now rewrite IHa1, IHa2. (* These rewrites rely on ≈ₐ being a congruence *)
  destruct (fold_constants_aexp a2); try rewrite <- IHa1, <- IHa2; try reflexivity.
  rewrite rminus. (* The optimization in this case corresponds exactly to [raop] *)
  reflexivity.

  -
  destruct (fold_constants_aexp a1).
  2,3,4,5: now rewrite IHa1, IHa2. (* These rewrites rely on ≈ₐ being a congruence *)
  destruct (fold_constants_aexp a2); try rewrite <- IHa1, <- IHa2; try reflexivity.
  rewrite rmult. (* The optimization in this case corresponds exactly to [raop] *)
  reflexivity.

Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end

  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end

  | <{ a1 > a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end

  | <{ ~ b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Lemma fold_constants_bexp_sound b :
  fold_constants_bexp b ≈ᵦ b.
Proof.
  induction b; try reflexivity; cbn.
  - destruct (fold_constants_aexp a1) eqn:EQ1.
    2,3,4,5: rewrite <- EQ1; now rewrite ? fold_constants_aexp_sound.
    destruct (fold_constants_aexp a2) eqn:EQ2; try rewrite <- EQ2.
    2,3,4,5: rewrite <- ?EQ1, <- ?EQ2; now rewrite ? fold_constants_aexp_sound.
    rewrite <- req. (* The optimization in this case corresponds exactly to [req] *)
    rewrite <- EQ1, fold_constants_aexp_sound.
    rewrite <- EQ2, fold_constants_aexp_sound.
    reflexivity.

  - destruct (fold_constants_aexp a1) eqn:EQ1.
    2,3,4,5: rewrite <- EQ1; now rewrite ? fold_constants_aexp_sound.
    destruct (fold_constants_aexp a2) eqn:EQ2; try rewrite <- EQ2.
    2,3,4,5: rewrite <- ?EQ1, <- ?EQ2; now rewrite ? fold_constants_aexp_sound.
    rewrite <- rneq. (* The optimization in this case corresponds exactly to [req] *)
    rewrite <- EQ1, fold_constants_aexp_sound.
    rewrite <- EQ2, fold_constants_aexp_sound.
    reflexivity.

  - destruct (fold_constants_aexp a1) eqn:EQ1.
    2,3,4,5: now rewrite <- EQ1, ? fold_constants_aexp_sound.
    destruct (fold_constants_aexp a2) eqn:EQ2; try rewrite <- EQ2.
    2,3,4,5: now rewrite <- EQ1, ? fold_constants_aexp_sound.
    rewrite <- rle. (* The optimization in this case corresponds exactly to [rle] *)
    rewrite <- EQ1, fold_constants_aexp_sound.
    rewrite <- EQ2, fold_constants_aexp_sound.
    reflexivity.

  - destruct (fold_constants_aexp a1) eqn:EQ1.
    2,3,4,5: now rewrite <- EQ1, ? fold_constants_aexp_sound.
    destruct (fold_constants_aexp a2) eqn:EQ2; try rewrite <- EQ2.
    2,3,4,5: now rewrite <- EQ1, ? fold_constants_aexp_sound.
    rewrite <- rgt. (* The optimization in this case corresponds exactly to [rle] *)
    rewrite <- EQ1, fold_constants_aexp_sound.
    rewrite <- EQ2, fold_constants_aexp_sound.
    reflexivity.

  - destruct (fold_constants_bexp b) eqn:EQ.
    all: try (rewrite <- IHb; reflexivity).
    rewrite <- IHb.
    rewrite <- rnegt. reflexivity.
    rewrite <- IHb.
    rewrite <- rnegf. reflexivity.

  - destruct (fold_constants_bexp b1) eqn:EQ1.
    all: try now rewrite IHb1, IHb2.
    all: destruct (fold_constants_bexp b2) eqn:EQ2; try now rewrite IHb1, IHb2.
    all:rewrite <- IHb1, <- IHb2.
    now rewrite randtt.
    rewrite and_comm. now rewrite randft.
    now rewrite randft.
    now rewrite randff.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Constant folding over commands *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}> => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Lemma fold_constants_com_sound c :
  fold_constants_com c ≊ c.
Proof.
  induction c; try reflexivity.
  - now cbn; rewrite fold_constants_aexp_sound.
  - now cbn; rewrite IHc1,IHc2.
  - cbn.
    repeat break_match.
    all: rewrite ?IHc1, ?IHc2.
    all: rewrite <- (fold_constants_bexp_sound b), EQ.
    all: try reflexivity.
    now rewrite iftrue.  (* The optimization in this case corresponds exactly to [iftrue] *)
    now rewrite iffalse. (* The optimization in this case corresponds exactly to [iffalse] *)
  - cbn.
    repeat break_match.
    all: rewrite <- (fold_constants_bexp_sound b), EQ.
    all: try now rewrite IHc.
    now rewrite <- whiletrue.  (* The optimization in this case corresponds exactly to [whiletrue] *)
    now rewrite <- whilefalse. (* The optimization in this case corresponds exactly to [whilefalse] *)
Qed.

(* ----------------------------------------------------------------- *)
(** *** Example of optimizing Commands

    Of course now that we have a sound syntactic level transformation,
    we can use this instead of our tactic for better efficiency.
*)
Example fold_com_ex1_revisited :
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  ≊ (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof.
  rewrite <- fold_constants_com_sound.
  cbn.
  reflexivity.
Qed.

Section State_Algebra.

  (** * State algebra
    We interpret our memory events into a state monad.
    One way to pinpoint that this structure is the right
    one is to check that it is a model for the state algebra,
    that is that it satisfies a set of axioms.

    Four of them axiomatize the interaction between two
    consecutive memory events over the same variable:
    + wr x v1; wr x v2 == wr x v2
    + v <- rd x;; wr x v == ret tt
    + v <- rd x;; v' <- rd x;; k v v' == v <- rd x;; k v v.
    + wr x v;; rd x == wr x v;; Ret v.

    Three additional events characterize that events over
    distinct variables commute.

    We first prove similar these results as direct shallow
    manipulations of the state, and then lift them to
    the interpretation of events.

    Note: At this point, we do _not_ yet lift things to the
    level of the source language. Indeed, things are more
    involved at the source: writes can involve an arbitrary
    number of reads in the evaluation of expressions notably.
*)

  (** ** Algebraic laws over concrete manipulations of the memory *)

  Lemma upd_lu : forall (σ : state)  x, (x !-> (σ x) ; σ) = σ.
  Proof.
    intros. apply t_update_same.
  Qed.

  Lemma upd_lu_eq : forall (σ : state) x v, (x !-> v ; σ) x = v.
  Proof.
    intros.
    apply t_update_eq.
  Qed.

  Lemma upd_lu_ineq : forall (σ:state) x y v,
      x <> y ->
      (x !-> v ; σ) y = σ y.
  Proof.
    intros.
    apply t_update_neq. assumption.
  Qed.

  Lemma upd_upd : forall (σ:state) x v1 v2, (x !-> v2 ; (x !-> v1 ; σ))  =  (x !-> v2 ; σ).
  Proof.
    intros.
    apply t_update_shadow.
  Qed.

  Lemma upd_upd_comm : forall (σ:state) x y v1 v2,
      x <> y ->
      (y !-> v2 ; x !-> v1 ; σ) =
      (x !-> v1 ; y !-> v2 ; σ).
  Proof.
    intros.
    apply t_update_permute. assumption.
  Qed.

  (** ** Algebraic laws over monadic computations *)
  Notation "x '==' y" := (forall σ, ℑ x σ ≈ ℑ y σ) (at level 70).

  Lemma rd_wr : forall x,
      v <- rd x;; wr x v == Ret tt.
  Proof.
    intros x σ; cbn.
    norm.
    now cbn; rewrite upd_lu.
  Qed.

  Lemma wr_wr : forall x v1 v2,
      wr x v1;; wr x v2 == wr x v2.
  Proof.
    intros *.
    norm.
    now cbn; rewrite upd_upd.
  Qed.

  Lemma rd_rd {R} : forall x (k : val -> val -> itree MemE R),
      v <- rd x;; v' <- rd x;; k v v' == v <- rd x;; k v v.
  Proof.
    intros *.
    norm.
    now cbn.
  Qed.

  Lemma wr_rd : forall x v,
      wr x v;; rd x == wr x v;; Ret v.
  Proof.
    intros *.
    norm.
    now cbn; rewrite upd_lu_eq.
  Qed.

  Lemma wr_wr_comm : forall x y v v',
      x <> y ->
      wr x v;; wr y v' == wr y v';; wr x v.
  Proof.
    intros * INEQ σ.
    norm.
    now cbn; rewrite upd_upd_comm.
  Qed.

  Lemma wr_rd_comm : forall x y v,
      x <> y ->
      wr x v;; rd y == v' <- rd y;; wr x v;; Ret v'.
  Proof.
    intros * INEQ σ.
    norm.
    now cbn; rewrite upd_lu_ineq.
  Qed.

  Lemma rd_rd_comm {R} : forall x y (k : val -> val -> itree _ R),
      x <> y ->
      v1 <- rd x;; v2 <- rd y;; k v1 v2 ==
      v2 <- rd y;; v1 <- rd x;; k v1 v2.
  Proof.
    intros * INEQ σ.
    norm.
    now reflexivity.
  Qed.

  (* A bit curious about the "algebraic" status of this one *)
  Lemma kill_rd {R} : forall x (t : itree _ R),
      rd x;; t == t.
  Proof.
    intros *.
    now norm.
  Qed.

End State_Algebra.

Lemma self_asgn_sound : forall x,
    <{ x := x }> ≊ <{ skip }>.
Proof.
  intros x σ.
  unfold model_com, Basics.compose; cbn.
  norm.
  ret.
  cbn.
  now rewrite upd_lu.
Qed.

(* 2024-06-13 11:26 *)
