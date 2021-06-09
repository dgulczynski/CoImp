
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From LF Require Import Maps.
From LF Require Import Imp.
From Coq Require Import Classical.

Reserved Notation
         "st '=[' c ']=>inf'"
         (at level 40, c custom com at level 99).

CoInductive evalinf : com -> state -> Prop :=
  | I_Seq1 : forall c1 c2 st,
      st  =[ c1 ]=>inf  ->
      st  =[ c1 ; c2 ]=>inf
  | I_Seq2 : forall c1 c2 st st',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=>inf ->
      st  =[ c1 ; c2 ]=>inf
  | I_IfTrue : forall st b c1 c2,
      beval st b = true ->
      st =[ c1 ]=>inf ->
      st =[ if b then c1 else c2 end]=>inf
  | I_IfFalse : forall st b c1 c2,
      beval st b = false ->
      st =[ c2 ]=>inf ->
      st =[ if b then c1 else c2 end]=>inf
  | I_WhileBody : forall st b c,
      beval st b = true ->
      st  =[ c ]=>inf ->
      st  =[ while b do c end ]=>inf
  | I_WhileLoop : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=>inf ->
      st  =[ while b do c end ]=>inf
  where "st =[ c ]=>inf" := (evalinf c st ).


Lemma loop_diverges: forall st,
    st =[ loop ]=>inf.
Proof.
    cofix COINDHYP; intros.
    unfold loop.
    eapply I_WhileLoop; auto using E_Skip.
Qed.

Lemma eval_evalinf_exclusive: forall c st st',
    st =[ c ]=> st' -> ~(st =[ c ]=>inf).
Proof.
    intros c st st'.
    induction 1; intros contra; inversion contra;
    subst; try rewrite H in H5; try rewrite H in H2; try discriminate; auto.
    - apply IHeval2; remember (eval_deterministic _ _ _ _ H H3); subst; auto.
    - generalize (eval_deterministic _ _ _ _ H0 H5); intros; subst st'0; auto.
Qed.

Reserved Notation
         "st '=[' c ']=>>' st'"
         (at level 40, c custom com at level 99).

CoInductive coeval : com -> state -> state -> Prop :=
| C_Skip : forall (st : state),
    st =[ skip ]=>> st
| C_Ass  : forall st a n x,
    aeval st a = n ->
    st =[ x := a ]=>> (x !-> n; st)
| C_Seq : forall c1 c2 st st' st'',
    st  =[ c1 ]=>> st'  ->
    st' =[ c2 ]=>> st'' ->
    st  =[ c1 ; c2 ]=>> st''
| C_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=>> st' ->
    st =[ if b then c1 else c2 end]=>> st'
| C_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=>> st' ->
    st =[ if b then c1 else c2 end]=>> st'
| C_WhileFalse : forall b st c,
    beval st b = false ->
    st =[ while b do c end ]=>> st
| C_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st  =[ c ]=>> st' ->
    st' =[ while b do c end ]=>> st'' ->
    st  =[ while b do c end ]=>> st''
where "st =[ c ]=>> st'" := (coeval c st st').

Lemma eval_coeval:
  forall c st st', st =[ c ]=> st' -> st =[ c ]=>> st'.
Proof.
  induction 1; econstructor; eauto; assumption.
Qed.

Lemma coeval_loop: forall st, coeval loop st st.
Proof.
    cofix COINDHYP.
    intros; unfold loop.
    eapply C_WhileTrue; auto; constructor.
Qed.

Lemma coeval_noteval_evalinf_while_true:
    forall b c st st', st =[ while b do c end]=>> st'
        -> ~(st =[ while b do c end ]=> st')
        -> st =[ while b do c end ]=>inf.
Proof.
  cofix COINDHYP. intros.
  elim (classic (st =[ c ]=> st')); intro.
  inversion H; subst.
  - elim H0. apply E_WhileFalse; auto.
  - inversion H8; subst.
    + elim H0. eapply E_WhileTrue; eauto. apply E_WhileFalse; auto.
    + admit.
  - eauto.
Admitted.
  
Lemma coeval_noteval_evalinf:
  forall c st st', st =[ c ]=>> st' -> ~(st =[ c ]=> st') -> st =[ c ]=>inf.
Proof.
    cofix COINDHYP. intros.
    inversion H; subst.
    - (* skip *) elim H0; constructor; auto.
    - (* x := a *) elim H0; constructor; auto.
    - (* c1; c2 *) elim (classic (st =[ c1 ]=> st'0)); intro.
      + (* st =[ c1 ]=> st'0 *)
        elim (classic (st'0 =[ c2 ]=> st')); intro.
        * (* st =[ c2 ]=> st'0 *)
          elim H0. econstructor. apply H3. apply H4.
        * (* ~ st =[ c2 ]=> st'0 *)
          eapply I_Seq2. apply H3. eauto.
      + (* ~ st =[ c1 ]=> st'0 *)
        eapply I_Seq1. eauto.
    - (* if true then c1 else c2 end *)
      elim (classic (st =[ c1 ]=> st')); intro.
      + (* st =[ c1 ]=> st' *)
        elim H0. econstructor. apply H1. apply H3.
      + (* ~st =[ c1 ]=> st' *)
        eapply I_IfTrue. apply H1. eauto.
    - (* if false then c1 else c2 end *)
      elim (classic (st =[ c2 ]=> st')); intro.
        + (* st =[ c2 ]=> st' *)
          elim H0. eapply E_IfFalse. apply H1. apply H3.
        + (* ~st =[ c2 ]=> st' *)
          eapply I_IfFalse. apply H1. eauto.
    - (* while false do c end *)
      elim H0. eapply E_WhileFalse; auto.
    - (* while true do c end *) 
    eapply coeval_noteval_evalinf_while_true; eauto.
Qed.