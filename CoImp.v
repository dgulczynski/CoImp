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
  eapply I_WhileLoop.
  - reflexivity.
  - constructor.
  - fold loop. apply COINDHYP.
Qed.

Lemma state_unchaning_loop_converges: forall b c st,
  beval st b = true ->
  st =[ c ]=> st ->
  st =[ while b do c end ]=>inf.
Proof.
  cofix COINDHYP. intros.
  eapply I_WhileLoop.
  - auto.
  - eauto.
  - eapply COINDHYP; auto.
Qed.

Lemma loop_diverges': forall st,
  st =[ loop ]=>inf.
Proof.
  intros.
  apply state_unchaning_loop_converges; auto; constructor.
Qed.


Definition loop' : com :=
  <{ while 1 <= X do
       X := X + 1
     end }>.

Lemma loop'_converges: forall st,
  st X = 0 -> st =[ loop' ]=> st /\ ~st =[ loop']=>inf.
Proof.
  intros st Hx; inversion Hx; split.
  - econstructor; simpl; rewrite H0; reflexivity.
  - intros H; inversion H; subst;
    simpl in H3; rewrite H0 in H3; discriminate.  
Qed.

Theorem eval_evalinf_exclusive: forall c st st',
    st =[ c ]=> st' -> ~(st =[ c ]=>inf).
Proof.
    intros c st st' H.
    induction H; intros contra; inversion contra;
    subst; try congruence; auto.
    - apply IHeval2. remember (eval_deterministic _ _ _ _ H H3); subst; auto.
    - generalize (eval_deterministic _ _ _ _ H0 H5); intros. subst st'0; auto.
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

Theorem eval_coeval: forall c st st',
    st =[ c ]=> st' ->
    st =[ c ]=>> st'.
Proof.
  induction 1; econstructor; eauto; assumption.
Qed.

Lemma coeval_loop: forall st,
  st =[ loop ]=>> st.
Proof.
    cofix COINDHYP.
    intros; unfold loop.
    eapply C_WhileTrue.
    - auto.
    - constructor.
    - apply COINDHYP.
Qed.

Lemma coeval_loop': forall st,
  st X = 0 -> st =[ loop ]=>> st.
Proof.
    cofix COINDHYP.
    intros; unfold loop.
    eapply C_WhileTrue.
    - auto.
    - constructor.
    - apply COINDHYP; auto.
Qed.

Lemma coeval_noteval_evalinf: forall c st st',
  st =[ c ]=>> st' -> ~(st =[ c ]=> st') -> st =[ c ]=>inf.
Proof.
    cofix COINDHYP. intros.
    inversion H; subst.
    - (* skip *) elim H0; constructor.
    - (* x := a *) elim H0; constructor; auto.
    - (* c1; c2 *) elim (classic (st =[ c1 ]=> st'0)); intro.
      + (* st =[ c1 ]=> st'0 *)
        elim (classic (st'0 =[ c2 ]=> st')); intro.
        * (* st'0 =[ c2 ]=> st' *)
          elim H0. econstructor; try apply H3;  apply H4.
        * (* ~ st'0 =[ c2 ]=> st' *)
          eapply I_Seq2; try apply H3. eapply COINDHYP; eauto; auto.
      + (* ~ st =[ c1 ]=> st'0 *)
        eapply I_Seq1; eapply COINDHYP; eauto.
    - (* if true then c1 else c2 end *)
      elim (classic (st =[ c1 ]=> st')); intro.
      + (* st =[ c1 ]=> st' *)
        elim H0; econstructor; try apply H1; apply H3.
      + (* ~st =[ c1 ]=> st' *)
        eapply I_IfTrue; try apply H1; eauto.
    - (* if false then c1 else c2 end *)
      elim (classic (st =[ c2 ]=> st')); intro.
        + (* st =[ c2 ]=> st' *)
          elim H0. eapply E_IfFalse; try apply H1; apply H3.
        + (* ~st =[ c2 ]=> st' *)
          eapply I_IfFalse; try apply H1; eauto.
    - (* while false do c end *)
      elim H0. eapply E_WhileFalse; auto.
    - (* while true do c end *) 
      elim (classic ( st =[ c0 ]=> st'0 )); intro.
      (* st =[ c0 ]=> st'0 *)
      + elim (classic ( st'0 =[ while b do c0 end ]=> st')); intro.
        (* ~ st'0 =[ while b do c0 end ]=> st' *)
        * elim H0; eauto using E_WhileTrue.
        (* ~ st'0 =[ while b do c0 end ]=> st' *)
        * eapply I_WhileLoop; eauto.
      (* ~ st =[ c0 ]=> st'0 *)
      + eapply I_WhileBody; eauto.
Qed.

Theorem coeval_eval_or_evalinf: forall c st st',
    st =[ c ]=>> st' ->
    st =[ c ]=> st' \/ st =[ c ]=>inf.
Proof.
  intros. elim (classic (st =[ c ]=> st')); intros.
  left; auto.
  right. eapply coeval_noteval_evalinf; eauto.
Qed.


Theorem eval_coeval_deterministic: forall c st st',
    st =[ c ]=> st' ->
    forall st'', st =[ c ]=>> st''-> st' = st''.
Proof.
  intros c st st' H. induction H; intros st''' H'; 
   inversion H'; subst; try congruence; auto.
   - (* st =[c1; c2]=>>st''' *)
      remember (IHeval1 _ H3); subst; auto.
   - (* st =[ while true do c end ]=>> st''' *)
      remember (IHeval1 _ H5); subst; auto.
Qed.
