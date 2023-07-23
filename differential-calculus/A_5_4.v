Require Export A_5_2.

Module A5_4.

(* 高阶导数 *)
Fixpoint dN (f : Fun) (n : nat) :=
  match n with
  | O => f
  | S n => \{\ λ x y, derivative (dN f n) x y \}\
  end.
 
Definition der f x n := cR \{ λ y', derivative (dN f n) x y' \}.

Notation "f '^' n [ x ]" := (der f x n)(at level 20). 

Lemma Lemma5_6 : ∀ (f : Fun) (x0 : R) (n : nat),
   x0 ∈ dom[dN f n] ->
  (∀ k, (k < n)%nat -> ∃ δ, δ > 0 /\
    (Neighbor x0 δ ⊂ dom[dN f k])).
Proof.
  intros f x0 n. induction n as [|n IHn].
  - simpl. intros H0 k H1. apply Nat.nlt_0_r in H1.
    contradiction.
  - intros H0 k H1.
    applyAxiomII H0.
    destruct H0 as [y H0].
    applyAxiomII' H0.
    destruct H0 as [H0 [[δ' [H2 H3]] H4]].
    assert (H5 : x0 ∈ dom[dN f n]).
    { apply H3. apply AxiomII. apply Abs_R.
      lra. }
    generalize (IHn H5). intros H6.
    apply lt_n_Sm_le in H1.
    apply le_lt_or_eq in H1 as [H1 | H1]; auto.
    exists δ'. rewrite H1. split; auto.
Qed.

Lemma Lemma5_6' : ∀ (f : Fun) (x0 : R) (n : nat),
   x0 ∈ dom[dN f n] ->
   (∃ δ, δ > 0 /\ (∀ k, (k < n)%nat -> 
    (Neighbor x0 δ ⊂ dom[dN f k]))).
Proof.
  intros f x0 n H0. induction n as [|n IHn].
  - exists 1. split; [lra | intros k I1].
    apply Nat.nlt_0_r in I1.
    contradiction.
  - apply Lemma5_6 with (k := n) in H0 as I1;
    try apply Nat.lt_succ_diag_r.
    destruct I1 as [δ1 [I1 I2]].
    assert (I3 : x0 ∈ dom[dN f n]).
    { apply I2. apply AxiomII.
      apply Abs_R. lra. }
    apply IHn in I3 as [δ2 [I3 I4]].
    generalize (Lemma1 δ1 δ2 I1 I3).
    intros [δ [I5 [I6 I7]]].
    exists δ. split; auto.
    intros k I8. apply lt_n_Sm_le in I8.
    apply le_lt_or_eq in I8 as [I8 | I8].
    + apply I4 in I8.
      intros x I9. apply I8.
      applyAxiomII I9. apply AxiomII.
      lra.
    + rewrite I8. intros x I9.
      apply I2. applyAxiomII I9.
      apply AxiomII. lra.
Qed.

(* 定义运算：n*(n-1)*(n-2)*...*(n-m+1) *)
Fixpoint mult_NM (n m : nat) :=
  match n, m with
  | O, _ => 1%nat
  | S n', O => 1%nat
  | S n', S m' => ((S n') * (mult_NM n' m'))%nat
  end.

Lemma mult_NM_ne_0 : ∀ n k, (mult_NM n k <> 0)%nat.
Proof.
  intros n. induction n as [|n IHn].
  - intros k. induction k as [|k IHk]; simpl; auto.
  - intros k. destruct k as [|k].
    + simpl. auto.
    + simpl. generalize (IHn k); intros H0.
      apply not_eq_sym in H0.
      apply neq_0_lt in H0.
      apply not_eq_sym.
      apply Nat.lt_neq. apply Nat.add_pos_nonneg; auto.
      apply Nat.le_0_l.
Qed.

(* 幂函数的k阶导数 *)
Lemma Lemma5_7 : ∀ a c n k, (k <= n)%nat ->
  (dN (\{\ λ x y, y = c*(x-a)^^n \}\) k) =
  \{\ λ x y, y = c * (INR (mult_NM n k))
    * (x-a)^^(n-k) \}\.
Proof.
  intros a c n k H0.
  generalize dependent n.
  generalize dependent c.
  induction k as [|k IHk].
  - intros c n H0. simpl. rewrite <- minus_n_O.
    assert (I1 : c * INR (mult_NM n 0) = c).
    { destruct n; simpl; field. }
    rewrite I1. reflexivity.
  - intros c n I1. simpl. apply le_Sn_le in I1 as I2.
    rewrite IHk; auto.
    assert (I3 : c * INR (mult_NM n k) * INR(n - k) =
      c * INR (mult_NM n (S k))).
    { rewrite Rmult_assoc. rewrite <- mult_INR.
      assert (I3 : ∀ n, (0 < n -> k < n ->
        mult_NM n k * (n - k) =
        mult_NM n (S k))%nat).
      { clear I1 I2 IHk. intros m.
        generalize dependent k.
        induction m as [|m IHm].
        - intros k J1 J2. apply Nat.lt_irrefl in J1.
          contradiction.
        - intros k J1 K2. apply lt_n_Sm_le in J1.
          apply le_lt_or_eq in J1 as [J1 | J1].
          + destruct k.
            * simpl. destruct m.
              -- simpl. reflexivity.
              -- simpl. rewrite <- plus_n_O.
                rewrite Nat.mul_1_r. reflexivity.
            * apply lt_S_n in K2.
              assert (J2 : ∀ n0 m0,
              (mult_NM (S n0) (S m0) =
              (S n0) * mult_NM n0 m0)%nat).
              { intros n0 m0. simpl. reflexivity. }
              rewrite J2. rewrite J2.
              rewrite <- IHm; auto.
              assert (J3 : (S m - S k = m - k)%nat).
              { simpl. reflexivity. }
              rewrite J3. apply mult_assoc_reverse.
          + rewrite <- J1 in *.
            apply lt_n_Sm_le in K2.
            apply le_n_0_eq in K2.
            rewrite <- K2 in *.
            simpl. reflexivity. }
      rewrite I3; auto.
      generalize (Nat.lt_0_succ k). intro I4.
      eapply Nat.lt_le_trans; eauto. }
    apply AxiomI. intros [x y]; split; intro I4;
    applyAxiomII' I4; apply AxiomII'.
    + generalize (Lemma5_5 a (c * INR (mult_NM n k))
        x (n - k)). intro I5.
      assert (I6 : y = (c * INR (mult_NM n k)
        * INR (n - k) * (x - a) ^^ (n - k - 1))).
      { eapply derivativeUnique; eauto. }
      rewrite I6. rewrite I3.
      rewrite <- Nat.sub_add_distr.
      rewrite Nat.add_1_r. reflexivity.
    + pattern (S k) at 2 in I4.
      rewrite <- Nat.add_1_r in I4.
      rewrite Nat.sub_add_distr in I4.
      rewrite <- I3 in I4. rewrite I4.
      apply Lemma5_5.
Qed.

Lemma Lemma5_7_1 : ∀ a n k, (k <= n)%nat ->
  (dN (\{\ λ x y, y = (x-a)^^n \}\) k) =
  \{\ λ x y, y = (INR (mult_NM n k))
    * (x-a)^^(n-k) \}\.
Proof.
  intros a n k H0.
  assert (H1 : \{\ λ x y, y = (x - a) ^^ n \}\ =
    \{\ λ x y, y = 1 * (x - a) ^^ n \}\).
  { apply AxiomI; intros [x y];
    split; intro I1;
    applyAxiomII' I1; apply AxiomII'; lra. }
  rewrite H1. rewrite Lemma5_7; auto.
  apply AxiomI; intros [x y];
  split; intro I1;
  applyAxiomII' I1; apply AxiomII'; lra.
Qed.

Lemma Lemma5_7' : ∀ a c n k, (n < k)%nat ->
  (dN (\{\ λ x y, y = c*(x-a)^^n \}\) k) =
  \{\ λ x y, y = 0 \}\.
Proof.
  intros a c n k H0. induction k as [|k IHk].
  - apply Nat.nlt_0_r in H0.
    contradiction.
  - apply lt_n_Sm_le in H0.
    apply le_lt_or_eq in H0 as [H0 | H0].
    + apply IHk in H0 as I1.
      simpl. rewrite I1. apply AxiomI.
      intros [x y]; split; intro J1;
      applyAxiomII' J1; apply AxiomII'.
      * generalize (Lemma5_12 0 x).
        intros J2. eapply derivativeUnique; eauto.
      * rewrite J1. apply Lemma5_12.
    + rewrite <- H0. simpl.
      rewrite (Lemma5_7 a c n n (le_n n)).
      rewrite Nat.sub_diag. simpl.
      apply AxiomI. intros [x y];
      split; intro I1; applyAxiomII' I1;
      apply AxiomII'.
      * generalize (Lemma5_12
          (c * INR (mult_NM n n) * 1) x).
        intros I2. eapply derivativeUnique; eauto.
      * rewrite I1. apply Lemma5_12.
Qed.

Lemma Lemma5_8 : ∀ x n f, (dN f (S n)) [x] = (dN f n) '[x].
Proof.
  intros x n f. simpl. unfold der. unfold ValueR.
  assert (I1 : \{ λ y, [x, y] ∈
    \{\ λ x1 y0, derivative (dN f n) x1 y0 \}\ \} =
    \{ λ y', derivative (dN f n) x y' \}).
  { apply AxiomI; intros y; split; intro J1;
    applyAxiomII J1; apply AxiomII.
    - applyAxiomII' J1. assumption.
    - apply AxiomII'. assumption. }
  rewrite I1. reflexivity.
Qed.

Lemma Lemma5_13 : ∀ f g n x, 
  x ∈ dom[dN f n] -> x ∈ dom[dN g n] ->
  [x, (dN f n)[x] - (dN g n)[x]] ∈
    (dN \{\ λ x y, y = f[x] - g[x] \}\ n).
Proof.
  intros f g n. induction n as [|n IHn].
  - intros x H0 H1. simpl.
    apply AxiomII'. reflexivity.
  - intros x H0 H1.
    simpl (dN \{\ λ x y, y = f [x] - g [x] \}\ (S n)).
    apply AxiomII'.
    rewrite Lemma5_8. rewrite Lemma5_8.
    apply Lemma5_6 with (k := n) in H0 as H2;
      try apply Nat.lt_succ_diag_r.
    destruct H2 as [δ1 [H2 H3]].
    apply Lemma5_6 with (k := n) in H1 as H4;
      try apply Nat.lt_succ_diag_r.
    destruct H4 as [δ2 [H4 H5]].
    assert (H6 : derivative (\{\ λ x0 y,
      y = (dN f n)[x0] - (dN g n)[x0] \}\) x
      (dN f n '[x] - dN g n '[x])).
    { apply Theorem5_4_2.
      - applyAxiomII H0. destruct H0 as [y H0].
        applyAxiomII' H0. exists y.
        assumption.
      - applyAxiomII H1. destruct H1 as [y H1].
        applyAxiomII' H1. exists y.
        assumption. }
    apply Lemma5_9 with (f := \{\ λ x0 y,
      y = (dN f n)[x0] - (dN g n)[x0] \}\); auto.
    + destruct n.
      * simpl. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2; assumption.
      * simpl. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        eapply derivativeUnique; eauto.
    + generalize (Lemma1 δ1 δ2 H2 H4).
      intros [δ [I1 [I2 I3]]]. exists δ.
      split; auto. intros x0 I4. split.
      * apply AxiomII.
        exists ((dN f n) [x0] - (dN g n) [x0]).
        applyAxiomII I4.
        apply IHn; [apply H3 | apply H5];
        apply AxiomII; lra.
      * assert (I5 : \{\ λ x1 y, y =
          (dN f n) [x1] - (dN g n) [x1] \}\ [x0]
          = (dN f n) [x0] - (dN g n) [x0]).
        { apply f_x.
          - intros x1 y1 z1 J1 J2.
            applyAxiomII' J1; applyAxiomII' J2.
            rewrite J2; assumption.
          - apply AxiomII'. reflexivity. }
        rewrite I5. symmetry. apply f_x.
        -- destruct n; intros x1 y1 z1 J1 J2;
          applyAxiomII' J1; applyAxiomII' J2.
          ++ rewrite J2; assumption.
          ++ eapply derivativeUnique; eauto.
        -- applyAxiomII I4. apply IHn;
          [apply H3 | apply H5];
          apply AxiomII; lra.
Qed.

Lemma Lemma5_13' : ∀ f g n x, 
  x ∈ dom[dN f n] -> x ∈ dom[dN g n] ->
  [x, (dN f n)[x] + (dN g n)[x]] ∈
    (dN \{\ λ x y, y = f[x] + g[x] \}\ n).
Proof.
  intros f g n. induction n as [|n IHn].
  - intros x H0 H1. simpl.
    apply AxiomII'. reflexivity.
  - intros x H0 H1.
    simpl (dN \{\ λ x y, y = f [x] + g [x] \}\ (S n)).
    apply AxiomII'.
    rewrite Lemma5_8. rewrite Lemma5_8.
    apply Lemma5_6 with (k := n) in H0 as H2;
      try apply Nat.lt_succ_diag_r.
    destruct H2 as [δ1 [H2 H3]].
    apply Lemma5_6 with (k := n) in H1 as H4;
      try apply Nat.lt_succ_diag_r.
    destruct H4 as [δ2 [H4 H5]].
    assert (H6 : derivative (\{\ λ x0 y,
      y = (dN f n)[x0] + (dN g n)[x0] \}\) x
      (dN f n '[x] + dN g n '[x])).
    { apply Theorem5_4_1.
      - applyAxiomII H0. destruct H0 as [y H0].
        applyAxiomII' H0. exists y.
        assumption.
      - applyAxiomII H1. destruct H1 as [y H1].
        applyAxiomII' H1. exists y.
        assumption. }
    apply Lemma5_9 with (f := \{\ λ x0 y,
      y = (dN f n)[x0] + (dN g n)[x0] \}\); auto.
    + destruct n.
      * simpl. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2; assumption.
      * simpl. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        eapply derivativeUnique; eauto.
    + generalize (Lemma1 δ1 δ2 H2 H4).
      intros [δ [I1 [I2 I3]]]. exists δ.
      split; auto. intros x0 I4. split.
      * apply AxiomII.
        exists ((dN f n) [x0] + (dN g n) [x0]).
        applyAxiomII I4.
        apply IHn; [apply H3 | apply H5];
        apply AxiomII; lra.
      * assert (I5 : \{\ λ x1 y, y =
          (dN f n) [x1] + (dN g n) [x1] \}\ [x0]
          = (dN f n) [x0] + (dN g n) [x0]).
        { apply f_x.
          - intros x1 y1 z1 J1 J2.
            applyAxiomII' J1; applyAxiomII' J2.
            rewrite J2; assumption.
          - apply AxiomII'. reflexivity. }
        rewrite I5. symmetry. apply f_x.
        -- destruct n; intros x1 y1 z1 J1 J2;
          applyAxiomII' J1; applyAxiomII' J2.
          ++ rewrite J2; assumption.
          ++ eapply derivativeUnique; eauto.
        -- applyAxiomII I4. apply IHn;
          [apply H3 | apply H5];
          apply AxiomII; lra.
Qed.

Lemma Lemma5_14 : ∀ c n, (0 < n)%nat ->
  (dN (\{\ λ x y, y = c \}\) n) =
  \{\ λ x y, y = 0 \}\.
Proof.
  intros c n H0. induction n as [|n IHn].
  - apply Nat.lt_irrefl in H0.
    contradiction.
  - apply lt_n_Sm_le in H0.
    apply le_lt_or_eq in H0 as [H0 | H0].
    + apply IHn in H0 as I1.
      simpl. apply AxiomI; intros [x y];
      split; intro I2;
      applyAxiomII' I2; apply AxiomII'.
      * rewrite I1 in I2.
        generalize (Lemma5_12 0 x).
        intros I3. eapply derivativeUnique; eauto.
      * rewrite I2. rewrite I1.
        apply Lemma5_12.
    + rewrite <- H0. simpl.
      apply AxiomI; intros [x y];
      split; intro I2;
      applyAxiomII' I2; apply AxiomII'.
      * generalize (Lemma5_12 c x).
        intros I3. eapply derivativeUnique; eauto.
      * rewrite I2. apply Lemma5_12.
Qed.

Lemma Lemma5_15 : ∀ f n, (0 < n)%nat -> Function (dN f n).
Proof.
  intros f n H0. destruct n as [|n].
  - apply Nat.lt_irrefl in H0. contradiction.
  - simpl. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    eapply derivativeUnique; eauto.
Qed.

Lemma Lemma5_16 : ∀ f n, Function f -> Function (dN f n).
Proof.
  intros f n H0. destruct n as [|n].
  - simpl. assumption.
  - simpl. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    eapply derivativeUnique; eauto.
Qed.

Lemma Lemma5_17 : ∀ f g n x y1 y2, (0 < n)%nat ->
  [x, y1] ∈ (dN f n) -> [x, y2] ∈ (dN g n) ->
  [x, y1 - y2] ∈ (dN \{\ λ x y,
    y = f[x] - g[x] \}\ n).
Proof.
  intros f g n x y1 y2 H0 H1 H2.
  apply f_x in H1 as H3; try apply Lemma5_15; auto.
  apply f_x in H2 as H4; try apply Lemma5_15; auto.
  rewrite <- H3. rewrite <- H4.
  apply Lemma5_13; apply AxiomII;
  [exists y1 | exists y2]; auto.
Qed.

Lemma Lemma5_17' : ∀ f g n x y1 y2, (0 < n)%nat ->
  [x, y1] ∈ (dN f n) -> [x, y2] ∈ (dN g n) ->
  [x, y1 + y2] ∈ (dN \{\ λ x y,
    y = f[x] + g[x] \}\ n).
Proof.
  intros f g n x y1 y2 H0 H1 H2.
  apply f_x in H1 as H3; try apply Lemma5_15; auto.
  apply f_x in H2 as H4; try apply Lemma5_15; auto.
  rewrite <- H3. rewrite <- H4.
  apply Lemma5_13'; apply AxiomII;
  [exists y1 | exists y2]; auto.
Qed.

Lemma Lemma5_18 : ∀ f g n x y1 y2,
  Function f -> Function g ->
  [x, y1] ∈ (dN f n) -> [x, y2] ∈ (dN g n) ->
  [x, y1 - y2] ∈ (dN \{\ λ x y,
    y = f[x] - g[x] \}\ n).
Proof.
  intros f g n x y1 y2 H0 H1 H2 H3.
  apply f_x in H2 as H4.
  apply f_x in H3 as H5.
  - rewrite <- H4. rewrite <- H5.
    apply Lemma5_13; apply AxiomII;
    [exists y1 | exists y2]; auto.
  - apply Lemma5_16; assumption.
  - apply Lemma5_16; assumption.
Qed.

Lemma Lemma5_18' : ∀ f g n x y1 y2,
  Function f -> Function g ->
  [x, y1] ∈ (dN f n) -> [x, y2] ∈ (dN g n) ->
  [x, y1 + y2] ∈ (dN \{\ λ x y,
    y = f[x] + g[x] \}\ n).
Proof.
  intros f g n x y1 y2 H0 H1 H2 H3.
  apply f_x in H2 as H4.
  apply f_x in H3 as H5.
  - rewrite <- H4. rewrite <- H5.
    apply Lemma5_13'; apply AxiomII;
    [exists y1 | exists y2]; auto.
  - apply Lemma5_16; assumption.
  - apply Lemma5_16; assumption.
Qed.

End A5_4.

Export A5_4.