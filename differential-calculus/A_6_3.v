
Require Export A_6_2.

Module A6_3.

(* 定义：数列前n项和 *)
Fixpoint Σ (x : Seq) (n : nat) :=
  match n with
  | 0%nat => x[0%nat]
  | S n => Σ x n + x[S n]
  end.

(* 定义: 阶乘 *)
Fixpoint factorial (n : nat) :=
  match n with
  | 0%nat => 1%nat
  | S n => ((S n) * factorial n)%nat
  end.

Notation "n !" := (factorial n)(at level 10).

Lemma Lemma6_3_1 : ∀ n, (0 < n!)%nat.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. apply Nat.lt_0_1.
  - simpl. apply Nat.add_pos_l.
    assumption.
Qed.

Lemma Lemma6_3_2 : ∀ n, n! = mult_NM n n.
Proof. 
  intros n. induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn.
    reflexivity.
Qed.


Lemma Lemma6_3_3 : ∀ n, (S n)! = mult_NM (S n) n.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. reflexivity.
  - assert (H0 : ((S (S n)) ! =
      (S (S n)) * (S n)!)%nat).
    { simpl. reflexivity. }
    rewrite H0.
    assert (H1 : (mult_NM (S (S n)) (S n) =
      (S (S n)) * mult_NM (S n) n)%nat).
    { simpl. reflexivity. }
    rewrite H1. rewrite <- IHn.
    reflexivity.
Qed.

Lemma Lemma6_3_4 : ∀ n, (0 < n)%nat -> 0^^n = 0.
Proof.
  intros n H0. destruct n as [|n]. 
  - apply Nat.lt_irrefl in H0. contradiction.
  - simpl. field.
Qed.

Lemma Lemma6_3_5 : ∀ x n, x <> 0 -> x^^n <> 0.
Proof.
  intros x n. induction n as [|n IHn].
  - intros H0. simpl. lra.
  - intros H0. apply IHn in H0 as H1. simpl.
    apply Rmult_integral_contrapositive_currified; auto.
Qed.

Lemma Lemma6_3_6 : ∀ n, (n > 0)%nat -> 
      INR (n !) = INR ((n - 1) ! * n).
Proof.
  intros. induction n as [|n IHn].
  - inversion H. 
  - simpl.
    rewrite plus_INR. rewrite mult_INR. rewrite mult_INR. 
    assert (INR(S n) = INR n + 1). apply S_INR.
    rewrite H0. clear H0.
    assert (INR ((n - 0) !) = INR (n !)).
    cut(n - 0 = n)%nat. intros.
    rewrite H0. auto. apply Nat.sub_0_r.
    rewrite H0. 
    rewrite Rmult_plus_distr_l. 
    lra.
Qed.


Lemma Lemma_6_3_7: ∀(n:nat) (f : Seq) ,(n > 0)%nat  -> 
 Σ f  n = Σ f (n - 1) + f[n].
Proof.
  intros. induction n.
  - inversion H.
  - simpl. 
    rewrite Nat.sub_0_r. auto.
Qed. 


(* 泰勒公式 *)
Theorem Theorem6_9 : ∀ (f : Fun) (n : nat) (x0 : R),
  (0 < n)%nat -> Function f -> x0 ∈ dom[dN f n] ->
    (∃ (o : Fun), InfinitesimalHigherOrder
      o \{\ λ x y, y = (x - x0)^^n \}\ x0 /\
      (∀ (x : R), f[x] =
      (Σ \{\ λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k \}\ n) + o[x])).
Proof.  
  intros f n x0 H0 H1 H2.
  assert (H3 : ∃ Rn, Rn = λ m, \{\ λ x y,
    y = f[x] - (Σ \{\ λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k \}\ m) \}\).
  { exists (λ m, \{\ λ x y, y =
    f[x] - (Σ \{\ λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k \}\ m) \}\).
    reflexivity. }
  destruct H3 as [Rn H3].  
  exists (Rn n). assert (H4 : ∀ m, Function (Rn m)).
  { intros m. rewrite H3. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H5 : ∀ x m, (Rn m)[x] = f[x] -
    (Σ \{\ λ k v, v = (dN f k)[x0] /
    (INR (k!)) * (x - x0)^^k \}\ m)).
  { intros x m. apply f_x; auto.
    rewrite H3. apply AxiomII'.
    reflexivity. }
  assert (H6 : ∀ x x0, Function
    \{\ λ k v, v = (dN f k) [x0]
    / INR (k !) * (x - x0)^^k \}\).
  { intros x x2 x1 y1 z1 I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H7 : ∀ x x0 k,
    \{\ λ k v, v = (dN f k) [x0]
    / INR (k !) * (x - x0)^^k \}\[k]
    = (dN f k) [x0] / INR (k !) * (x - x0)^^k).
  { intros x x1 k.
    apply f_x; try apply H6.
    apply AxiomII'. reflexivity. }
  assert (H8 : ∀ m x, (Rn (S m))[x] =
    (Rn m)[x] - (dN f (S m)) [x0] /
    INR ((S m) !) * (x - x0) ^^ (S m)).
  { intros m x.
    rewrite H5. rewrite H5.
    simpl Σ. rewrite H7.
    field. apply not_0_INR.
    apply not_eq_sym. apply lt_0_neq.
    apply Lemma6_3_1. }
  assert (H9 : ∀ k, x0 ∈ dom[dN (Rn k) n]).
  { intros k. induction k as [|k IHk].
    - rewrite H3. assert (I1 : \{\ λ x y,
        y = f [x] - Σ \{\ λ k v,
        v = (dN f k) [x0] / INR (k !)
        * (x - x0) ^^ k \}\ 0 \}\ =
        \{\ λ x y, y = f[x] - \{\ λ x1 y1,
        y1 = f[x0] \}\[x] \}\).
      { apply AxiomI; intros [x y];
        split; intro I1;
        applyAxiomII' I1; apply AxiomII'.
        - rewrite H7 in I1. simpl in I1.
          rewrite Lemma5_11. simpl.
          rewrite I1. field.
        - simpl. rewrite H7.
          rewrite Lemma5_11 in I1.
          simpl. rewrite I1. field. }
      rewrite I1. clear I1.
      apply AxiomII. exists ((dN f n)[x0] -
        (dN \{\ λ x1 y1, y1 = f[x0] \}\ n)[x0]).
      apply Lemma5_13; auto. apply AxiomII.
      exists 0. rewrite Lemma5_14.
      apply AxiomII'. reflexivity. assumption.
    - assert (I1 : Rn (S k) =
        \{\ λ x y, y = (Rn k)[x] -
        \{\ λ x1 y1, y1 = (dN f (S k)) [x0]
        / INR ((S k) !) * (x1 - x0) ^^ S k
        \}\[x] \}\).
      { apply AxiomI. intros [x y].
        split; intro I1.
        - apply AxiomII'.
          apply f_x in I1; auto.
          rewrite <- I1. rewrite Lemma4'.
          apply H8.
        - apply -> AxiomII' in I1.
          lazy beta in I1.
          rewrite Lemma4' in I1.
          rewrite <- H8 in I1.
          rewrite I1. apply x_fx; auto.
          apply AxiomII. rewrite H3.
          exists (f[x] - Σ \{\ λ k0 v,
            v = (dN f k0) [x0] / INR (k0 !)
            * (x - x0) ^^ k0 \}\ (S k)).
          apply AxiomII'. reflexivity. }
      rewrite I1. clear I1. apply AxiomII.
      exists ((dN (Rn k) n)[x0] - (dN \{\ λ x1 y1,
        y1 = (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ S k\}\ n)[x0]).
      apply Lemma5_13; auto.
      destruct (Nat.le_gt_cases n (S k))
        as [I1 | I1].
      + rewrite Lemma5_7; auto.
        apply AxiomII. exists ((dN f (S k)) [x0]
          / INR ((S k) !) * INR (mult_NM (S k) n)
          * (x0 - x0) ^^ (S k - n)).
        apply AxiomII'. reflexivity.
      + rewrite Lemma5_7'; auto. apply AxiomII.
        exists 0. apply AxiomII'. reflexivity. }
  assert (H10 : ∀ k, Function \{\ λ x y,
      y = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 \}\ k \}\).
  { intros k. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H11 : ∀ k x, \{\ λ x y, y =
    Σ \{\ λ k1 v, v = (dN f k1)[x0] /
    (INR (k1!)) * (x - x0)^^k1 \}\ k \}\ [x]
    = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
    (INR (k1!)) * (x - x0)^^k1 \}\ k).
  { intros k x. apply f_x;
    try apply H10.
    apply AxiomII'. reflexivity. } 
  assert (H12 : ∀ x k m, (k < m)%nat ->
      [x, 0] ∈ (dN (\{\ λ x1 y1,
      y1 = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x1 - x0)^^k1 \}\ k \}\) m)).
  { intros x k m. induction k as [|k IHk].
    - intros I1. simpl.
      assert (I2 : \{\ λ x y, y = \{\ λ k1 v,
        v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 \}\[0%nat] \}\ =
        \{\ λ x y, y = f[x0] \}\).
      { apply AxiomI; intros [x1 y1];
        split; intro J1;
        applyAxiomII' J1; apply AxiomII'.
        - rewrite J1. rewrite H7.
          simpl. field.
        - rewrite H7. simpl. rewrite J1.
          field. }
      rewrite I2. clear I2. 
      rewrite Lemma5_14; [apply AxiomII' | assumption].
      reflexivity.
    - intros I1. assert (I2 : \{\ λ x1 y1,
        y1 = Σ \{\ λ k1 v, v = (dN f k1) [x0]
        / INR (k1 !) * (x1 - x0) ^^ k1 \}\ (S k) \}\
        = \{\ λ x2 y2, y2 = \{\ λ x1 y1,
        y1 = Σ \{\ λ k1 v, v = (dN f k1) [x0]
        / INR (k1 !) * (x1 - x0) ^^ k1 \}\ k \}\[x2]
        + \{\ λ x1 y1, y1 = (dN f (S k)) [x0]
        / INR ((S k) !) * (x1 - x0) ^^ (S k) \}\[x2]
        \}\ ).
      { apply AxiomI; intros [x1 y1];
        split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H11. rewrite Lemma4'.
          rewrite H7 in J1. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7. rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I2. clear I2. assert (I2 : (k < m)%nat).
      { apply Nat.lt_succ_l; assumption. }
      apply IHk in I2 as I3.
      assert (I4 : (0 < m)%nat).
      { apply (Nat.lt_lt_0 k). assumption. }
      apply f_x in I3 as I5; try apply Lemma5_15; auto.
      assert (I6 : (dN \{\ λ x1 y1, y1 =
        (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ (S k) \}\ m)[x] = 0).
      { apply f_x.
        - apply Lemma5_15; assumption.
        - rewrite Lemma5_7'; auto.
          apply AxiomII'. reflexivity. }
      assert (I7 : 0 = (dN \{\ λ x2 y2,
      y2 = Σ \{\ λ k1 v, v = (dN f k1) [x0]
      / INR (k1 !) * (x2 - x0) ^^ k1 \}\
      k \}\ m) [x] + (dN \{\ λ x1 y1, y1 =
        (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ (S k) \}\ m)[x]).
      { rewrite I5. rewrite I6. field. }
      rewrite I7. apply Lemma5_13'.
      + apply AxiomII. exists 0.
        assumption.
      + apply AxiomII. exists 0.
        rewrite Lemma5_7'; auto.
        apply AxiomII'. reflexivity. }
  assert (H13 : ∀ x k, [x, (dN f k)[x0]] ∈
      (dN (\{\ λ x y,
      y = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 \}\ k \}\) k)).
  { intros x k. destruct k as [|k].
    - simpl. apply AxiomII'.
      rewrite H7. simpl. field.
    - assert (I1 : \{\ λ x y, y = Σ \{\ λ k1 v,
        v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 \}\ (S k) \}\ =
        \{\ λ x y, y = \{\ λ x1 y1, y1 =
          Σ \{\ λ k1 v,
          v = (dN f k1) [x0] / INR (k1 !)
          * (x1 - x0) ^^ k1 \}\ k \}\[x] +
        \{\ λ x1 y1, y1 = (dN f (S k)) [x0]
          / INR ((S k) !) * (x1 - x0) ^^ (S k) \}\[x]
        \}\).
      { apply AxiomI. intros [x1 y1].
        split; intros J1.
        - applyAxiomII' J1. apply AxiomII'.
          rewrite H11. rewrite Lemma4'.
          rewrite H7 in J1. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7. rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I1. clear I1.
      assert (I1 : (k < S k)%nat).
      { apply Nat.lt_succ_diag_r. }
      apply (H12 x) in I1.
      assert (I2 : [x, (dN f (S k)) [x0]]
          ∈ dN \{\ λ x y, y = (dN f (S k)) [x0]
          / INR ((S k) !) * (x - x0) ^^ (S k)
          \}\ (S k)).
      { rewrite Lemma5_7; try apply le_n.
        apply AxiomII'. rewrite <- Lemma6_3_2.
        rewrite Nat.sub_diag. simpl pow.
        field. apply not_0_INR.
        apply not_eq_sym. apply lt_0_neq.
        apply Lemma6_3_1. }
      assert (I3 : (dN f (S k)) [x0] = (dN \{\ λ x y,y =
        Σ \{\ λ k1 v, v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 \}\ k \}\ (S k))[x] + 
        (dN \{\ λ x y, y = (dN f (S k)) [x0]
        / INR ((S k) !) * (x - x0) ^^ S k \}\
        (S k))[x]).
      { generalize (Nat.lt_0_succ k). intros J1.
        apply f_x in I1; try apply Lemma5_15; auto.
        apply f_x in I2; try apply Lemma5_15; auto.
        rewrite I1; rewrite I2. field. }
      pattern ((dN f (S k)) [x0]) at 1.
      rewrite I3. apply Lemma5_13'.
      + apply AxiomII. exists 0. assumption.
      + apply AxiomII. exists ((dN f (S k)) [x0]).
        assumption. }
  assert (H14 : ∀ k, (k <= n)%nat ->
    [x0, 0] ∈ (dN (Rn k) k)).
  { intros k I0. assert (I1 : Rn k = \{\ λ x y,
      y = f[x] - \{\ λ x1 y1, y1 = Σ \{\ λ k1 v,
      v = (dN f k1) [x0] / INR (k1 !) *
      (x1 - x0) ^^ k1 \}\ k \}\[x] \}\).
    { rewrite H3. apply AxiomI;
      intros [x y]; split; intro J1;
      applyAxiomII' J1; apply AxiomII'.
      - rewrite H11. assumption.
      - rewrite H11 in J1. assumption. }
    rewrite I1. clear I1.
    assert (I1 : x0 ∈ dom[ dN f k]).
    { apply le_lt_or_eq in I0 as [I0 | I0].
      - apply Lemma5_6 with (k := k)
          in H2 as J1; auto.
        destruct J1 as [δ [J1 J2]].
        apply J2. apply AxiomII.
        apply Abs_R; lra.
      - rewrite I0; assumption. }
    assert (I2 : Function (dN f k)).
    { apply Lemma5_16. assumption. }
    apply x_fx in I1 as I3; auto.
    generalize (H13 x0 k); intros I4.
    assert (I5 : 0 = (dN f k)[x0] -
      (dN \{\ λ x1 y1, y1 = Σ \{\ λ k1 v,
      v = (dN f k1) [x0] / INR (k1 !) *
      (x1 - x0) ^^ k1 \}\ k \}\ k)[x0]).
    { apply f_x in I4.
      - rewrite I4. field.
      - apply Lemma5_16. auto. }
    rewrite I5. apply Lemma5_13; auto.
    apply AxiomII. exists ((dN f k) [x0]).
    assumption. }
  assert (H15 : ∀ k, (k <= n)%nat ->
    [x0, 0] ∈ (dN (Rn n) k)).
  { clear H0.
    induction n as [|n IHn].
    - intros k I1. apply le_n_0_eq in I1.
      rewrite <- I1. simpl. rewrite H3.
      apply AxiomII'. simpl. rewrite H7.
      simpl. field.
    - intros k I1. assert (I2 : x0 ∈ dom[ dN f n]).
      { apply Lemma5_6 with (k := n) in H2 as J1.
        destruct J1 as [δ [J1 J2]]. apply J2.
        - apply AxiomII. apply Abs_R. lra.
        - apply Nat.lt_succ_diag_r. }
      assert (I3 : ∀k : nat,x0 ∈ dom[ dN (Rn k) n]).
      { intros m. generalize (H9 m); intros J1.
        apply Lemma5_6 with (k := n) in J1 as J2.
        destruct J2 as [δ [J2 J3]].
        - apply J3. apply AxiomII.
          apply Abs_R. lra.
        - apply Nat.lt_succ_diag_r. }
      assert (I4 : (∀ k, (k <= n)%nat ->
        [x0, 0] ∈ dN (Rn k) k)).
      { intros k0 J1. apply H14.
        apply le_S. assumption. }
      generalize (IHn I2 I3 I4); intros I5.
      apply Nat.le_succ_r in I1 as [I1 | I1].
      + generalize (I5 k I1); intros I6.
        assert (I7 : Rn (S n) = \{\ λ x y, y =
          (Rn n)[x] - \{\ λ x1 y1, y1 =
          (dN f (S n)) [x0] / INR ((S n) !)
          * (x1 - x0) ^^ S n \}\[x] \}\).
        { apply AxiomI; intros [x y];
          split; intro J1.
          - apply AxiomII'.
            apply f_x in J1; try apply H4.
            rewrite <- J1. rewrite Lemma4'.
            apply H8.
          - apply -> AxiomII' in J1.
            lazy beta in J1. rewrite Lemma4' in J1.
            rewrite <- H8 in J1.
            rewrite J1. apply x_fx; auto.
            apply AxiomII. rewrite H3.
            exists (f[x] - Σ \{\ λ k0 v, v =
              (dN f k0) [x0] / INR (k0 !) *
              (x - x0) ^^ k0 \}\ (S n)).
            apply AxiomII'. reflexivity. }
        rewrite I7. clear I7.
        assert (I7 : [x0, 0] ∈ dN \{\ λ x y, y =
          (dN f (S n)) [x0] / INR ((S n) !)
          * (x - x0) ^^ S n\}\ k).
        { rewrite Lemma5_7;
          try apply le_S; auto.
          apply AxiomII'.
          assert (I7 : x0 - x0 = 0). lra.
          rewrite I7. clear I7.
          assert (I8 : ∀ m, (0 < m)%nat -> 0^^m = 0).
          { intros m. induction m as [|m IHm].
            - intros J1. apply Nat.lt_irrefl in J1.
              contradiction.
            - intros J1. apply lt_n_Sm_le in J1 as J2.
              apply le_lt_or_eq in J2 as [J2 | J2].
              + apply IHm in J2. simpl. field.
              + rewrite <- J2. simpl. field. }
          assert (I9 : (0 < S n - k)%nat).
          { apply ArithProp.lt_minus_O_lt.
            apply le_lt_n_Sm. assumption. }
          rewrite I8; auto. field. apply not_0_INR.
          apply not_eq_sym. apply lt_0_neq.
          apply Lemma6_3_1. }
        assert (I8 : 0 = 0 - 0). lra.
        rewrite I8. apply Lemma5_18; auto.
        apply Lemma3'.
      + rewrite I1. apply H14.
        apply le_n. }
  assert (H16 : ∀ k, (S k - k = 1)%nat).
  { intros k. rewrite Nat.sub_succ_l.
    - rewrite Nat.sub_diag.
      reflexivity.
    - apply le_n. }
  assert (H17 : ∀ x k, (0 < k)%nat ->
    [x, (dN f (k-1))[x0] + (dN f k)[x0] * (x-x0)]
      ∈ (dN \{\ λ x y,
      y = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 \}\ k \}\ (k-1))).
  { intros x k I1. destruct k as [|k].
    - apply Nat.lt_irrefl in I1.
      contradiction.
    - simpl minus. rewrite Nat.sub_0_r.
      assert (I2 : \{\ λ x y,
        y = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
        (INR (k1!)) * (x - x0)^^k1 \}\ (S k) \}\ =
        \{\ λ x y, y = \{\ λ x1 y1,
        y1 = Σ \{\ λ k1 v, v = (dN f k1)[x0] /
        (INR (k1!)) * (x1 - x0)^^k1 \}\ k \}\[x]
        + \{\ λ x1 y1, y1 = (dN f (S k))[x0] /
        (INR ((S k)!)) * (x1 - x0)^^(S k) \}\[x] \}\).
      { apply AxiomI; intros [x1 y1];
        split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H7 in J1. rewrite H11.
          rewrite Lemma4'. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7.
          rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I2. clear I2.
      generalize (H13 x k); intros I2.
      assert (I3 : [x, (dN f (S k))[x0] * (x - x0)]
        ∈ dN \{\ λ x y, y = (dN f (S k))[x0] /
        (INR ((S k)!)) * (x - x0)^^(S k) \}\ k).
      { rewrite Lemma5_7;
        try apply (Nat.le_succ_diag_r k).
        apply AxiomII'.
        rewrite H16. rewrite <- Lemma6_3_3.
        simpl pow. field. apply not_0_INR.
        apply not_eq_sym.
        apply lt_0_neq. apply Lemma6_3_1. }
      apply Lemma5_18'; auto. apply Lemma3'. }
  assert (H18 : ∃ δ, 0 < δ /\ (∀ x, x ∈ Neighbor x0 δ
    -> (dN (Rn n) (n-1))[x] = (dN f (n-1))[x] -
    (dN f (n-1))[x0] - (dN f n)[x0] * (x - x0))).
  { generalize (Lemma5_6' f x0 n H2).
    intros [δ [I1 I2]].
    exists δ. split; [apply I1 | intros x I3].
    destruct n as [|n].
    - apply Nat.lt_irrefl in H0.
      contradiction.
    - simpl minus. rewrite Nat.sub_0_r.
      assert (I4 : [x, (dN f n)[x]] ∈
        dN f n).
      { apply x_fx.
        - apply Lemma5_16. assumption.
        - apply I2; auto. }
      generalize (H17 x (S n) H0).
      intros I5. simpl minus in I5.
      rewrite Nat.sub_0_r in I5.
      assert (I6 : Rn (S n) = \{\ λ x y,
        y = f[x] - \{\ λ x1 y1, y1 = Σ \{\ λ k v,
        v = (dN f k) [x0] / INR (k !) *
        (x1 - x0) ^^ k \}\ (S n) \}\[x] \}\).
      { rewrite H3. apply AxiomI;
        intros [x1 y1]; split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H11. assumption.
        - apply -> AxiomII' in J1;
          lazy beta in J1.
          apply AxiomII'. rewrite H11 in J1.
          assumption. }
      apply f_x.
      + apply Lemma5_16. apply H4.
      + assert (J1 : (dN f n)[x] - (dN f n)[x0]
          - (dN f (S n))[x0] * (x - x0) =
          (dN f n)[x] - ((dN f n)[x0]
          + (dN f (S n))[x0] * (x - x0))).
        field. rewrite J1. rewrite I6.
        apply Lemma5_18; auto. }
  destruct H18 as [δ1 [H18 H19]].
  assert (H20 : ∀ k, (k < n-1)%nat ->
    limit (dN (Rn n) k) x0 0 /\
    limit (dN \{\ λ x y, y = (x - x0)^^n \}\ k) x0 0).
  { intros k I1.
    assert (I2 : (S k <= n)%nat).
    { destruct n as [|n].
      - simpl in I1. apply Nat.nlt_0_r in I1.
        contradiction.
      - simpl in I1. rewrite Nat.sub_0_r in I1.
        apply Peano.le_n_S.
        apply Nat.lt_le_incl.
        assumption. }
    apply le_Sn_le in I2 as I3.
    split.
    - apply H15 in I2 as I4.
      simpl in I4. applyAxiomII' I4.
      assert (I5 : derivable (dN (Rn n) k) x0).
      { exists 0. assumption. }
      apply Theorem5_1 in I5 as [I6 I7].
      apply H15 in I3 as I8.
      apply f_x in I8.
      + rewrite I8 in I7. assumption.
      + apply Lemma5_16. auto.
    - rewrite Lemma5_7_1; auto.
      generalize (Lemma7' x0 (INR (mult_NM n k))
        x0 (n - k)).
      intros I4.
      assert (I5 : (INR (mult_NM n k) *
        (x0 - x0) ^^ (n - k)) = 0).
      { assert (J1 : x0 - x0 = 0). lra.
        rewrite J1. assert (J2 : (0 < n - k)%nat).
        { apply ArithProp.lt_minus_O_lt.
          apply le_S_gt. assumption. }
        rewrite Lemma6_3_4; auto.
        field. }
      rewrite I5 in I4.
      assumption. }
  assert (H21 : ∀ k, (0 < k <= n-1)%nat ->
    (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂
    dom[dN (Rn n) k] /\ Neighbor0 x0 δ' ⊂
    dom[dN \{\ λ x y, y = (x - x0)^^n \}\ k] /\
    (∀ x, x ∈ Neighbor0 x0 δ' ->
    (dN \{\ λ x y, y = (x - x0)^^n \}\ k)[x] <> 0))).
  { intros k I1. assert (I2 : (k < n)%nat).
    { destruct n as [|n].
      - apply Nat.lt_irrefl in H0.
        contradiction.
      - simpl in I1. rewrite Nat.sub_0_r in I1.
        apply le_lt_n_Sm. apply I1. }
    generalize (Lemma5_6 (Rn n) x0 n (H9 n) k I2).
    intros [δ [I3 I4]]. exists δ.
    apply Nat.lt_le_incl in I2 as I5.
    repeat split; auto.
    - intros x J1. apply I4.
      applyAxiomII J1. apply AxiomII.
      apply J1.
    - rewrite Lemma5_7_1; auto.
      intros x J1. apply AxiomII.
      exists (INR (mult_NM n k) *
        (x - x0) ^^ (n - k)).
      apply AxiomII'. reflexivity.
    - intros x J1. rewrite Lemma5_7_1; auto.
      rewrite Lemma4'.
      apply Rmult_integral_contrapositive_currified.
      + apply not_0_INR. apply mult_NM_ne_0.
      + apply Lemma6_3_5. applyAxiomII J1.
        apply Lemma2 in J1. apply J1. }
  assert (H22 : limit \{\ λ x y, y = (dN (Rn n) (n-1))[x]
    / (dN \{\ λ x y, y = (x - x0)^^n \}\ (n-1))[x] \}\ x0 0).
  { assert (I1 : (n - 1 <= n)%nat).
    { destruct n as [|n].
      - simpl. apply le_n.
      - simpl. rewrite Nat.sub_0_r.
        apply Nat.le_succ_diag_r. }
    rewrite Lemma5_7_1; auto.
    assert (I2 : \{\ λ x y, y = (dN (Rn n) (n - 1)) [x]
      / \{\ λ x1 y0, y0 = INR (mult_NM n (n - 1)) *
      (x1 - x0) ^^ (n - (n - 1))\}\ [x] \}\ =
      \{\ λ x y, y = (dN (Rn n) (n - 1)) [x] /
        (INR (n!) * (x - x0)) \}\).
    { assert (K1 :(n - (n - 1) = 1)%nat /\
          (mult_NM n (n - 1) = n!)%nat).
      { destruct n as [|n].
        - apply Nat.lt_irrefl in H0.
          contradiction.
        - assert (L1 : (S n - 1 = n)%nat).
          { simpl. apply Nat.sub_0_r. }
          split.
          + rewrite L1. apply H16.
          + rewrite L1. rewrite Lemma6_3_3.
            reflexivity. }
      destruct K1 as [K1 K2].
      apply AxiomI; intros [x y];
      split; intro J1;
      applyAxiomII' J1; apply AxiomII'.
      - rewrite Lemma4' in J1.
        rewrite K1 in J1.
        rewrite K2 in J1.
        simpl in J1.
        assert (K3 : (x - x0) * 1 = x - x0).
        field. rewrite K3 in J1.
        assumption.
      - rewrite K1; rewrite K2.
        rewrite Lemma4'. simpl.
        assert (K3 : (x - x0) * 1 = x - x0).
        field. rewrite K3.
        assumption. }
    rewrite I2. clear I2.
    assert (I2 : Function \{\ λ x y, y =
      (dN (Rn n) (n - 1)) [x] /
      (INR (n!) * (x - x0)) \}\).
    { intros x y z J1 J2.
      applyAxiomII' J1; applyAxiomII' J2.
      rewrite J2; assumption. }
    split; auto.
    assert (I3 : (n = S (n - 1))%nat).
    { destruct n as [|n].
      - apply Nat.lt_irrefl in H0.
        contradiction.
      - assert (J1 : (S n - 1 = n)%nat).
        { simpl. apply Nat.sub_0_r. }
        rewrite J1. reflexivity. }
    assert (I4 : Function (dN f n)).
    { apply Lemma5_16; assumption. }
    apply x_fx in H2; auto.
    pattern n at 2 in H2.
    rewrite I3 in H2. simpl dN in H2.
    apply -> AxiomII' in H2.
    lazy beta in H2. unfold derivative in H2.
    destruct H2 as [I5 [[δ1' [I6 I7]] I8]].
    unfold limit in I8.
    destruct I8 as [I8 [δ' [I9 [I10 I11]]]].
    exists δ'. split; [assumption | split].
    - intros x J1. apply AxiomII.
      exists ((dN (Rn n) (n - 1)) [x] /
        (INR (n !) * (x - x0))).
      apply AxiomII'. reflexivity.
    - intros ε J1. generalize (I11 ε J1).
      intros [δ2 [[J2 J3] J4]].
      generalize (Lemma1 δ1 δ2 H18 J2).
      intros [δ [J5 [J6 J7]]].
      exists δ. split; [lra | intros x J8].
      assert (J9 :∀ x, \{\ λ x1 y, y =
        (dN (Rn n) (n - 1)) [x1] /
        (INR (n !) * (x1 - x0))\}\ [x] =
        (dN (Rn n) (n - 1)) [x] /
        (INR (n !) * (x - x0))).
      { intros t. apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite J9.
      assert (J10 : x ∈ Neighbor x0 δ1).
      { apply AxiomII. lra. }
      assert (J11 : 0 < Abs [x - x0] < δ2). lra.
      generalize (H19 x J10).
      intros J12. rewrite J12.
      generalize (J4 x J11).
      intros J13.
      assert (J14 : \{\ λ x y, y =
        ((dN f (n - 1)) [x] - (dN f (n - 1)) [x0])
        / (x - x0) \}\ [x] =
        ((dN f (n - 1)) [x] - (dN f (n - 1)) [x0])
        / (x - x0)).
      { apply f_x.
        - intros x1 y1 z1 K1 K2.
          applyAxiomII' K1; applyAxiomII' K2.
          rewrite K2; assumption.
        - apply AxiomII'. reflexivity. }
      rewrite J14 in J13. clear J14.
      assert (J14 : ∀ k,  1 <= INR (k!)).
      { intros k. assert (K1 : 1 = INR 1%nat).
        { simpl. reflexivity. }
        rewrite K1. apply le_INR.
        induction k as [|k IHk].
        - simpl. apply le_n.
        - simpl. apply le_plus_trans.
          assumption. }
      assert (J15 : 0 < INR (n !)).
      { apply lt_0_INR. apply Lemma6_3_1. }
      assert (J16 : INR (n !) <> 0).
      { apply not_eq_sym.
        apply Rlt_not_eq. auto. }
      assert (J17 : ((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0] - (dN f n) [x0]
        * (x - x0)) / (INR (n !) * (x - x0))
        - 0 = (((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0)
        - (dN f n) [x0]) / (INR (n !))).
      { field. split; auto.
        - apply Lemma2 in J8. apply J8. }
      rewrite J17. clear J17.
      rewrite Abs_div; auto.
      rewrite (Abs_gt (INR (n!))); auto.
      apply Rmult_lt_reg_r with (r := INR (n !)); auto.
      assert (J17 : Abs [((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0) -
        (dN f n) [x0]] / INR (n !) * INR (n !) =
        Abs [((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0) -
        (dN f n) [x0]]).
      { field. assumption. }
      rewrite J17. clear J17.
      assert (J17 : ε <= ε * INR (n !)).
      { pattern ε at 1. rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; auto. lra. }
      lra. }
  generalize (Lemma6_1 (Rn n) \{\ λ x y,
    y = (x - x0)^^n \}\ x0 0 (n-1) H20 H21 H22).
  intros H23. split.
  - unfold InfinitesimalHigherOrder.
    split; [auto | split];
    [apply Lemma3 | split]; auto.
    exists 1. split; [lra | repeat split].
    + intros x I1. rewrite H3. apply AxiomII.
      exists (f[x] - Σ \{\ λ k v, v =
        (dN f k)[x0] / INR (k !)
        * (x - x0) ^^ k\}\ n).
      apply AxiomII'. reflexivity.
    + intros x I1. apply AxiomII.
      exists ((x - x0) ^^ n).
      apply AxiomII'. reflexivity.
    + intros x I1. rewrite Lemma4.
      apply Lemma6_3_5. applyAxiomII I1.
      apply Lemma2 in I1.
      apply I1.
  - intros x. rewrite H5.
    field.
Qed.




(* Lemma Lemma5_7' : ∀ a c n k, (k <= n)%nat ->
  (dN (\{\ λ x y, y = c*(a-x)^^n \}\) k) =
  \{\ λ x y, y = c * (INR (mult_NM n k))
    * -1 * (a-x)^^(n-k) \}\.
Proof.
  intros a c n k H0. 
  assert (\{\ λ x y, y = c*(a-x)^^n \}\ = 
          \{\ λ x y, y = c*((-1)^^n) * ((x-a)^^n) \}\).
  { apply AxiomI. split; intros.
    - applyAxiomII H. destruct H as [x0[y0[H H']]].
      apply AxiomII. exists x0,y0. split; auto.
      rewrite H'. 
      cut ((-1) ^^ n * (x0 - a) ^^ n = (a - x0) ^^ n).
      intros. rewrite <- H1. auto.
      rewrite Rmult_assoc. auto.
      rewrite (Lemma_pow4 (-1) (x0 - a) n).
      cut ((-1 * (x0 - a)) = (a - x0)). intros. rewrite H1.
      auto. lra.
    - applyAxiomII H. destruct H as [x0[y0[H H']]].
      apply AxiomII. exists x0,y0. split; auto.
      rewrite H'.
      cut ((-1) ^^ n * (x0 - a) ^^ n = (a - x0) ^^ n).
      intros. rewrite <- H1.
      rewrite Rmult_assoc. auto.
      rewrite (Lemma_pow4 (-1) (x0 - a) n).
      cut ((-1 * (x0 - a)) = (a - x0)). intros. rewrite H1.
      auto. lra. }
  rewrite H. clear H.
  assert (dN \{\ λ x y,y = c * (-1) ^^ n * (x - a) ^^ n \}\ k
   = \{\ λ x y, y = c * (-1) ^^ n * (INR (mult_NM n k))
    * (x-a)^^(n-k) \}\).
  apply Lemma5_7; auto.
  assert (\{\λ x y, y = c * (-1) ^^ n * INR (mult_NM n k) * 
             (x - a) ^^ (n - k) \}\ = 
         \{\ λ x y, y = c * INR (mult_NM n k) * -1 * 
         (a - x) ^^ (n - k) \}\).
  

Admitted.  *)

Theorem Theorem4_4_0 : ∀(f : Fun) (x x1: R),
  Continuous \{\ λ t y : R,y = f [x] \}\ x1.
Proof.
(*   assert (derivative \{\ λ t y : R,y = f [x] \}\). *)
  intros. red. split.
  - apply AxiomII. exists f[x]. apply AxiomII'. auto.
  - assert (\{\ λ t y : R,y = f [x] \}\ [x1] = f[x]).
    apply f_x. red. intros. applyAxiomII' H.
    applyAxiomII' H0. rewrite H. auto. apply AxiomII'. auto.
    rewrite H. apply Lemma5_19.
Qed.

Lemma Lemma6_10 : ∀(f : Fun) (x0: R), Continuous f x0 ->
    Continuous \{\ λ t y, y = f [t] \}\ x0.
Proof.
  intros. red in H. destruct H. red in H0.
  destruct H0 as [H0[δ'[H0'[H0'' H0''']]]].
  red. split. apply AxiomII. exists f[x0]. 
  apply AxiomII'. auto. red. split.
  QED_function. exists δ'. split; auto.
  split. red. intros. apply AxiomII. exists f[z].
  apply AxiomII'. auto. intros. apply H0''' in H1. 
  destruct H1 as [δ''[H1 H1']]. exists δ''. split; auto.
  intros. apply H1' in H2.
  assert (\{\ λ t y, y = f [t] \}\ [x] = f[x]).
  Function_ass.
  assert (\{\ λ t y, y = f [t] \}\ [x0] = f[x0]).
  Function_ass.
  rewrite H3, H4. auto. 
Qed. 

Lemma Lemma6_10_1: ∀(f : Fun) (b x: R), ContinuousLeft f b ->
      ContinuousLeft \{\ λ t y, y = f [x] - f [t] \}\ b.
Proof.
  intros. red in H. destruct H. red in H0. 
  destruct H0 as [H0 [δ'[H0'[H0'' H0''']]]].
  red. split.
  - apply AxiomII. exists (f [x] - f [b]). apply AxiomII'.
    auto.
  - red. split. QED_function. exists δ'. split; auto.
    split. red. intros. apply AxiomII. exists ( f [x] - f [z]).
    apply AxiomII'. auto.
    intros. apply H0''' in H1. destruct H1 as [δ'' [H1 H1']].
    exists δ''. split; auto. intros. apply H1' in H2.
    assert (\{\ λ t y, y = f [x] - f [t] \}\ [x0] = 
                       f [x] - f [x0]).
    { Function_ass. }
    assert (\{\ λ t y, y = f [x] - f [t] \}\ [b] = 
                       f [x] - f [b]).
    { Function_ass. }
    rewrite H3. rewrite H4.
    cut (f [b] - f [x0] = f [x] - f [x0] - (f [x] - f [b])).
    intros. rewrite <- H5.
    rewrite Abs_eq_neg. 
    cut (f [x0] - f [b] = - (f [b] - f [x0])). intros. 
    rewrite <- H6. auto. lra. lra.
Qed.

Lemma Lemma6_10_2: ∀(f : Fun) (a x: R), ContinuousRight f a ->
      ContinuousRight \{\ λ t y, y = f [x] - f [t] \}\ a.
Proof.
  intros. red in H. destruct H. red in H0. 
  destruct H0 as [H0 [δ'[H0'[H0'' H0''']]]].
  red. split.
  - apply AxiomII. exists (f [x] - f [a]). apply AxiomII'.
    auto.
  - red. split. QED_function. exists δ'. split; auto.
    split. red. intros. apply AxiomII. exists ( f [x] - f [z]).
    apply AxiomII'. auto.
    intros. apply H0''' in H1. destruct H1 as [δ'' [H1 H1']].
    exists δ''. split; auto. intros. apply H1' in H2.
    assert (\{\ λ t y, y = f [x] - f [t] \}\ [x0] = 
                       f [x] - f [x0]).
    { Function_ass. }
    assert (\{\ λ t y, y = f [x] - f [t] \}\ [a] = 
                       f [x] - f [a]).
    { Function_ass. }
    rewrite H3. rewrite H4. 
    cut (f [a] - f [x0] = f [x] - f [x0] - (f [x] - f [a])).
    intros. rewrite <- H5.
    rewrite Abs_eq_neg. 
    cut (f [x0] - f [a] = - (f [a] - f [x0])). intros. 
    rewrite <- H6. auto. lra. lra.
Qed.

Lemma Lemma6_10_3 : ∀(f : Fun) (a b x0 x: R),
    a < b -> ContinuousClose f a b -> 
    x0 ∈ \[a, b\] -> x ∈ \[a, b\] -> x0 < x ->
    ContinuousClose \{\ λ t y, y = f [x] - f [t] \}\ x0 x.
Proof.
  intros. red in H0. destruct H0 as [H0[H0' H0'']].
  applyAxiomII H1. applyAxiomII H2. destruct H1 as [H1 H1'].
  destruct H2 as [H2 H2'].
  assert (Q1 :\{\ λ t y, y = f [x] - f [t] \}\ =
                \{\ λ t y, y = f [x] \}\ \- 
                \{\ λ t y, y =f [t] \}\).
  { apply AxiomI. split; intros. applyAxiomII H4.
    destruct H4 as [x0'[y0'[H4 H4']]].
    apply AxiomII. exists x0',y0'. split; auto. split. 
    apply AxiomII. exists f [x]. apply AxiomII'.
    auto. split. apply AxiomII. exists f[x0']. 
    apply AxiomII'. auto.
    assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
    apply f_x. red. intros. applyAxiomII' H5.
    applyAxiomII' H6. rewrite H5; auto.
    apply AxiomII'. auto. rewrite H5. clear H5.
    assert (\{\ λ t y, y = f [t] \}\ [x0'] = f [x0']).
    apply f_x. red. intros. applyAxiomII' H5.
    applyAxiomII' H6. rewrite H5; auto.
    apply AxiomII'. auto. rewrite H5. clear H5.
    auto.
    applyAxiomII H4. 
    destruct H4 as [x0'[y0'[H4[H4'[H4'' H4''']]]]].
    assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
    apply f_x. red. intros. applyAxiomII' H5.
    applyAxiomII' H6. rewrite H5; auto.
    apply AxiomII'. auto. rewrite H5 in H4'''. clear H5.
    assert (\{\ λ t y, y = f [t] \}\ [x0'] = f [x0']).
    apply f_x. red. intros. applyAxiomII' H5.
    applyAxiomII' H6. rewrite H5; auto.
    apply AxiomII'. auto. rewrite H5 in H4'''.
    clear H5. apply AxiomII. exists x0',y0'. auto. }  
   destruct H1, H1', H2, H2'. 
  - red in H0. red. split.
    + red. intros. cut (a < x1 < b). intros.
      apply H0 in H7. rewrite Q1.
      apply Theorem4_4_2. apply Theorem4_4_0.
      apply Lemma6_10; auto. 
      intros. apply f_x.
      red. intros. applyAxiomII' H9. applyAxiomII' H10. 
      destruct H9 as [H9[H9' H9'']].
      destruct H10 as [H10[H10' H10'']].
      rewrite H9''. auto. apply AxiomII'.
      applyAxiomII H8. split. tauto. split. tauto. auto.
      lra.
    + split. 
      assert (Continuous \{\ λ t y, y = f [x] - f [t] \}\ x0).
      { rewrite Q1. apply Theorem4_4_2. apply Theorem4_4_0. 
        assert (a < x0 < b). auto. apply H0 in H6. 
        apply Lemma6_10. auto.
        intros. apply f_x.
        red. intros. applyAxiomII' H7. applyAxiomII' H8. 
        destruct H7 as [H7[H7' H7'']].
        destruct H8 as [H8[H8' H8'']].
        rewrite H8''. auto. apply AxiomII'.
        applyAxiomII H6. split. tauto. split. tauto. auto. }
        apply Theorem4_1 in H6. tauto.
        assert (Continuous \{\ λ t y, y = f [x] - f [t] \}\ x).
        { rewrite Q1. apply Theorem4_4_2. apply Theorem4_4_0. 
          assert (a < x < b). auto. apply H0 in H6. 
          apply Lemma6_10. auto.
          intros. apply f_x.
          red. intros. applyAxiomII' H7. applyAxiomII' H8. 
          destruct H7 as [H7[H7' H7'']].
          destruct H8 as [H8[H8' H8'']].
          rewrite H8''. auto. apply AxiomII'.
          applyAxiomII H6. split. tauto. split. tauto. auto. }
          apply Theorem4_1 in H6. tauto.
  - rewrite H5.
    red. split.
    + rewrite <- H5. red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. rewrite Q1.
      apply Theorem4_4_2. apply Theorem4_4_0.
      apply Lemma6_10; auto. 
      intros. apply f_x.
      red. intros. applyAxiomII' H9. applyAxiomII' H10. 
      destruct H9 as [H9[H9' H9'']].
      destruct H10 as [H10[H10' H10'']].
      rewrite H9''. auto. apply AxiomII'.
      applyAxiomII H8. split. tauto. split. tauto. auto. 
    + split. rewrite <- H5.
      assert (Continuous \{\ λ t y, y = f [x] - f [t] \}\ x0).
      { rewrite Q1. apply Theorem4_4_2. apply Theorem4_4_0. 
        assert (a < x0 < b). auto. apply H0 in H6. 
        apply Lemma6_10. auto.
        intros. apply f_x.
        red. intros. applyAxiomII' H7. applyAxiomII' H8. 
        destruct H7 as [H7[H7' H7'']].
        destruct H8 as [H8[H8' H8'']].
        rewrite H8''. auto. apply AxiomII'.
        applyAxiomII H6. split. tauto. split. tauto. auto. }
        apply Theorem4_1 in H6. tauto.
        apply Lemma6_10_1. auto.
  - rewrite <- H2 in H1. lra.
  - rewrite H2 in H5. lra.
  - rewrite <- H4 in H5. lra.
  - rewrite <- H4 in H5. lra.
  - rewrite <- H2 in H1. lra.
  - rewrite <- H4 in H5. lra.
  - red. split.
    + red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. rewrite Q1.
      apply Theorem4_4_2. apply Theorem4_4_0.
      apply Lemma6_10; auto. 
      intros. apply f_x.
      red. intros. applyAxiomII' H9. applyAxiomII' H10. 
      destruct H9 as [H9[H9' H9'']].
      destruct H10 as [H10[H10' H10'']].
      rewrite H9''. auto. apply AxiomII'.
      applyAxiomII H8. split. tauto. split. tauto. auto. 
    + split. rewrite H1.  
      apply Lemma6_10_2. auto.
      assert (Continuous \{\ λ t y, y = f [x] - f [t] \}\ x).
      { rewrite Q1. apply Theorem4_4_2. apply Theorem4_4_0. 
        assert (a < x < b). auto. apply H0 in H6. 
        apply Lemma6_10. auto.
        intros. apply f_x.
        red. intros. applyAxiomII' H7. applyAxiomII' H8. 
        destruct H7 as [H7[H7' H7'']].
        destruct H8 as [H8[H8' H8'']].
        rewrite H8''. auto. apply AxiomII'.
        applyAxiomII H6. split. tauto. split. tauto. auto. }
        apply Theorem4_1 in H6. tauto.
  - red. split. 
    + red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. rewrite Q1.
      apply Theorem4_4_2. apply Theorem4_4_0.
      apply Lemma6_10; auto. 
      intros. apply f_x.
      red. intros. applyAxiomII' H9. applyAxiomII' H10. 
      destruct H9 as [H9[H9' H9'']].
      destruct H10 as [H10[H10' H10'']].
      rewrite H9''. auto. apply AxiomII'.
      applyAxiomII H8. split. tauto. split. tauto. auto. 
    + split. rewrite H1.  
      apply Lemma6_10_2. auto.
      rewrite H5. apply Lemma6_10_1. auto.
  - rewrite <- H1 in H2. lra.
  - rewrite <- H1 in H2. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
Qed.

Lemma Lemma6_10_4 : ∀(f g: Fun) (x0 x: R), 
    ContinuousClose f x0 x -> ContinuousClose g x0 x ->
    ContinuousClose (f \- g) x0 x.
Proof.
  intros. red in H. destruct H as [H [H' H'']].
  red in H0. destruct H0 as [H0 [H0' H0'']].
  red. split.  
  - red. intros. apply Theorem4_4_2. pose proof H1 as H1'.
    red in H. apply H in H1. red in H0. apply H0 in H1'.
    auto. auto. intros. apply f_x. red. intros.
    applyAxiomII' H3. applyAxiomII' H4.
    destruct H3 as [H3[H3' H3'']].
    destruct H4 as [H4[H4' H4'']].
    rewrite H3''. auto.
    apply AxiomII'. applyAxiomII H2. tauto.
  - split. red. red in H'. destruct H' as [H1 H1'].
    red in H0'. destruct H0' as [H2 H2'].
    split. apply AxiomII. exists (f [x0] - g [x0]). 
    apply AxiomII'. tauto. red. red in H1'. red in H2'.
    destruct H1' as [J1[δ1[J2[J3 J4]]]].
    destruct H2' as [K1[δ2[K2[K3 K4]]]]. 
    split. 
    + red. intros. applyAxiomII' H3. applyAxiomII' H4.
      destruct H3 as [H3[H3' H3'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H3''. auto. 
    + pose proof (Lemma1 δ1 δ2); auto.
      apply H3 in J2 as H3'; auto.
      clear H3.
      destruct H3' as [δ3[H3[H3' H3'']]].
      exists δ3. split; auto. split.
      red. intros. apply AxiomII. exists (f [z] - g [z]). 
      apply AxiomII'. split.
      apply J3. applyAxiomII H4.
      apply AxiomII. lra. split. apply K3.
      applyAxiomII H4. apply AxiomII. lra. auto.
      intros. 
      assert (H4': ε/2 > 0). lra.
      apply J4 in H4' as J4'.
      apply K4 in H4' as K4'.
      destruct J4' as [δ1'[J4' J4'']].
      destruct K4' as [δ2'[K4' K4'']]. 
      pose proof (Lemma1' δ1' δ2' δ3). 
      assert (δ1' > 0). lra. apply H5 in H6; auto.
      destruct H6 as [δ3'[H6[H6'[H6'' H6''']]]].
      exists δ3'. split. lra. intros.  
      assert (H8':x0 < x1 < x0 + δ2'). lra.
      assert (H8:x0 < x1 < x0 + δ1'). lra.
      apply J4'' in H8. apply K4'' in H8'.
      assert ((f \- g) [x1] = f[x1] - g[x1]).
      { apply f_x. red. intros. 
        applyAxiomII' H9. applyAxiomII' H10.
        destruct H9 as [H9[H9' H9'']].
        destruct H10 as [H10[H10' H10'']].
        rewrite H9''. auto. apply AxiomII'.
        split. apply J3. apply AxiomII. lra.
        split. apply K3. apply AxiomII. lra.
        auto. }
      rewrite H9.
      assert ((f \- g) [x0] = f[x0] - g[x0]).
      { apply f_x. red. intros.  
        applyAxiomII' H10. applyAxiomII' H11.
        destruct H10 as [H10[H10' H10'']].
        destruct H11 as [H11[H11' H11'']].
        rewrite H10''. auto. apply AxiomII'.
        split. auto.
        split. auto.
        auto. }
      rewrite H10. apply Abs_R in H8. apply Abs_R in H8'.
      apply Abs_R. lra. tauto. 
  + red. red in H''. destruct H'' as [H1 H1'].
    red in H0''. destruct H0'' as [H2 H2'].
    split. apply AxiomII. exists (f [x] - g [x]). 
    apply AxiomII'. tauto. red. red in H1'. red in H2'.
    destruct H1' as [J1[δ1[J2[J3 J4]]]].
    destruct H2' as [K1[δ2[K2[K3 K4]]]]. 
    split. 
    * red. intros. applyAxiomII' H3. applyAxiomII' H4.
      destruct H3 as [H3[H3' H3'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H3''. auto. 
    * pose proof (Lemma1 δ1 δ2); auto.
      apply H3 in J2 as H3'; auto.
      clear H3.
      destruct H3' as [δ3[H3[H3' H3'']]].
      exists δ3. split; auto. split.
      red. intros. apply AxiomII. exists (f [z] - g [z]). 
      apply AxiomII'. split.
      apply J3. applyAxiomII H4.
      apply AxiomII. lra. split. apply K3.
      applyAxiomII H4. apply AxiomII. lra. auto.
      intros. 
      assert (H4': ε/2 > 0). lra.
      apply J4 in H4' as J4'.
      apply K4 in H4' as K4'.
      destruct J4' as [δ1'[J4' J4'']].
      destruct K4' as [δ2'[K4' K4'']]. 
      pose proof (Lemma1' δ1' δ2' δ3). 
      assert (δ1' > 0). lra. apply H5 in H6; auto.
      destruct H6 as [δ3'[H6[H6'[H6'' H6''']]]].
      exists δ3'. split. lra. intros.  
      assert (H8':x - δ2' < x1 < x). lra.
      assert (H8:x - δ1' < x1 < x). lra.
      apply J4'' in H8. apply K4'' in H8'.
      assert ((f \- g) [x1] = f[x1] - g[x1]).
      { apply f_x. red. intros. 
        applyAxiomII' H9. applyAxiomII' H10.
        destruct H9 as [H9[H9' H9'']].
        destruct H10 as [H10[H10' H10'']].
        rewrite H9''. auto. apply AxiomII'.
        split. apply J3. apply AxiomII. lra.
        split. apply K3. apply AxiomII. lra.
        auto. }
      rewrite H9. 
      assert ((f \- g) [x] = f[x] - g[x]).
      { apply f_x. red. intros.  
        applyAxiomII' H10. applyAxiomII' H11.
        destruct H10 as [H10[H10' H10'']].
        destruct H11 as [H11[H11' H11'']].
        rewrite H10''. auto. apply AxiomII'.
        split. auto.
        split. auto.
        auto. }
      rewrite H10. apply Abs_R in H8. apply Abs_R in H8'.
      apply Abs_R. lra. tauto.
Qed.

Lemma Lemma6_10_4' : ∀(f g: Fun) (x0 x: R), 
    ContinuousClose f x0 x -> ContinuousClose g x0 x ->
    ContinuousClose (f \+ g) x0 x.
Proof. 
  intros. red in H. destruct H as [H [H' H'']].
  red in H0. destruct H0 as [H0 [H0' H0'']].
  red. split.
  - red. intros. apply Theorem4_4_1. auto. pose proof H1 as H1'.
    red in H. apply H in H1. red in H0. apply H0 in H1'.
    auto. auto. intros. apply f_x. red. intros.
    applyAxiomII' H3. applyAxiomII' H4.
    destruct H3 as [H3[H3' H3'']].
    destruct H4 as [H4[H4' H4'']].
    rewrite H3''. auto.
    apply AxiomII'. applyAxiomII H2. tauto.
  - split. red. red in H'. destruct H' as [H1 H1'].
    red in H0'. destruct H0' as [H2 H2'].
    split. apply AxiomII. exists (f [x0] + g [x0]). 
    apply AxiomII'. tauto. red. red in H1'. red in H2'.
    destruct H1' as [J1[δ1[J2[J3 J4]]]].
    destruct H2' as [K1[δ2[K2[K3 K4]]]]. 
    split. 
    + red. intros. applyAxiomII' H3. applyAxiomII' H4.
      destruct H3 as [H3[H3' H3'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H3''. auto. 
    + pose proof (Lemma1 δ1 δ2); auto.
      apply H3 in J2 as H3'; auto.
      clear H3.
      destruct H3' as [δ3[H3[H3' H3'']]].
      exists δ3. split; auto. split.
      red. intros. apply AxiomII. exists (f [z] + g [z]). 
      apply AxiomII'. split.
      apply J3. applyAxiomII H4.
      apply AxiomII. lra. split. apply K3.
      applyAxiomII H4. apply AxiomII. lra. auto.
      intros. 
      assert (H4': ε/2 > 0). lra.
      apply J4 in H4' as J4'.
      apply K4 in H4' as K4'.
      destruct J4' as [δ1'[J4' J4'']].
      destruct K4' as [δ2'[K4' K4'']]. 
      pose proof (Lemma1' δ1' δ2' δ3). 
      assert (δ1' > 0). lra. apply H5 in H6; auto.
      destruct H6 as [δ3'[H6[H6'[H6'' H6''']]]].
      exists δ3'. split. lra. intros.  
      assert (H8':x0 < x1 < x0 + δ2'). lra.
      assert (H8:x0 < x1 < x0 + δ1'). lra.
      apply J4'' in H8. apply K4'' in H8'.
      assert ((f \+ g) [x1] = f[x1] + g[x1]).
      { apply f_x. red. intros. 
        applyAxiomII' H9. applyAxiomII' H10.
        destruct H9 as [H9[H9' H9'']].
        destruct H10 as [H10[H10' H10'']].
        rewrite H9''. auto. apply AxiomII'.
        split. apply J3. apply AxiomII. lra.
        split. apply K3. apply AxiomII. lra.
        auto. }
      rewrite H9.
      assert ((f \+ g) [x0] = f[x0] + g[x0]).
      { apply f_x. red. intros.  
        applyAxiomII' H10. applyAxiomII' H11.
        destruct H10 as [H10[H10' H10'']].
        destruct H11 as [H11[H11' H11'']].
        rewrite H10''. auto. apply AxiomII'.
        split. auto.
        split. auto.
        auto. }
      rewrite H10. apply Abs_R in H8. apply Abs_R in H8'.
      apply Abs_R. lra. tauto. 
  + red. red in H''. destruct H'' as [H1 H1'].
    red in H0''. destruct H0'' as [H2 H2'].
    split. apply AxiomII. exists (f [x] + g [x]). 
    apply AxiomII'. tauto. red. red in H1'. red in H2'.
    destruct H1' as [J1[δ1[J2[J3 J4]]]].
    destruct H2' as [K1[δ2[K2[K3 K4]]]]. 
    split. 
    * red. intros. applyAxiomII' H3. applyAxiomII' H4.
      destruct H3 as [H3[H3' H3'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H3''. auto. 
    * pose proof (Lemma1 δ1 δ2); auto.
      apply H3 in J2 as H3'; auto.
      clear H3.
      destruct H3' as [δ3[H3[H3' H3'']]].
      exists δ3. split; auto. split.
      red. intros. apply AxiomII. exists (f [z] + g [z]). 
      apply AxiomII'. split.
      apply J3. applyAxiomII H4.
      apply AxiomII. lra. split. apply K3.
      applyAxiomII H4. apply AxiomII. lra. auto.
      intros. 
      assert (H4': ε/2 > 0). lra.
      apply J4 in H4' as J4'.
      apply K4 in H4' as K4'.
      destruct J4' as [δ1'[J4' J4'']].
      destruct K4' as [δ2'[K4' K4'']]. 
      pose proof (Lemma1' δ1' δ2' δ3). 
      assert (δ1' > 0). lra. apply H5 in H6; auto.
      destruct H6 as [δ3'[H6[H6'[H6'' H6''']]]].
      exists δ3'. split. lra. intros.  
      assert (H8':x - δ2' < x1 < x). lra.
      assert (H8:x - δ1' < x1 < x). lra.
      apply J4'' in H8. apply K4'' in H8'.
      assert ((f \+ g) [x1] = f[x1] + g[x1]).
      { apply f_x. red. intros. 
        applyAxiomII' H9. applyAxiomII' H10.
        destruct H9 as [H9[H9' H9'']].
        destruct H10 as [H10[H10' H10'']].
        rewrite H9''. auto. apply AxiomII'.
        split. apply J3. apply AxiomII. lra.
        split. apply K3. apply AxiomII. lra.
        auto. }
      rewrite H9. 
      assert ((f \+ g) [x] = f[x] + g[x]).
      { apply f_x. red. intros.  
        applyAxiomII' H10. applyAxiomII' H11.
        destruct H10 as [H10[H10' H10'']].
        destruct H11 as [H11[H11' H11'']].
        rewrite H10''. auto. apply AxiomII'.
        split. auto.
        split. auto.
        auto. }
      rewrite H10. apply Abs_R in H8. apply Abs_R in H8'.
      apply Abs_R. lra. tauto.
Qed.

Theorem Theorem3_3_1' : ∀ (f : Fun) (x0 : R), (∃ A, limit_pos f x0 A) ->
  (∃ δ, δ > 0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (rightNeighbor0 x0 δ) -> Abs[f[x]] <= M))).
Proof.
  intros f x0 H0. destruct H0 as [A H0].
  destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5.
  destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra.
  exists (Abs[A] + 1). split.
  - generalize (Abs_Rge0 A). intro I7. lra.
  - intros x I7. applyAxiomII I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A).
    intro I8. lra.
Qed.

Theorem Theorem3_3_2' : ∀ (f : Fun) (x0 : R), (∃ A, limit_neg f x0 A) ->
  (∃ δ, δ > 0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (leftNeighbor0 x0 δ) -> Abs[f[x]] <= M))).
Proof.
  intros f x0 H0. destruct H0 as [A H0].
  destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5.
  destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra.
  exists (Abs[A] + 1). split.
  - generalize (Abs_Rge0 A). intro I7. lra.
  - intros x I7. applyAxiomII I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A).
    intro I8. lra.
Qed.

Theorem Theorem3_4_1' : ∀ (f : Fun) (x0 A : R), limit_pos f x0 A -> A > 0 ->
  (∀ r, 0 < r < A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (rightNeighbor0 x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4_2' : ∀ (f : Fun) (x0 A : R), limit_pos f x0 A -> A < 0 ->
  (∀ r, 0 < r < -A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (rightNeighbor0 x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(A + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4_1'' : ∀ (f : Fun) (x0 A : R), limit_neg f x0 A -> A > 0 ->
  (∀ r, 0 < r < A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (leftNeighbor0 x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4_2'' : ∀ (f : Fun) (x0 A : R), limit_neg f x0 A -> A < 0 ->
  (∀ r, 0 < r < -A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (leftNeighbor0 x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(A + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Lemma Lemma6_10_4_1 : ∀ (f g : Fun) (x0 A B : R),
  limit_pos f x0 A -> limit_pos g x0 B
  -> limit_pos (f ** g) x0 (A*B).
Proof. 
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]]. 
  assert (H14 : (∃ δ3', δ3' >0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (rightNeighbor0 x0 δ3') -> Abs[g[x]] <= M)))).
  { apply Theorem3_3_1'. exists B. split; auto. exists δ2'.
    repeat split; auto. }
  destruct H14 as [δ3' [H14 H15]].
  assert (H8 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2' /\ δ' <= δ3').
  { destruct (Rlt_or_le δ1' δ2') as [J1 | J1].
    - destruct (Rlt_or_le δ1' δ3') as [J2 | J2];
        [exists (δ1'/2) | exists (δ3'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2' δ3') as [J2 | J2];
        [exists (δ2'/2) | exists (δ3'/2)]; repeat split; lra. }
  destruct H8 as [δ' [H8 [H9 [H10 H11]]]].
  assert (H12 : Function (f ** g)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  split; auto. exists (δ'). split; auto.
  assert (H13 : rightNeighbor0 x0 δ' ⊂ dom[ f ** g]).
  { intros x I1. apply AxiomII. exists (f[x]*g[x]).
    apply AxiomII'. repeat split; [apply H2 | apply H6];
    apply AxiomII; applyAxiomII I1; lra. }
  split; auto.
  destruct H15 as [M H15].
  intros ε H16. destruct H15 as [H15 H17].
  generalize (Abs_Rge0 A). intro H18.
  assert (H19 : ε / (M+Abs[A]) > 0).
  { apply  Rmult_gt_0_compat; auto.
    apply Rinv_0_lt_compat. lra. }
  apply H7 in H19 as H21. apply H3 in H19 as H20.
  destruct H20 as [δ1 [H22 H23]].
  destruct H21 as [δ2 [H24 H25]].
  assert (H26 : ∃ δ, δ > 0 /\ δ <= δ1 /\ δ <= δ2 /\ δ < δ').
  { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
    - destruct (Rlt_or_le δ1 δ') as [J2 | J2];
        [exists (δ1/2) | exists (δ'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2 δ') as [J2 | J2];
        [exists (δ2/2) | exists (δ'/2)]; repeat split; lra. }
  destruct H26 as [δ [H26 [H27 [H28 H29]]]].
  exists δ. split; [lra | idtac]. intros x H30.
  assert (H31 : x0 < x < x0 + δ1). lra.
  assert (H32 : x0 < x < x0 + δ2). lra.
  assert (H33 : (f ** g)[x] = f[x]*g[x]).
  { apply f_x; auto. apply AxiomII'. repeat split;
    [apply H2 | apply H6]; apply AxiomII; lra. }
  rewrite H33. clear H33. apply H23 in H31 as H33.
  apply H25 in H32 as H34.
  assert (H35 : f[x]*g[x] - A*B =
    (f[x]-A)*g[x] + A*(g[x]-B)). field.
  rewrite H35.
  generalize (Abs_plus_le ((f[x]-A)*g[x]) (A*(g[x]-B))).
  intro H36. generalize (Abs_mult (f[x]-A) (g[x])).
  intro H37. generalize (Abs_mult (A) (g[x]-B)).
  intro H38. rewrite H37 in H36. rewrite H38 in H36.
  apply Rle_lt_trans with (r2 := Abs[f[x]-A]*Abs[g[x]] +
    Abs[A]*Abs[g[x]-B]); auto.
  assert (H39 : Abs[g[x]] <= M).
  { apply H17. apply AxiomII. lra. }
  assert (H40 : ε = (ε/(M + Abs[A])) * M + Abs[A]*(ε/(M + Abs[A]))).
  field; lra. rewrite H40. apply Rplus_lt_le_compat.
  - destruct H39 as [H39 | H39].
    + apply Rmult_le_0_lt_compat; auto;
      apply Rge_le; apply Abs_Rge0.
    + rewrite H39. apply Rmult_lt_compat_r; auto.
  - apply Rmult_le_compat_l; lra.
Qed.

Lemma Lemma6_10_4_2 : ∀ (f g : Fun) (x0 A B : R),
  limit_neg f x0 A -> limit_neg g x0 B
  -> limit_neg (f ** g) x0 (A*B).
Proof. 
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]]. 
  assert (H14 : (∃ δ3', δ3' >0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (leftNeighbor0 x0 δ3') -> Abs[g[x]] <= M)))).
  { apply Theorem3_3_2'. exists B. split; auto. exists δ2'.
    repeat split; auto. }
  destruct H14 as [δ3' [H14 H15]].
  assert (H8 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2' /\ δ' <= δ3').
  { destruct (Rlt_or_le δ1' δ2') as [J1 | J1].
    - destruct (Rlt_or_le δ1' δ3') as [J2 | J2];
        [exists (δ1'/2) | exists (δ3'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2' δ3') as [J2 | J2];
        [exists (δ2'/2) | exists (δ3'/2)]; repeat split; lra. }
  destruct H8 as [δ' [H8 [H9 [H10 H11]]]].
  assert (H12 : Function (f ** g)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  split; auto. exists (δ'). split; auto.
  assert (H13 : leftNeighbor0 x0 δ' ⊂ dom[ f ** g]).
  { intros x I1. apply AxiomII. exists (f[x]*g[x]).
    apply AxiomII'. repeat split; [apply H2 | apply H6];
    apply AxiomII; applyAxiomII I1; lra. }
  split; auto.
  destruct H15 as [M H15].
  intros ε H16. destruct H15 as [H15 H17].
  generalize (Abs_Rge0 A). intro H18.
  assert (H19 : ε / (M+Abs[A]) > 0).
  { apply  Rmult_gt_0_compat; auto.
    apply Rinv_0_lt_compat. lra. }
  apply H7 in H19 as H21. apply H3 in H19 as H20.
  destruct H20 as [δ1 [H22 H23]].
  destruct H21 as [δ2 [H24 H25]].
  assert (H26 : ∃ δ, δ > 0 /\ δ <= δ1 /\ δ <= δ2 /\ δ < δ').
  { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
    - destruct (Rlt_or_le δ1 δ') as [J2 | J2];
        [exists (δ1/2) | exists (δ'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2 δ') as [J2 | J2];
        [exists (δ2/2) | exists (δ'/2)]; repeat split; lra. }
  destruct H26 as [δ [H26 [H27 [H28 H29]]]].
  exists δ. split; [lra | idtac]. intros x H30.
  assert (H31 : x0 - δ1 < x < x0). lra.
  assert (H32 : x0 - δ2 < x < x0). lra.
  assert (H33 : (f ** g)[x] = f[x]*g[x]).
  { apply f_x; auto. apply AxiomII'. repeat split;
    [apply H2 | apply H6]; apply AxiomII; lra. }
  rewrite H33. clear H33. apply H23 in H31 as H33.
  apply H25 in H32 as H34.
  assert (H35 : f[x]*g[x] - A*B =
    (f[x]-A)*g[x] + A*(g[x]-B)). field.
  rewrite H35.
  generalize (Abs_plus_le ((f[x]-A)*g[x]) (A*(g[x]-B))).
  intro H36. generalize (Abs_mult (f[x]-A) (g[x])).
  intro H37. generalize (Abs_mult (A) (g[x]-B)).
  intro H38. rewrite H37 in H36. rewrite H38 in H36.
  apply Rle_lt_trans with (r2 := Abs[f[x]-A]*Abs[g[x]] +
    Abs[A]*Abs[g[x]-B]); auto.
  assert (H39 : Abs[g[x]] <= M).
  { apply H17. apply AxiomII. lra. }
  assert (H40 : ε = (ε/(M + Abs[A])) * M + Abs[A]*(ε/(M + Abs[A]))).
  field; lra. rewrite H40. apply Rplus_lt_le_compat.
  - destruct H39 as [H39 | H39].
    + apply Rmult_le_0_lt_compat; auto;
      apply Rge_le; apply Abs_Rge0.
    + rewrite H39. apply Rmult_lt_compat_r; auto.
  - apply Rmult_le_compat_l; lra.
Qed.

Theorem Lemma6_10_4_3' : ∀ (f : Fun) (x0 A : R),
  limit_pos f x0 A -> A <> 0
  -> limit_pos (1 /// f) x0 (/A).
Proof.
  intros f x0 A H0 H1.
  assert (H2 : ∃ δ1', δ1' > 0 /\ 
  (∀ x, x ∈ (rightNeighbor0 x0 δ1')
    -> f[x] <> 0)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra.
    - generalize (Theorem3_4_1' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra. }
  destruct H2 as [δ1' [H2 H3]].
  assert (H4 : ∃ δ1, δ1 > 0 /\ (∀ x, x ∈ (rightNeighbor0 x0 δ1)
    -> Abs[f[x]] > Abs[A]/2)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] < 0). lra.
      repeat rewrite Abs_lt; auto. lra.
    - generalize (Theorem3_4_1' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] > 0). lra.
      repeat rewrite Abs_gt; auto. lra. }
  destruct H4 as [δ1 [H5 H6]].
  assert (H7 : ∀ ε, ε > 0 -> ∃ δ, δ > 0
    /\ rightNeighbor0 x0 δ ⊂ dom[ f]
    /\ (∀ x, x ∈ (rightNeighbor0 x0 δ)
    -> Abs[1/f[x]-1/A] < 2*ε/(A*A))).
  { intros ε I1. destruct H0 as [H0 [δ2' [I2 [I3 I4]]]].
    apply I4 in I1 as I5.
    destruct I5 as [δ2 [I6 I7]].
    assert (I8 : ∃ δ, δ > 0 /\ δ < δ1' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ1' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ1' δ2) as [J2 | J2];
          [exists (δ1'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct I8 as [δ [I8 [I9 [I10 I11]]]].
    exists δ. 
    assert (I12 : rightNeighbor0 x0 δ ⊂ dom[ f]).
    { intros x J1. apply I3. apply AxiomII.
      applyAxiomII J1. lra. }
    repeat split; auto.
    intros x I13. assert (I14 : f[x] <> 0).
    { apply H3. apply AxiomII.
      applyAxiomII I13. lra. }
    assert (I15 : 1/f[x] - 1/A = - ((f[x]-A)/(f[x]*A))).
    { field. split; auto. }
    rewrite I15. rewrite <- Abs_eq_neg.
    assert (I16 : f[x]*A <> 0).
    { apply Rmult_integral_contrapositive_currified; auto. }
    rewrite Abs_div; auto.
    rewrite Abs_mult. clear I15.
    assert (I17 : Abs[f[x]] > Abs[A] / 2).
    { apply H6. apply AxiomII. applyAxiomII I13.
      lra. }
    assert (I18 : Abs[A] > 0).
    { apply Abs_not_eq_0. apply H1. }
    assert (I19 : Abs[f[x]]*Abs[A] > (Abs[A]/2)*Abs[A]).
    { apply Rmult_gt_compat_r; auto. }
    assert (I20 : Abs[A]/2 * Abs[A] = (A*A) / 2).
    { apply Rdichotomy in H1.
      destruct H1 as [H1 | H1].
      - rewrite Abs_lt; auto. field.
      - rewrite Abs_gt; auto. field. }
    assert (I21 : 0 < (Abs[A]/2*Abs[A]) * (Abs[f[x]]*Abs[A])).
    { apply Rmult_gt_0_compat; apply Rmult_gt_0_compat; lra. }
    apply Rinv_lt_contravar in I19; auto.
    clear I21. rewrite I20 in I19.
    assert (I21 : 0 <= Abs[f[x]-A]).
    { apply Rge_le. apply Abs_Rge0. }
    apply Rlt_le in I19 as I22.
    apply Rmult_le_compat_l with
      (r := Abs[f[x]-A]) in I22; auto.
    assert (I23 : A*A/2 > 0).
    { rewrite <- I20. apply Rmult_gt_0_compat; lra. }
    apply Rle_lt_trans with
      (r2 := Abs[f[x]-A] * /(A*A/2)); auto.
    assert (I24 : Abs[f[x]-A] < ε).
    { apply I7. applyAxiomII I13. lra. }
    apply Rinv_0_lt_compat in I23.
    apply Rmult_lt_compat_r with
      (r := / (A*A/2)) in I24; auto.
    assert (I25 : ε * /(A * A / 2) = 2 * ε / (A * A)).
    { field; auto. }
    rewrite <- I25. assumption. }
  unfold limit. assert (H8 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  destruct H0 as [H0 [δ2' [H9 [H10 H11]]]].
  assert (H12 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1];
      [exists δ1' | exists δ2']; lra. }
  destruct H12 as [δ' [H13 [H14 H15]]].
  split; auto. exists δ'. repeat split; auto.
  - intros x I1. apply AxiomII. exists (1/f[x]).
    apply AxiomII'. repeat split;
    [apply H10 | apply H3]; apply AxiomII;
    applyAxiomII I1; lra.
  - intros ε H16. assert (H17 : (A*A) * ε / 2 > 0).
    { assert (I1 : A*A > 0).
      { apply Rdichotomy in H1.
        destruct H1 as [H1 | H1].
        - apply Ropp_gt_lt_0_contravar in H1 as I1.
          assert (I2 : (-A)*(-A) = A*A). field.
          rewrite <- I2. apply Rmult_gt_0_compat; auto.
        - apply Rmult_gt_0_compat; auto. }
      assert (I2 : A * A * ε / 2 = (A * A) * (ε / 2)).
      field. rewrite I2. apply Rmult_gt_0_compat; auto.
      lra. }
    apply H7 in H17 as H18.
    destruct H18 as [δ2 [H18 [H19 H20]]].
    assert (H21 : ∃ δ, δ > 0 /\ δ < δ2 /\ δ < δ').
    { destruct (Rlt_or_le δ2 δ') as [I1 | I1];
        [exists ((δ2)/2) | exists (δ'/2)]; lra. }
    destruct H21 as [δ [H21 [H22 H23]]].
    exists δ. split; try lra.
    intros x H24.
    assert (H25 : (1 /// f)[x] = 1/f[x]).
    { apply f_x; auto. apply AxiomII'.
      repeat split; auto.
      - apply H10. apply AxiomII. lra.
      - apply H3. apply AxiomII. lra. }
    rewrite H25.
    assert (H26 : 2 * (A * A * ε / 2) / (A * A) = ε).
    { field; auto. }
    rewrite H26 in H20.
    assert (H27 : /A = 1/A). field; auto.
    rewrite H27. apply H20.
    apply AxiomII. lra.
Qed.

Lemma Lemma6_10_4_3 : ∀ (f g : Fun) (x0 A B : R),
  limit_pos f x0 A -> limit_pos g x0 B -> B <> 0
  -> limit_pos (f // g) x0 (A/B).
Proof. 
  intros f g x0 A B H0 H1 H2. 
  apply Lemma6_10_4_3' in H1 as H3; auto.
  assert (H4 : f // g = f ** (1 /// g)).
  { apply AxiomI.
    assert (I6 : ∀ x, x ∈ dom[g] -> g[x] <> 0
      -> (1 /// g)[x] = /g[x]).
    { intros x J1 J2. apply f_x; try apply H3. apply AxiomII'.
      repeat split; auto. field. auto. }
    intro z; split; intro I1.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 [I4 I5]]]]]].
      rewrite I1. apply AxiomII'. repeat split; auto.
      + apply AxiomII. exists (1/g[x]).
        apply AxiomII'. repeat split; auto.
      + rewrite I6; auto.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 I4]]]]].
      rewrite I1. apply AxiomII'.
      split; auto. applyAxiomII I3.
      destruct I3 as [y' I3]. applyAxiomII' I3.
      destruct I3 as [I3 [I5 I7]].
      rewrite I6 in I4; auto. } 
  rewrite H4. apply Lemma6_10_4_1; auto.
Qed.

Theorem Lemma6_10_4_4' : ∀ (f : Fun) (x0 A : R),
  limit_neg f x0 A -> A <> 0
  -> limit_neg (1 /// f) x0 (/A).
Proof.
  intros f x0 A H0 H1.
  assert (H2 : ∃ δ1', δ1' > 0 /\ 
  (∀ x, x ∈ (leftNeighbor0 x0 δ1')
    -> f[x] <> 0)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2'' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra.
    - generalize (Theorem3_4_1'' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra. }
  destruct H2 as [δ1' [H2 H3]].
  assert (H4 : ∃ δ1, δ1 > 0 /\ (∀ x, x ∈ (leftNeighbor0 x0 δ1)
    -> Abs[f[x]] > Abs[A]/2)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2'' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] < 0). lra.
      repeat rewrite Abs_lt; auto. lra.
    - generalize (Theorem3_4_1'' f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] > 0). lra.
      repeat rewrite Abs_gt; auto. lra. }
  destruct H4 as [δ1 [H5 H6]].
  assert (H7 : ∀ ε, ε > 0 -> ∃ δ, δ > 0
    /\ leftNeighbor0 x0 δ ⊂ dom[ f]
    /\ (∀ x, x ∈ (leftNeighbor0 x0 δ)
    -> Abs[1/f[x]-1/A] < 2*ε/(A*A))).
  { intros ε I1. destruct H0 as [H0 [δ2' [I2 [I3 I4]]]].
    apply I4 in I1 as I5.
    destruct I5 as [δ2 [I6 I7]].
    assert (I8 : ∃ δ, δ > 0 /\ δ < δ1' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ1' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ1' δ2) as [J2 | J2];
          [exists (δ1'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct I8 as [δ [I8 [I9 [I10 I11]]]].
    exists δ. 
    assert (I12 : leftNeighbor0 x0 δ ⊂ dom[ f]).
    { intros x J1. apply I3. apply AxiomII.
      applyAxiomII J1. lra. }
    repeat split; auto.
    intros x I13. assert (I14 : f[x] <> 0).
    { apply H3. apply AxiomII.
      applyAxiomII I13. lra. }
    assert (I15 : 1/f[x] - 1/A = - ((f[x]-A)/(f[x]*A))).
    { field. split; auto. }
    rewrite I15. rewrite <- Abs_eq_neg.
    assert (I16 : f[x]*A <> 0).
    { apply Rmult_integral_contrapositive_currified; auto. }
    rewrite Abs_div; auto.
    rewrite Abs_mult. clear I15.
    assert (I17 : Abs[f[x]] > Abs[A] / 2).
    { apply H6. apply AxiomII. applyAxiomII I13.
      lra. }
    assert (I18 : Abs[A] > 0).
    { apply Abs_not_eq_0. apply H1. }
    assert (I19 : Abs[f[x]]*Abs[A] > (Abs[A]/2)*Abs[A]).
    { apply Rmult_gt_compat_r; auto. }
    assert (I20 : Abs[A]/2 * Abs[A] = (A*A) / 2).
    { apply Rdichotomy in H1.
      destruct H1 as [H1 | H1].
      - rewrite Abs_lt; auto. field.
      - rewrite Abs_gt; auto. field. }
    assert (I21 : 0 < (Abs[A]/2*Abs[A]) * (Abs[f[x]]*Abs[A])).
    { apply Rmult_gt_0_compat; apply Rmult_gt_0_compat; lra. }
    apply Rinv_lt_contravar in I19; auto.
    clear I21. rewrite I20 in I19.
    assert (I21 : 0 <= Abs[f[x]-A]).
    { apply Rge_le. apply Abs_Rge0. }
    apply Rlt_le in I19 as I22.
    apply Rmult_le_compat_l with
      (r := Abs[f[x]-A]) in I22; auto.
    assert (I23 : A*A/2 > 0).
    { rewrite <- I20. apply Rmult_gt_0_compat; lra. }
    apply Rle_lt_trans with
      (r2 := Abs[f[x]-A] * /(A*A/2)); auto.
    assert (I24 : Abs[f[x]-A] < ε).
    { apply I7. applyAxiomII I13. lra. }
    apply Rinv_0_lt_compat in I23.
    apply Rmult_lt_compat_r with
      (r := / (A*A/2)) in I24; auto.
    assert (I25 : ε * /(A * A / 2) = 2 * ε / (A * A)).
    { field; auto. }
    rewrite <- I25. assumption. }
  unfold limit. assert (H8 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  destruct H0 as [H0 [δ2' [H9 [H10 H11]]]].
  assert (H12 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1];
      [exists δ1' | exists δ2']; lra. }
  destruct H12 as [δ' [H13 [H14 H15]]].
  split; auto. exists δ'. repeat split; auto.
  - intros x I1. apply AxiomII. exists (1/f[x]).
    apply AxiomII'. repeat split;
    [apply H10 | apply H3]; apply AxiomII;
    applyAxiomII I1; lra.
  - intros ε H16. assert (H17 : (A*A) * ε / 2 > 0).
    { assert (I1 : A*A > 0).
      { apply Rdichotomy in H1.
        destruct H1 as [H1 | H1].
        - apply Ropp_gt_lt_0_contravar in H1 as I1.
          assert (I2 : (-A)*(-A) = A*A). field.
          rewrite <- I2. apply Rmult_gt_0_compat; auto.
        - apply Rmult_gt_0_compat; auto. }
      assert (I2 : A * A * ε / 2 = (A * A) * (ε / 2)).
      field. rewrite I2. apply Rmult_gt_0_compat; auto.
      lra. }
    apply H7 in H17 as H18.
    destruct H18 as [δ2 [H18 [H19 H20]]].
    assert (H21 : ∃ δ, δ > 0 /\ δ < δ2 /\ δ < δ').
    { destruct (Rlt_or_le δ2 δ') as [I1 | I1];
        [exists ((δ2)/2) | exists (δ'/2)]; lra. }
    destruct H21 as [δ [H21 [H22 H23]]].
    exists δ. split; try lra.
    intros x H24.
    assert (H25 : (1 /// f)[x] = 1/f[x]).
    { apply f_x; auto. apply AxiomII'.
      repeat split; auto.
      - apply H10. apply AxiomII. lra.
      - apply H3. apply AxiomII. lra. }
    rewrite H25.
    assert (H26 : 2 * (A * A * ε / 2) / (A * A) = ε).
    { field; auto. }
    rewrite H26 in H20.
    assert (H27 : /A = 1/A). field; auto.
    rewrite H27. apply H20.
    apply AxiomII. lra.
Qed.

Lemma Lemma6_10_4_4 : ∀ (f g : Fun) (x0 A B : R),
  limit_neg f x0 A -> limit_neg g x0 B -> B <> 0
  -> limit_neg (f // g) x0 (A/B).
Proof. 
  intros f g x0 A B H0 H1 H2. 
  apply Lemma6_10_4_4' in H1 as H3; auto.
  assert (H4 : f // g = f ** (1 /// g)).
  { apply AxiomI.
    assert (I6 : ∀ x, x ∈ dom[g] -> g[x] <> 0
      -> (1 /// g)[x] = /g[x]).
    { intros x J1 J2. apply f_x; try apply H3. apply AxiomII'.
      repeat split; auto. field. auto. }
    intro z; split; intro I1.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 [I4 I5]]]]]].
      rewrite I1. apply AxiomII'. repeat split; auto.
      + apply AxiomII. exists (1/g[x]).
        apply AxiomII'. repeat split; auto.
      + rewrite I6; auto.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 I4]]]]].
      rewrite I1. apply AxiomII'.
      split; auto. applyAxiomII I3.
      destruct I3 as [y' I3]. applyAxiomII' I3.
      destruct I3 as [I3 [I5 I7]].
      rewrite I6 in I4; auto. }
  rewrite H4. apply Lemma6_10_4_2; auto.
Qed.

Lemma Lemma6_10_7: ∀(f g: Fun) (x0 x: R), 
    ContinuousClose f x0 x -> ContinuousClose g x0 x -> 
    (∀a, g[a] <> 0) -> ContinuousClose (f // g) x0 x.
Proof. 
  intros. red in H. destruct H as [H [H' H'']].
  red in H0. destruct H0 as [H0 [H0' H0'']].
  red. split.
  - red. intros. apply Theorem4_4_4. auto. auto.
    pose proof (H1 x1). auto. 
    intros. apply f_x. red. intros.
    applyAxiomII' H5. applyAxiomII' H6.
    destruct H5 as [H5[H5' [H5''' H5'']]].
    destruct H6 as [H6[H6' [H6''' H6'']]].
    rewrite H5''. auto.
    apply AxiomII'. applyAxiomII H3.
    split; tauto.
  - split.  
    + red. red in H'. destruct H' as [H2 H2'].
    red in H0'. destruct H0' as [H3 H3'].
    split. apply AxiomII. exists (f [x0] / g [x0]). 
    apply AxiomII'. pose proof (H1 x0). tauto. 
    assert ((f // g) [x0] = f [x0] / g [x0]).
    { apply f_x. red. intros. applyAxiomII' H4.
      applyAxiomII' H5. destruct H4 as [H4[H4' [H4''' H4'']]].
      destruct H5 as [H5[H5' [H5''' H5'']]]. rewrite H5''. auto.
      apply AxiomII'. pose proof (H1 x0). split; tauto. }
    rewrite H4.
    apply Lemma6_10_4_3; auto.  
    + red. red in H''. destruct H'' as [H2 H2'].
    red in H0''. destruct H0'' as [H3 H3'].
    split. apply AxiomII. exists (f [x] / g [x]). 
    apply AxiomII'. pose proof (H1 x). tauto. 
    assert ((f // g) [x] = f [x] / g [x]).
    { apply f_x. red. intros. applyAxiomII' H4.
      applyAxiomII' H5. destruct H4 as [H4[H4' [H4''' H4'']]].
      destruct H5 as [H5[H5' [H5''' H5'']]]. rewrite H5''. auto.
      apply AxiomII'. pose proof (H1 x). split; tauto. }
    rewrite H4.
    apply Lemma6_10_4_4; auto. 
Qed.

Lemma Lemma6_10_7': ∀(f g: Fun) (x0 x: R), 
    ContinuousClose f x0 x -> ContinuousClose g x0 x -> 
    ContinuousClose (f ** g) x0 x.
Proof. 
  intros. red in H. destruct H as [H [H' H'']].
  red in H0. destruct H0 as [H0 [H0' H0'']].
  red. split.
  - red. intros. apply Theorem4_4_3. auto. auto.
    intros. apply f_x. red. intros.
    applyAxiomII' H3. applyAxiomII' H4.
    destruct H3 as [H3[H3' H3'']].
    destruct H4 as [H4[H4' H4'']].
    rewrite H3''. auto.
    apply AxiomII'. applyAxiomII H2.
    split; tauto.
  - split.  
    + red. red in H'. destruct H' as [H2 H2'].
    red in H0'. destruct H0' as [H3 H3'].
    split. apply AxiomII. exists (f [x0] * g [x0]). 
    apply AxiomII'. tauto.
    assert ((f ** g) [x0] = f [x0] * g [x0]).
    { apply f_x. red. intros. applyAxiomII' H1.
      applyAxiomII' H4. destruct H1 as [H1[H1' H1'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H4''. auto.
      apply AxiomII'. split; tauto. }  
    rewrite H1.
    apply Lemma6_10_4_1; auto.  
    + red. red in H''. destruct H'' as [H2 H2'].
    red in H0''. destruct H0'' as [H3 H3'].
    split. apply AxiomII. exists (f [x] * g [x]). 
    apply AxiomII'. tauto.
    assert ((f ** g) [x] = f [x] * g [x]).
    { apply f_x. red. intros. applyAxiomII' H1.
      applyAxiomII' H4. destruct H1 as [H1[H1' H1'']].
      destruct H4 as [H4[H4' H4'']]. rewrite H4''. auto.
      apply AxiomII'. split; tauto. }  
    rewrite H1.
    apply Lemma6_10_4_2; auto.  
Qed.

Lemma Lemma6_10_5: ∀(f : Fun) (x x0: R),
  ContinuousClose \{\ λ t y, y = f [x] \}\ x0 x.
Proof.
  intros. red. split.
  - red. intros. red. split.
    apply AxiomII. exists f[x]. apply AxiomII'. auto.
    red. split. QED_function. exists 1. split. lra.
    split. red. intros. apply AxiomII. exists f[x].
    apply AxiomII'. auto. intros.
    exists (1/2). split. lra. intros.
    assert (\{\ λ t y : R,y = f [x] \}\ [x2] = f[x]).
    apply f_x. QED_function. apply AxiomII'. auto.
    assert (\{\ λ t y : R,y = f [x] \}\ [x1] = f[x]).
    apply f_x. QED_function. apply AxiomII'. auto.
    rewrite H2. rewrite H3. replace (f [x] - f [x]) with 0.
    assert (Abs [0] = 0). rewrite <- Abs_eq_0. lra. 
    rewrite H4. lra. lra.
  - split. 
    + red. split. apply AxiomII. exists f[x].
      apply AxiomII'. auto.
      red. split. QED_function. exists 1. split. lra.
      split. red. intros. apply AxiomII. exists f[x].
      apply AxiomII'. auto.
      intros. exists (1/2). split. lra. intros.
      assert (\{\ λ t y : R,y = f [x] \}\ [x1] = f[x]).
      apply f_x. QED_function. apply AxiomII'. auto.
      assert (\{\ λ t y : R,y = f [x] \}\ [x0] = f[x]).
      apply f_x. QED_function. apply AxiomII'. auto.
      rewrite H2. rewrite H1. replace (f [x] - f [x]) with 0.
      assert (Abs [0] = 0). rewrite <- Abs_eq_0. lra. 
      rewrite H3. lra. lra.
    + red. split. apply AxiomII. exists f[x].
      apply AxiomII'. auto.
      red. split. QED_function. exists 1. split. lra.
      split. red. intros. apply AxiomII. exists f[x].
      apply AxiomII'. auto.
      intros. exists (1/2). split. lra. intros.
      assert (\{\ λ t y : R,y = f [x] \}\ [x1] = f[x]).
      apply f_x. QED_function. apply AxiomII'. auto.
      assert (\{\ λ t y : R,y = f [x] \}\ [x] = f[x]).
      apply f_x. QED_function. apply AxiomII'. auto.
      rewrite H2. rewrite H1. replace (f [x] - f [x]) with 0.
      assert (Abs [0] = 0). rewrite <- Abs_eq_0. lra. 
      rewrite H3. lra. lra.
Qed.

Lemma Lemma6_10_6 : ∀(f : Fun) (a b x0 x: R), a < b ->
  ContinuousClose f a b -> 
  x0 ∈ \[a, b\] -> x ∈ \[a, b\] -> x0 < x ->
  ContinuousClose f x0 x.
Proof.
  intros. red in H0. destruct H0 as [H0[H0' H0'']].
  applyAxiomII H1. applyAxiomII H2. destruct H1 as [H1 H1'].
  destruct H2 as [H2 H2'].
  destruct H1, H1', H2, H2'. 
  - red in H0. red. split.
    + red. intros. cut (a < x1 < b). intros.
      apply H0 in H7. auto. lra. 
    + split. 
      assert (Continuous f x0).
      { assert (a < x0 < b). auto. apply H0 in H6.
        auto. } 
      apply Theorem4_1 in H6. tauto.
      assert (Continuous f x).
      { assert (a < x < b). auto. apply H0 in H6.
        auto. } 
      apply Theorem4_1 in H6. tauto.
  - rewrite H5.
    red. split. 
    + rewrite <- H5. red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. auto. 
    + split. 
      assert (Continuous f x0).
      { assert (a < x0 < b). auto. apply H0 in H6.
        auto. } 
      apply Theorem4_1 in H6. tauto. auto.
  - rewrite <- H2 in H1. lra.
  - rewrite H2 in H5. lra.
  - rewrite <- H4 in H5. lra.
  - rewrite <- H4 in H5. lra.
  - rewrite <- H2 in H1. lra.
  - rewrite <- H4 in H5. lra.
  - red. split.
    + red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. auto. 
    + split. rewrite H1. auto.  
      assert (Continuous f x).
      { assert (a < x < b). auto. apply H0 in H6.
        auto. }
      apply Theorem4_1 in H6. tauto.
  - red. split. 
    + red. intros. assert (a < x1 < b). lra.
      apply H0 in H7. auto.
    + split. rewrite H1. auto.   
      rewrite H5. auto.
  - rewrite <- H1 in H2. lra.
  - rewrite <- H1 in H2. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
  - rewrite H1 in H4. lra.
Qed.

Lemma Lemma6_10_8: ∀ (x0 x: R)(k :nat), x0 < x ->
   ContinuousClose \{\ λ t1 y1, y1 = INR ((S k) !) \}\ x0 x.
Proof. 
  intros. red. split.  
  - red. intros. red. split. apply AxiomII.  
    exists (INR ((S k) !)). apply AxiomII'. auto.
    red. split. QED_function. exists 1. split. lra. split.
    red. intros. apply AxiomII. exists (INR ((S k) !)).
    apply AxiomII'. auto. intros. exists (1/2). split.
    lra. intros. 
    assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x2]
     = INR ((S k) !)).
    { apply f_x. QED_function. apply AxiomII'. auto. }
    assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x1]
     = INR ((S k) !)).
    { apply f_x. QED_function. apply AxiomII'. auto. }
    rewrite H3. rewrite H4. 
    replace (INR ((S k) !) - INR ((S k) !)) with 0.
    replace Abs [0] with 0. lra. pose proof (Abs_eq_0 0).
    destruct H5. symmetry. apply H5. lra. lra.
  - split.
    + assert (Continuous \{\ λ t1 y1,y1 = INR ((S k) !) \}\ x0).
      { red. split. apply AxiomII.  
        exists (INR ((S k) !)). apply AxiomII'. auto.
        red. split. QED_function. exists 1. split. lra. split.
        red. intros. apply AxiomII. exists (INR ((S k) !)).
        apply AxiomII'. auto. intros. exists (1/2). split.
        lra. intros.  
        assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x1]
         = INR ((S k) !)).
        { apply f_x. QED_function. apply AxiomII'. auto. }
        assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x0]
        = INR ((S k) !)).
       { apply f_x. QED_function. apply AxiomII'. auto. }
       rewrite H3. rewrite H2. 
       replace (INR ((S k) !) - INR ((S k) !)) with 0.
       replace Abs [0] with 0. lra. pose proof (Abs_eq_0 0).
       destruct H4. symmetry. apply H4. lra. lra. }
       apply Theorem4_1 in H0. tauto.
   + assert (Continuous \{\ λ t1 y1,y1 = INR ((S k) !) \}\ x).
      { red. split. apply AxiomII.  
        exists (INR ((S k) !)). apply AxiomII'. auto.
        red. split. QED_function. exists 1. split. lra. split.
        red. intros. apply AxiomII. exists (INR ((S k) !)).
        apply AxiomII'. auto. intros. exists (1/2). split.
        lra. intros.  
        assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x1]
         = INR ((S k) !)).
        { apply f_x. QED_function. apply AxiomII'. auto. }
        assert ( \{\ λ t1 y1, y1 = INR ((S k) !) \}\[x]
        = INR ((S k) !)).
       { apply f_x. QED_function. apply AxiomII'. auto. }
       rewrite H3. rewrite H2. 
       replace (INR ((S k) !) - INR ((S k) !)) with 0.
       replace Abs [0] with 0. lra. pose proof (Abs_eq_0 0).
       destruct H4. symmetry. apply H4. lra. lra. }
       apply Theorem4_1 in H0. tauto.
Qed.

Lemma Lemma6_10_9: ∀ (x0 x: R)(k :nat), x0 < x ->
 ContinuousClose \{\ λ t1 y1,  y1 = (x - t1) ^^ S k  \}\ x0 x.
Proof. 
  intros.
  assert(C1: ∀k : nat, Continuous \{\ λ t1 y1, y1 = 
            (x - t1) ^^ k\}\ x0).
  { intros.  
    red. split. apply AxiomII. exists ((x - x0) ^^ k0).
    apply AxiomII'; auto.  
    assert(∀t : R, (x - t) ^^ k0 = (-1 * (t - x)) ^^ k0).
    { intros. replace (-1 * (t - x)) with (x - t). auto.
      lra. }  
    assert(\{\ λ t y,y = (x - t) ^^ k0 \}\ = \{\ λ t y, y = (-1) ^^ k0 * (t - x) ^^ k0 \}\). 
    { apply AxiomI. split; intros.
      - applyAxiomII H1. destruct H1 as [x'[y'[H1 H2]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4. 
        replace (-1 * (x' - x)) with (x - x').
        auto. lra.
      - applyAxiomII H1. destruct H1 as [x'[y'[H1 H2]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4 in H2. 
        replace (-1 * (x' - x)) with (x - x') in H2.
        auto. lra. }  
     rewrite H1. 
     assert(∀t : R,\{\ λ t y,y = (-1) ^^ k0 * (t - x) ^^ k0 \}\ [t] = (-1) ^^ k0 * (t - x) ^^ k0). 
     intros. Function_ass. rewrite H2. 
     apply Lemma7'. } 
  pose proof (C1 (S k)). apply Theorem4_1 in H0. 
  assert(C2: ∀k : nat, Continuous \{\ λ t1 y1, y1 = 
            (x - t1) ^^ k\}\ x).
  { intros. 
    red. split. apply AxiomII. exists ((x - x) ^^ k0).
    apply AxiomII'; auto.  
    assert(∀t : R, (x - t) ^^ k0 = (-1 * (t - x)) ^^ k0).
    { intros. replace (-1 * (t - x)) with (x - t). auto.
      lra. }  
    assert(\{\ λ t y,y = (x - t) ^^ k0 \}\ = \{\ λ t y, y = (-1) ^^ k0 * (t - x) ^^ k0 \}\). 
    { apply AxiomI. split; intros.
      - applyAxiomII H2. destruct H2 as [x'[y'[H2 H3]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4. 
        replace (-1 * (x' - x)) with (x - x').
        auto. lra.
      - applyAxiomII H2. destruct H2 as [x'[y'[H2 H3]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4 in H3. 
        replace (-1 * (x' - x)) with (x - x') in H3.
        auto. lra. }  
     rewrite H2. 
     assert(∀t : R,\{\ λ t y,y = (-1) ^^ k0 * (t - x) ^^ k0 \}\ [t] = (-1) ^^ k0 * (t - x) ^^ k0). 
     intros. Function_ass. rewrite H3. 
     apply Lemma7'. }
  pose proof (C2 (S k)). apply Theorem4_1 in H1.
  red. split. 
  - red. intros. 
    assert(C3: ∀k : nat, Continuous \{\ λ t1 y1, y1 = 
            (x - t1) ^^ k\}\ x1).
    { intros. 
      red. split. apply AxiomII. exists ((x - x1) ^^ k0).
      apply AxiomII'; auto.  
    assert(∀t : R, (x - t) ^^ k0 = (-1 * (t - x)) ^^ k0).
    { intros. replace (-1 * (t - x)) with (x - t). auto.
      lra. }  
    assert(\{\ λ t y,y = (x - t) ^^ k0 \}\ = \{\ λ t y, y = (-1) ^^ k0 * (t - x) ^^ k0 \}\). 
    { apply AxiomI. split; intros.
      - applyAxiomII H4. destruct H4 as [x'[y'[H4 H5]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4. 
        replace (-1 * (x' - x)) with (x - x').
        auto. lra.
      - applyAxiomII H4. destruct H4 as [x'[y'[H4 H5]]].
        apply AxiomII. exists x', y'. split; auto.
        rewrite Lemma_pow4 in H5. 
        replace (-1 * (x' - x)) with (x - x') in H5.
        auto. lra. }  
     rewrite H4. 
     assert(∀t : R,\{\ λ t y,y = (-1) ^^ k0 * (t - x) ^^ k0 \}\ [t] = (-1) ^^ k0 * (t - x) ^^ k0). 
     intros. Function_ass. rewrite H5. 
     apply Lemma7'. }
     pose proof (C3 (S k)). auto.  
  - tauto. 
Qed.

(* Lemma Lemma6_10_6: ∀(n:nat) (f : Seq) ,(n > 0)%nat  -> 
 Σ f  () = Σ f (n - 1) + f[n].
Proof.
  intros. induction n.
  - inversion H.
  - simpl. 
    rewrite Nat.sub_0_r. auto.
Qed. *)

Theorem Theorem6_10 : ∀ (f : Fun) (n : nat) (a b: R), 
  a < b -> Function f -> ( ∀ k : nat, (k <= n)%nat -> 
  (\[a, b\] ⊂ dom[dN f k] /\ ContinuousClose (dN f k) a b)) 
  /\ \(a, b\) ⊂ dom[dN f (S n)] ->
  (∀ (x x0: R), x ∈ \[a, b\] /\ x0 ∈ \[a, b\] /\ x0 < x -> 
    ∃ ξ, ξ ∈ \(a, b\) /\
    f[x] =(Σ \{\ λ k v, v = (dN f k)[x0] /(INR (k!)) * (x - x0)^^k \}\ n) 
          + (dN f (S n))[ξ] /(INR ((S n)!)) * (x - x0)^^(S n)).
Proof.
  intros. destruct H2 as [H2 [H2' H2'']]. 
  destruct H1 as [H1 H1'].
  pose proof (Nat.eq_0_gt_0_cases n) as L1.
  (**n = 0%nat \/ (0 < n)%nat**)
  destruct L1 as [L1|L1].
  (**分情况讨论 n = 0%nat**)
  - rewrite L1.
    assert (J1:(0<=n)%nat). rewrite L1. left.
    apply H1 in J1.
    destruct J1 as [J1 J1'].
    (**J1 : \[ a, b \] ⊂ dom[ dN f 0]
       J1': ContinuousClose (dN f 0) a b **)
    (**由于x，x0 ∈ \[ a, b \]
       所以在闭区间连续 ContinuousClose f x0 x**)
    assert (ContinuousClose f x0 x). 
    { red in J1'. destruct J1' as [H4[H4' H4'']].
      red. split.
      - red. intros. red in H4.
        assert (a < x1 < b). applyAxiomII H2.
        applyAxiomII H2'. lra. apply H4 in H5. auto.
      - split. 
        + applyAxiomII H2'. destruct H2'.
          destruct H5, H3.
          * assert (a < x0 < b). lra. red in H4. apply H4 in H6. 
            apply Theorem4_1 in H6. tauto.
          * applyAxiomII H2. destruct H2.
            rewrite <- H3 in H4'. simpl in H4'. auto.
          * rewrite H5 in H2''. applyAxiomII H2. lra.
          * rewrite H5 in H3. lra.
        + applyAxiomII H2. destruct H2.
          destruct H2, H3.
          * assert (a < x < b). lra. red in H4. apply H4 in H5. 
            apply Theorem4_1 in H5. tauto.
          * rewrite <- H3 in H4''. auto.
          * applyAxiomII H2'. destruct H2'.
            rewrite H2 in H3. lra.
          * rewrite H2 in H3. lra. } 
    (**由条件可得f在(x0,x)之间任意一点都可导**)
    assert (∀ x', x0 < x' < x -> derivable f x'). 
    { intros. red. rewrite L1 in H1'. simpl in H1'.
      exists (\{\ λ x y, derivative f x y \}\[x']).
      assert (\{\ λ x1 y, derivative f x1 y \}\ = (dN f 1)).
      { simpl. auto. }
        assert (H6: x' ∈ dom[(dN f 1)]). rewrite H5 in H1'.
        apply H1'. applyAxiomII H2. applyAxiomII H2'.
        apply AxiomII. lra.
        apply x_fx in H6. simpl in H6. applyAxiomII' H6.
        auto. apply Lemma5_16; auto. }
    pose proof H2'' as H2'''.
    (**由拉格朗日中值定理
    Theorem Theorem6_2 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∀ x, a < x < b -> derivable f x)
  -> ∃ ξ, a < ξ < b /\ derivative f ξ ((f[b] - f[a]) / (b - a))
  可得∃ξ : R,x0 < ξ < x /\ derivative f ξ ((f [x] - f [x0]) / (x - x0))**)
    apply (Theorem6_2 f x0 x) in H2''; auto.
    destruct H2'' as [ξ'[I1 I1']].
    (**找到了这个ξ值**) 
    exists ξ'. split; auto. apply AxiomII. applyAxiomII H2.
    applyAxiomII H2'. lra.
    (**这个ξ，(ξ ∈ \( a, b \)) **)
    simpl.
    assert (\{\λ k v, v = (dN f k) [x0] / INR (k !) * 
                           (x - x0) ^^ k \}\[0%nat] = f [x0]).
    { apply f_x. red. intros. applyAxiomII' H5.
      applyAxiomII' H6. rewrite H6; auto.
      apply AxiomII'. simpl. lra. } 
    rewrite H5. clear H5. 
    unfold Rdiv. rewrite Rmult_1_r. apply H4 in I1. red in I1.
    destruct I1 as [f' I1].
    (**f在ξ'处导数为f'**) 
    assert (\{\ λ x1 y, derivative f x1 y \}\ [ξ'] = f '[ ξ']).
    { apply f_x. red. intros. applyAxiomII' H5. applyAxiomII' H6.
      apply derEqual in H5. apply derEqual in H6. rewrite <- H5; auto.
      apply AxiomII'. apply derEqual in I1 as I1''.
      rewrite I1''. auto.  }
    rewrite H5. clear H5. apply derEqual in I1'.
    (**由拉格朗日中值定理f '[ ξ'] = (f [x] - f [x0]) / (x - x0)可推目标
       f [x] = f [x0] + f '[ ξ'] * (x - x0)**)
    rewrite I1'. field. lra.
    
    (**(0 < n)%nat**)
  - assert (H3 : ∃ F, F = λ m, \{\ λ t y,
    y = f[x] - (Σ \{\ λ k v, v = (dN f k)[t] /
      (INR (k!)) * (x - t)^^k \}\ m) \}\).
    { exists (λ m, \{\ λ t y, y =
      f[x] - (Σ \{\ λ k v, v = (dN f k)[t] /
      (INR (k!)) * (x - t)^^k \}\ m) \}\).
      reflexivity. }
    destruct H3 as [F H3].
    (**构造一个辅助函数F(t)= f [x] - Σ\{\ λ k v, v = (dN f k) [t] 
                           / INR (k !) * (x - t) ^^ k \}\ m \}\
     **)
    assert (H4 : ∀ m, Function (F m)).
    { intros m. rewrite H3. intros x' y z I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption. }
    assert (H5 : ∀ t m, (F m)[t] = f[x] -
    (Σ \{\ λ k v, v = (dN f k)[t] /
    (INR (k!)) * (x - t)^^k \}\ m)).
    { intros t m. apply f_x; auto.
      rewrite H3. apply AxiomII'.
      reflexivity. }
    assert (H6 : ∀ x t, Function
    \{\ λ k v, v = (dN f k) [t]
    / INR (k !) * (x - t)^^k \}\).
    { intros x' x2 x1 y1 z1 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption. }
    assert (H6' : ∀ x k, Function
    \{\ λ t v, v = (dN f (S k)) [t]
    / INR ((S k) !) * (x - t)^^(S k) \}\).
    { intros x' x2 x1 y1 z1 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption. }
    assert (H7 : ∀ x t k,
    \{\ λ k v, v = (dN f k) [t]
    / INR (k !) * (x - t)^^k \}\[k]
    = (dN f k) [t] / INR (k !) * (x - t)^^k).
    { intros x' x1 k.
      apply f_x; try apply H6.
      apply AxiomII'. reflexivity. }
    assert (H7' : ∀ x t k,
    \{\ λ t v, v = (dN f (S k)) [t]
    / INR ((S k)!) * (x - t)^^(S k) \}\[t]
    = (dN f (S k)) [t] / INR ((S k) !) * (x - t)^^(S k)).
    { intros x' x1 k.
      apply f_x; try apply H6'.
      apply AxiomII'. reflexivity. }
    assert (H8 : ∀ k, Function \{\ λ t y,
      y = Σ \{\ λ k1 v, v = (dN f k1)[t] /
      (INR (k1!)) * (x - t)^^k1 \}\ k \}\).
    { intros n'. intros x' y' z' I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption. }  
    assert (H9 : ∀ k t, \{\ λ t y, y =
      Σ \{\ λ k1 v, v = (dN f k1)[t] /
      (INR (k1!)) * (x - t)^^k1 \}\ k \}\ [t]
       = Σ \{\ λ k1 v, v = (dN f k1)[t] /
        (INR (k1!)) * (x - t)^^k1 \}\ k).
    { intros n' t. apply f_x;
      try apply H8.
      apply AxiomII'. reflexivity. } 
  (**同样构造一个辅助函数G(t) = (x - t)^(n + 1)**)
  assert (J1:∃G, G = \{\ λ t y, y = (x - t)^^(S n) \}\).
  { exists \{\ λ t y, y = (x - t)^^(S n) \}\. auto. }
  destruct J1 as [G J1].
  assert (J2: Function G).
  { red. intros. rewrite J1 in H10, H11.
    applyAxiomII H10. applyAxiomII H11.
    destruct H10 as [x' [y' [H10 H10']]].
    destruct H11 as [x''[y''[H11 H11']]].
    apply ProdEqual in H10. apply ProdEqual in H11.
    destruct H10 as [H10 H10'']. destruct H11 as [H11 H11''].
    rewrite H10''. rewrite H11''. rewrite H10'. rewrite H11'.
    rewrite <- H10.
    rewrite <- H11. auto. }
  assert (J3:∀ t, G[t] = (x - t) ^^ (S n)).
  { intros. rewrite J1. apply f_x. rewrite <- J1; auto.     
    apply AxiomII. exists t, ((x - t) ^^ (S n)).
    split; auto. }  
  (**n+1项求和等于前n项+(第n+1)项**)
  assert (I1 : ∀(k : nat), \{\ λ t1 y1, y1 = Σ \{\ λ n2 v,
        v = (dN f n2) [t1] / INR (n2 !)
        * (x - t1) ^^ n2 \}\ (S k) \}\ =
        \{\ λ t2 y2, y2 = \{\ λ t1 y1, y1 =
          Σ \{\ λ n2 v,
          v = (dN f n2) [t1] / INR (n2 !)
          * (x - t1) ^^ n2 \}\ k \}\[t2] +
        \{\ λ t1 y1, y1 = (dN f (S k)) [t1]
          / INR ((S k) !) * (x - t1) ^^ (S k) \}\[t2]
        \}\).
  { intros. apply AxiomI. intros [x1' y1'].
    split; intros R1.
    - applyAxiomII' R1. apply AxiomII'. rewrite H9.
      rewrite H7 in R1. rewrite H7'. assumption.
    - apply -> AxiomII' in R1.
      lazy beta in R1. apply AxiomII'.
      simpl. rewrite H7. rewrite H9 in R1. rewrite H7' in R1.
      assumption. }
  (**F的一阶导数**) 
  assert (I2: ∀t, x0 < t < x -> 
           [t, (- (dN f (n+1))[t] / INR (n!) * (x - t) ^^n)] 
             ∈ (dN (F n) 1)). 
  { intros.
    assert(E1 : ∀x' : R,\{\ λ t1 y,y = 1 / INR (n !) * 
            (x - t1) ^^ n \}\ [x'] = 
            1 / INR (n !) * (x - x') ^^ n ). 
    { intros z. Function_ass. }
     (**F(t)的第n项也就是最后一项
     ((dN f n) [t1] / INR (n !) * (x - t1) ^^ n)求导的结果**)
    assert(E2: [t, (dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n - (dN f (n - 1 + 1)) [t] / INR ((n - 1) !) * (x - t) ^^ (n - 1)] ∈ dN \{\ λ t1 y ,y = (dN f n) [t1] / INR (n !) * (x - t1) ^^ n \}\ 1).
    { apply AxiomII'. 
      assert(H11: t ∈ dom[(dN f (S n))]).
      { apply H1'. apply AxiomII. applyAxiomII H2.
        applyAxiomII H2'. lra. }
      apply x_fx in H11; [|apply Lemma5_16; auto].
      simpl in H11. applyAxiomII' H11. 
      assert(H12: \{\ λ x y,derivative (dN f n) x y \}\ [t] = 
      (dN f (S n))[t]). { simpl. auto.  }
      rewrite H12 in H11.  
      assert(derivable (dN f n) t).
      { red. exists ((dN f (S n)) [t]); auto. }
      assert(derivative \{\ λ t1 y, y = 1 / INR (n !) * (x - t1) ^^ n \}\ t (-1 * / INR ((n -1) !) * (x - t) ^^ (n -1))).
      { assert (derivative \{\ λ t1 y, y = (t1 - x) ^^ n \}\ 
             t ( INR (n) * (t - x) ^^ (n - 1))).
        apply (Lemma5_4 x t n). 
        assert (derivative \{\ λ t1 y, y = (1 / INR (n !) *
              (- 1)^^(n)) * (t1 - x) ^^ n \}\ t
             ((1 / INR (n !) * (- 1)^^(n)) * 
             INR (n) * (t - x) ^^ (n - 1))).
        apply (Lemma5_5 x (1 / INR (n !) *(- 1)^^(n)) t n).
        assert (\{\ λ t1 y, y = 1 / INR (n !) * (-1) ^^ n *
               (t1 - x) ^^ n \}\  = 
       \{\ λ t1 y, y = 1 / INR (n !) * (x - t1) ^^ n \}\).
        { apply AxiomI. split; intros.
          - applyAxiomII H16.
            destruct H16 as [x'[y'[H16 H16']]].
            apply AxiomII. exists x', y'.
            split; auto. rewrite H16'. 
            rewrite Rmult_assoc. rewrite Rmult_comm.
            rewrite (Lemma_pow4 (-1) (x' - x)(n)).
            assert ((-1 * (x' - x)) = (x - x')).
            rewrite <- Ropp_minus_distr'. lra. rewrite H17.
            rewrite Rmult_comm. auto. 
          - applyAxiomII H16.
            destruct H16 as [x'[y'[H16 H16']]].
            apply AxiomII. exists x', y'.
            split; auto. rewrite H16'.  
            symmetry. rewrite Rmult_assoc. rewrite Rmult_comm.
            rewrite (Lemma_pow4 (-1) (x' - x)(n)).
            assert ((-1 * (x' - x)) = (x - x')).
            rewrite <- Ropp_minus_distr'. lra. rewrite H17.
            rewrite Rmult_comm.
            auto. }
         rewrite H16 in H15. clear H16.  
         assert ((1 / INR (n !) * (-1) ^^ n * INR n * (t - x) ^^ (n - 1)) =  
            (-1 * / INR ((n - 1) !) * (x - t) ^^ (n - 1))).
         { assert ( (-1) ^^ n = -1 * (-1)^^(n - 1)).
           { cut (-1 = (-1)^^1). intros. 
             assert (-1 * (-1) ^^ (n - 1) = (-1) ^^ 1
             * (-1) ^^ (n - 1)). 
             apply (Rmult_eq_compat_r ((-1) ^^ (n - 1)) (-1)
                     ((-1) ^^ 1)). lra. 
             rewrite H17.  
             rewrite <- (Lemma_pow1 (-1) (1) (n - 1)). 
             cut ((1 + (n - 1))%nat = n). intros.
             rewrite H18. auto. simpl. 
             rewrite <- (Nat.add_1_r (n-1)). 
             apply Nat.sub_add.
             apply L1. simpl. lra. }
           rewrite H16. clear H16. 
           rewrite <- Rmult_assoc.
           rewrite Rmult_assoc. rewrite Rmult_assoc. 
           assert (((-1) ^^ (n - 1) * (INR n * (t - x) ^^ (n - 1))) = INR n * (x - t) ^^ (n - 1)).
           { rewrite Rmult_comm.
             assert ((t - x) ^^ (n - 1) * (-1) ^^ (n - 1) = 
                      (x - t) ^^ (n - 1)). 
             rewrite (Lemma_pow4 (t - x) (-1) (n - 1)).
             auto. 
             assert (((t - x) * -1) = (x - t)). field.
             rewrite H16. auto.
             rewrite <- H16. rewrite <- Rmult_assoc. auto. }
           rewrite H16. clear H16. rewrite <- Rmult_assoc.
           assert (1 / INR (n !) * -1 * INR n =
                   -1 * / INR ((n - 1) !)).
           { rewrite Rmult_assoc. rewrite Rmult_comm.
             assert (INR n * (1 / INR (n !)) = 
                     / INR ((n - 1) !)).
             { rewrite Rmult_comm. 
               apply (Rmult_eq_reg_r (1/INR n)).
               rewrite Rmult_assoc. 
               assert ((INR n * (1 / INR n)) = 1).
               { unfold Rdiv. rewrite Rmult_comm. 
                  rewrite Rmult_1_l. 
                  apply Rinv_l. apply not_0_INR.   
                 intro. rewrite H16 in L1. inversion L1. }
               rewrite H16. clear H16. rewrite Rmult_1_r.
               unfold Rdiv. 
               assert (/ INR ((n - 1) !) * (1 * / INR n) =
                    1 * / INR ((n - 1) !) * / INR n).
               { field. split.  
                 apply not_0_INR. intro. rewrite H16 in L1.
                 inversion L1.
                 apply not_0_INR.
                 pose proof (Lemma6_3_1 (n - 1)).
                 intro. rewrite H17 in H16.
                 inversion H16. }
               rewrite H16. clear H16.
               rewrite Rmult_1_l. rewrite Rmult_1_l.     
               rewrite <- Rinv_mult_distr.
               assert (INR (n !) = (INR ((n - 1) !) * INR n)).
               { rewrite <- mult_INR. 
                 apply Lemma6_3_6; auto. }
               rewrite H16; auto. 
               apply not_0_INR.
               pose proof (Lemma6_3_1 (n-1)). intro.
               rewrite H17 in H16. inversion H16.
               apply not_0_INR.
               intro. 
               rewrite H16 in L1. inversion L1.
               unfold Rdiv. rewrite Rmult_1_l.
               apply Rinv_neq_0_compat.
               apply not_0_INR. intro. rewrite H16 in L1.
               inversion L1. } 
             rewrite Rmult_assoc.
             rewrite H16. auto. }
           rewrite H16. auto. }
         rewrite H16 in H15;
         auto. }                                       
      assert(derivable \{\ λ t1 y,y = 1 / INR (n !) * (x - t1) ^^ n \}\ t). 
      { red. 
        exists  (-1 * / INR ((n - 1) !) * (x - t) ^^ (n - 1)). auto. } 
      unfold Rdiv. 
      apply derEqual in H11 as H12'.
      cut((n + 1)%nat = S n). intros. 
      rewrite H16. rewrite <- H12'.
      unfold Rminus.
      rewrite Rmult_assoc. 
      rewrite Ropp_mult_distr_r. 
      assert(H17: \{\ λ t1 y,y = 1 / INR (n !) * (x - t1) ^^ n \}\[t] = / INR (n !) * (x + - t) ^^ n).
      { Function_ass. unfold Rminus. lra. } rewrite Rmult_assoc.
      rewrite <- H17. 
      apply derEqual in H14 as H14'.
      replace ((/ INR ((n - 1) !) * - (x + - t) ^^ (n - 1))) with (-1 * / INR ((n - 1) !) * (x - t) ^^ (n - 1)).
       rewrite <- H14'. 
      assert(\{\ λ t1 y,y = (dN f n) [t1] * / INR (n !) * (x + - t1) ^^ n \}\  = \{\ λ t1 y, y = (dN f n) [t1] * \{\ λ t1 y,y = 1 / INR (n !) * (x - t1) ^^ n \}\[t1] \}\).
      { apply AxiomI. 
        split; intros H15'. 
        - applyAxiomII H15'. 
          destruct H15' as [x'[y'[H15' H15'']]].
          apply AxiomII. exists x', y'. split; auto.
          rewrite E1.  unfold Rminus. lra.
        - applyAxiomII H15'. 
          destruct H15' as [x'[y'[H15' H15'']]].
          apply AxiomII. rewrite E1 in H15''. 
          exists x', y'. split; auto. unfold Rminus in H15''.
          lra. }
      rewrite H18. 
      assert((dN f (n - 1 + 1)) [t] = (dN f n) [t]).
      { cut((n - 1 + 1)%nat = n%nat). intros.
        rewrite H19; auto. 
        apply Nat.sub_add. 
        apply L1.  } 
      rewrite  H19.
      rewrite (Rmult_comm (dN f n) [t] _).
      apply (Theorem5_5'' (dN f n) \{\ λ t2 y0,y0 = 1 / INR (n !) * (x - t2) ^^ n \}\ t); auto. 
      unfold Rminus. lra. rewrite Nat.add_1_r; auto.  } 

    (**n>=1时,求F的n-1项和的导数**)
    assert (∀(k : nat) (t :R) , (k <= n - 1)%nat -> x0 < t < x -> 
           [t, ( (dN f (k+1))[t] / INR (k!) * (x - t) ^^k)] ∈
            (dN (\{\ λ t y, y =Σ \{\λ k v, v = (dN f k) [t] 
                     / INR (k !) *(x - t) ^^ k \}\ k \}\) 1)).
    { intros. induction k.         
     - assert(t0 ∈ dom[ dN f 1]). 
       { pose proof (H1 1%nat).
         cut ((1 <= n)%nat); intros.
         apply H13 in H14. destruct H14 as [H14 H14'].
         apply H14. apply AxiomII. applyAxiomII H2. 
         applyAxiomII H2'. lra.
         apply L1. }    (**n>=1时,求n-1项和的导数**)
       apply x_fx in H13. 
       applyAxiomII' H13. simpl. 
       apply AxiomII'. 
       assert( \{\ λ t1 y,y =
       \{\ λ(k : nat)(v : R),v = (dN f k) [t1] / INR (k !) * (x - t1) ^^ k \}\
            [0%nat] \}\ = \{\λ t1 y, y = f[t1] \}\ ).
       { apply AxiomI; split; intros. 
         - applyAxiomII H14. 
           destruct H14 as [x0'[y0'[H14 H14']]].
           assert (\{\λ k v, v = (dN f k) [x0'] / INR (k !) * 
                           (x - x0') ^^ k \}\[0%nat] = f [x0']).
           { Function_ass. simpl. lra. }
           rewrite H15 in H14'. clear H15. 
           apply AxiomII. exists x0', y0'. tauto.
         - applyAxiomII H14. 
           destruct H14 as [x0'[y0'[H14 H14']]].
           apply AxiomII. exists x0',y0'. split; auto. 
           assert (\{\λ k v, v = (dN f k) [x0'] / INR (k !) * 
                           (x - x0') ^^ k \}\[0%nat] = f [x0']).
           { Function_ass. simpl. lra. }
           rewrite H15. auto. }
      rewrite H14.
      assert(\{\ λ x1 y,derivative f x1 y \}\ [t0] / 1 * 1 = \{\ λ x y,derivative f x y \}\ [t0]).
      { field. } 
      rewrite H15. 
      apply derEqual in H13 as H13'. 
      rewrite <- H13'. rewrite <- H13' in H13. 
      clear H13' H14 H15. 
      red in H13. red. split. QED_function. 
      destruct H13 as [H13[H14 H15]].
      red in H15.
      split. destruct H14 as [δ'].
      exists δ'. split. tauto. 
      intros z H19. apply AxiomII. exists f[z].
      apply AxiomII'; auto. red.
      destruct H15 as [H15 [δ' [H16 [H17 H18]]]].
      split. QED_function. 
      assert(∀x : R, \{\ λ t1 y0,y0 = f [t1] \}\[x] = f[x]).
      { intros. Function_ass. }
      exists δ'. 
      split; auto. split.
      intros z H20. apply AxiomII. exists ((f[z] - f[t0])/(z - t0)).
      apply AxiomII'. rewrite H19. rewrite H19.
      auto. intros. apply H18 in H20.
      destruct H20 as [δ[[H20 H21]H22]].
      exists δ. split; auto. intros. 
      apply H22 in H23. 
      assert(\{\ λ x y,y = (f [x] - f [t0]) / (x - t0) \}\ [x1]  = (f [x1] - f [t0]) / (x1 - t0)). { Function_ass. }
      rewrite H24 in H23. 
      assert(\{\ λ x2 y,y = (\{\ λ t1 y0,y0 = f [t1] \}\ [x2] - \{\ λ t1 y0,y0 = f [t1] \}\ [t0]) / (x2 - t0) \}\ [x1] = (f [x1] - f [t0]) / (x1 - t0)).
      { apply f_x. QED_function. 
        apply AxiomII'. rewrite H19. rewrite H19. auto. }
      rewrite H25. auto. apply Lemma5_16; auto.

      - assert([t0, (dN f (S k + 1)) [t0] / INR ((S k) !) * (x - t0) ^^ S k - (dN f (S k)) [t0] / INR (k !) * (x - t0) ^^ k] ∈ dN
    \{\
    λ t1 y ,y = (dN f (S k)) [t1] / INR ((S k)!) * (x - t1) ^^ S k \}\ 1).
    { apply AxiomII'. 
      assert(t0 ∈ dom[(dN f (S k +1))]).
      { pose proof (H1 (S k + 1)%nat).
         cut ( (S k + 1 <= n)%nat); intros.
         apply H13 in H14. destruct H14 as [H14 H14'].
         apply H14. apply AxiomII. applyAxiomII H2. 
         applyAxiomII H2'. lra. 
         apply Peano.le_n_S in H11.
         replace (S k + 1)%nat with (S (S k)).
         replace n with (S (n - 1)). apply H11.
         rewrite <- (Nat.add_1_r (n - 1)). 
         apply Nat.sub_add. 
         apply L1.
         rewrite <- (Nat.add_1_r (S k)). auto. }
      apply x_fx in H13; [|apply Lemma5_16; auto].
      simpl in H13. applyAxiomII' H13. 
      assert(\{\ λ x y,derivative (dN f (k + 1)) x y \}\ [t0] = 
      (dN f (S k + 1))[t0]). { simpl. auto.  }
      rewrite H14 in H13.  
      assert(derivable (dN f (k + 1)) t0).
      { red. exists ((dN f (S k + 1)) [t0]); auto. }
      assert(derivative \{\ λ t1 y, y = 1 / INR ((S k) !) * (x - t1) ^^ S k \}\ t0 (-1 * / INR (k !) * (x - t0) ^^ k)).
      {
      assert (derivative \{\ λ t1 y, y = (t1 - x) ^^ S k \}\ 
             t0 ( INR (S k) * (t0 - x) ^^ (S k - 1))).
     apply (Lemma5_4 x t0 (S k)). 
     assert (derivative \{\ λ t1 y, y = (1 / INR ((S k) !) *
              (- 1)^^(S k)) * (t1 - x) ^^ S k \}\ t0
             ((1 / INR ((S k) !) * (- 1)^^(S k)) * 
             INR (S k) * (t0 - x) ^^ (S k - 1))).
     apply (Lemma5_5 x (1 / INR ((S k) !) *(- 1)^^(S k)) 
             t0 (S k)).
    assert (\{\ λ t1 y, y = 1 / INR ((S k) !) * (-1) ^^ S k *
               (t1 - x) ^^ S k \}\  = 
       \{\ λ t1 y, y = 1 / INR ((S k) !) * (x - t1) ^^ S k \}\).
    { apply AxiomI. split; intros.
      - applyAxiomII H18.
        destruct H18 as [x'[y'[H18 H18']]].
        apply AxiomII. exists x', y'.
        split; auto. rewrite H18'. 
        assert (-1 * (-1) ^^ k = (-1)^^ S k).
        simpl. auto. rewrite H19. clear H19.
        assert ((x' - x) * (x' - x) ^^ k = (x' - x) ^^ S k).
        simpl. auto. rewrite H19. clear H19.
        rewrite Rmult_assoc. rewrite Rmult_comm.
        rewrite (Lemma_pow4 (-1) (x' - x)(S k)).
        assert ((-1 * (x' - x)) = (x - x')).
        rewrite <- Ropp_minus_distr'. lra. rewrite H19.
        rewrite Rmult_comm. 
        assert (1 / INR (k ! + k * k !) = 1 / INR ((S k) !)).
        simpl. auto. rewrite H20. auto.
      - applyAxiomII H18.
        destruct H18 as [x'[y'[H18 H18']]].
        apply AxiomII. exists x', y'.
        split; auto. rewrite H18'.  
        assert ((x - x') * (x - x') ^^ k = (x - x') ^^ S k).
        simpl. auto. rewrite H19. clear H19.
        symmetry. rewrite Rmult_assoc. rewrite Rmult_comm.
        rewrite (Lemma_pow4 (-1) (x' - x)(S k)).
        assert ((-1 * (x' - x)) = (x - x')).
        rewrite <- Ropp_minus_distr'. lra. rewrite H19.
        rewrite Rmult_comm.
        assert (1 / INR (k ! + k * k !) = 1 / INR ((S k) !)).
        simpl. auto. rewrite H20. auto. }
    rewrite H18 in H17. clear H18. 
    assert (((-1) ^^ S k * INR (S k) *(t0 - x) ^^ (S k - 1)) =  
            (- INR (k + 1) * (x - t0) ^^ k)).
    { assert ((-1) ^^ S k = (- 1) * (- 1) ^^ k).
      simpl. lra. rewrite H18. clear H18.
      assert ( (t0 - x) ^^ (S k - 1) = (t0 - x) ^^ k) .
      simpl. rewrite Nat.sub_0_r. auto.
      rewrite H18. clear H18. 
      assert (-1 * (-1) ^^ k * INR (S k) * (t0 - x) ^^ k
             = -1 * INR (S k) * ((-1) ^^ k * (t0 - x) ^^ k)).
      field. 
      rewrite H18. clear H18.
      rewrite (Lemma_pow4 (-1) (t0 - x) k). 
      assert ((-1 * (t0 - x)) = (x - t0)).
      rewrite <- Ropp_minus_distr'. lra. rewrite H18.
      assert (INR (S k) = INR (k + 1)).
      rewrite <- Nat.add_1_l. auto. rewrite Nat.add_comm. auto.
      rewrite H19. lra. }
    assert ((1 / INR ((S k) !) * (-1) ^^ S k * INR (S k) * 
            (t0 - x) ^^ (S k - 1)) = 
           1 / INR ((S k) !) * (- INR (k + 1) * (x - t0) ^^ k)).
    { rewrite Rmult_assoc. rewrite Rmult_assoc. 
      rewrite Rmult_comm. rewrite Rmult_assoc in H18.
      rewrite H18. symmetry. rewrite Rmult_comm. auto. }
    rewrite H19 in H17. 
    assert ((1 / INR ((S k)!) * (- INR (k+1) * (x - t0) ^^ k))
            = (-1 * 1 / INR (k !) * (x - t0) ^^ k)).
    { rewrite <- Rmult_assoc.
      assert ( 1 / INR ((S k) !) * - INR (k + 1) =
              - 1 / INR (k !)).
      { rewrite Ropp_mult_distr_r_reverse. 
        rewrite (Ropp_eq_compat 
               (1 / INR ((S k) !) * INR (k + 1)) 
               (1 * 1 / INR (k !))). 
        field. intro. pose proof (Lemma6_3_1 k).
        apply lt_0_INR in H21. rewrite H20 in H21.
        lra. rewrite Rmult_1_l.
        apply (Rmult_eq_reg_r (1/INR (k + 1)) 
        (1 / INR ((S k) !) * INR (k + 1)) (1 / INR (k !)) ).
        rewrite Rmult_assoc. 
        assert ((INR (k + 1) * (1 / INR (k + 1))) = 1).
        { unfold Rdiv. rewrite Rmult_comm. rewrite Rmult_1_l. 
          apply Rinv_l. apply not_0_INR.  
          rewrite Nat.add_1_r.
          apply Nat.neq_succ_0. }
        rewrite H20. clear H20. rewrite Rmult_1_r. unfold Rdiv.
        assert (1 * / INR (k !) * (1 * / INR (k + 1)) =
                1 * 1 * / INR (k !) * / INR (k + 1)).
        { field. split. 
          apply not_0_INR. rewrite Nat.add_1_r. 
          apply Nat.neq_succ_0.
          apply not_0_INR.
          pose proof (Lemma6_3_1 k).
          intro. rewrite H21 in H20.
          inversion H20. }
        rewrite H20. clear H20. 
        rewrite Rmult_1_l. rewrite Rmult_1_l. rewrite Rmult_1_l.
        rewrite <- Rinv_mult_distr.   
        assert (INR ((S k) !) = (INR (k !) * INR (k + 1))).
        { rewrite <- mult_INR. 
          simpl. rewrite plus_INR. 
          rewrite mult_INR. rewrite mult_INR.
          rewrite plus_INR. simpl.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r. lra. } 
        rewrite H20. auto.
        apply not_0_INR.
        pose proof (Lemma6_3_1 k). 
        intro. rewrite H21 in H20. inversion H20.
        apply not_0_INR. rewrite Nat.add_1_r. 
        apply Nat.neq_succ_0.
        unfold Rdiv. rewrite Rmult_1_l.
        apply Rinv_neq_0_compat.
        apply not_0_INR. rewrite Nat.add_1_r. 
        apply Nat.neq_succ_0. } 
        rewrite H20. field.
        apply not_0_INR.
        pose proof (Lemma6_3_1 k).
        intro. rewrite H22 in H21. inversion H21.
    }
  rewrite H20 in H17.
  assert ((-1 * 1 / INR (k !) * (x - t0) ^^ k) = (-1 * / INR (k !) * (x - t0) ^^ k)). lra. rewrite H21 in H17. auto.
  }
  assert(derivable \{\ λ t1 y,y = 1 / INR ((S k) !) * (x - t1) ^^ S k \}\ t0). 
  { red. exists ((-1 * / INR (k !) * (x - t0) ^^ k)); auto. }
      unfold Rdiv. 
      apply derEqual in H13 as H14'. rewrite <- H14'.
      unfold Rminus.
      rewrite Rmult_assoc. 
      rewrite Ropp_mult_distr_r. 
      assert(\{\ λ t1 y,y = 1 / INR ((S k) !) * (x - t1) ^^ S k \}\[t0] = / INR ((S k) !) * (x + - t0) ^^ S k).
      { Function_ass. unfold Rminus. lra. } rewrite Rmult_assoc.
      rewrite <- H18.
      apply derEqual in H16 as H16'.
      replace ((/ INR (k !) * - (x + - t0) ^^ k)) with (-1 * / INR (k !) * (x - t0) ^^ k).
       rewrite <- H16'.
      assert(\{\ λ t1 y, y = (dN f (S k)) [t1] * / INR ((S k) !) * (x + - t1) ^^ S k \}\  = \{\ λ t1 y, y = (dN f (k + 1)) [t1] * \{\ λ t1 y,y = 1 / INR ((S k) !) * (x - t1) ^^ S k \}\[t1] \}\).
      {  rewrite <- Nat.add_1_r.
        apply AxiomI.
        assert(∀t1 : R, \{\ λ t2 y0,y0 = 1 / INR ((k + 1) !) * (x - t2) ^^ (k+1) \}\[t1] = 1 / INR ((k+1) !) * (x - t1) ^^ (k+1)).
        { intros z. Function_ass. }
        split; intros H15'. 
        - applyAxiomII H15'. destruct H15' as [x'[y'[H15'' H15']]].
          apply AxiomII. exists x', y'. split; auto.
          rewrite H19.  unfold Rminus.  
          lra.
        - applyAxiomII H15'. destruct H15' as [x'[y'[H15'' H15']]].
          apply AxiomII. rewrite H19 in H15'. 
          exists x', y'. split; auto. unfold Rminus in H15'. lra. }
      rewrite H19. 
      assert((dN f (S k)) [t0] = (dN f (k + 1)) [t0]).
      rewrite Nat.add_1_r; auto. rewrite H20.
      rewrite (Rmult_comm (dN f (k + 1)) [t0] _).
      apply (Theorem5_5'' (dN f (k + 1)) \{\ λ t2 y0,y0 = 1 / INR ((S k) !) * (x - t2) ^^ S k \}\ t0); auto. 
      unfold Rminus. lra. } 
    rewrite I1.  
    assert(∃y1:R, y1 = (dN f (k + 1)) [t0] / INR (k !) * (x - t0) ^^ k).
    { exists ((dN f (k + 1)) [t0] / INR (k !) * (x - t0) ^^ k); auto. }
    destruct H14 as [y1]. rewrite <- H14 in IHk.
    rewrite Nat.add_1_r in H14.
    rewrite <- H14 in H13.  
    assert(∃y2:R, y2 = (dN f (S k + 1)) [t0] / INR ((S k) !) * (x - t0) ^^ S k). exists ((dN f (S k + 1)) [t0] / INR ((S k) !) * (x - t0) ^^ S k); auto. destruct H15 as [y2].
    rewrite <- H15. rewrite <- H15 in H13.
    assert(y2 = y1 + (y2 - y1)). lra. 
    rewrite H16. apply Lemma5_18'; auto. 
    apply IHk. apply le_Sn_le. auto. } 
    (**引入OK**)
    pose proof (H11 (n-1)%nat).  
    clear H11. 
    
    (**F的n项的导数=前n-1项导数+第n项导数**)
    assert([t,(dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n] ∈ dN
           \{\ λ t0 y,y = Σ \{\  λ(k : nat)(v : R),
           v = (dN f k) [t0] / INR (k !) * (x - t0) ^^ k \}\ n \}\ 1).
   
    { clear I1.
      assert (I1 : \{\ λ t1 y1, y1 = Σ \{\ λ n2 v,
      v = (dN f n2) [t1] / INR (n2 !) * (x - t1) ^^ n2 \}\ n \}\ =
      \{\ λ t2 y2, y2 = \{\ λ t1 y1, y1 = Σ \{\ λ n2 v, 
      v = (dN f n2) [t1] / INR (n2 !) * (x - t1) ^^ n2 \}\ (n-1) \}\
      [t2] + \{\ λ t1 y1, y1 = (dN f n) [t1] / INR (n !) * 
      (x - t1) ^^ n \}\[t2] \}\).
      { apply AxiomI. 
        assert(∀x' : R, \{\ λ t1 y1,y1 = (dN f n) [t1] / INR (n !) * (x - t1) ^^ n \}\ [x'] = (dN f n) [x'] / INR (n !) * (x - x') ^^ n).
        { intros z. Function_ass. } 
        split; intros.
        - applyAxiomII H13. destruct H13 as [x'[y'[H13' H13'']]].
          apply AxiomII. exists x', y'. split; auto.
          rewrite H9. rewrite H11.
          rewrite (Lemma_6_3_7 n \{\ λ(k1 : nat)(v : R),v = (dN f k1) [x'] / INR (k1 !) * (x - x') ^^ k1 \}\) in H13''; auto.
          rewrite H13''. rewrite H7; auto. 
        - applyAxiomII H13. destruct H13 as [x'[y'[H13' H13'']]].
          apply AxiomII. exists x', y'. split; auto.
          rewrite H9 in H13''. rewrite H11 in H13''. 
          rewrite (Lemma_6_3_7 n \{\ λ(n2 : nat)(v : R),v = (dN f n2) [x'] / INR (n2 !) * (x - x') ^^ n2 \}\); auto.
          rewrite H7; auto.  }  
     rewrite I1. clear I1. 
     cut ((n - 1 <= n - 1)%nat). intros.
     apply (H12 t) in H11; auto. clear H12.
     cut((n - 1 + 1)%nat = n); intros.
     rewrite H12 in H11. rewrite H12 in E2.
     assert((dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n = (dN f n) [t] / INR ((n - 1) !) * (x - t) ^^ (n - 1) + ((dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n -
     (dN f n) [t] / INR ((n - 1) !) * (x - t) ^^ (n - 1))). lra.
     rewrite H13. apply Lemma5_18'; auto.
     QED_function. apply Nat.sub_add. apply L1. auto. }
     apply AxiomII'. applyAxiomII' H11.
     rewrite H3. apply derEqual in H11 as H11'.
     assert (N1: derivative \{\ λ t0 y, y = f [x]\}\ t 0).
     { apply Lemma5_12. }
     assert (N1': derivable \{\ λ t0 y, y = f [x]\}\ t).
     { red. exists 0. auto. }
     assert (N2: derivable \{\ λ t0 y, y =Σ\{\ λ k v, v =
                 (dN f k) [t0] / INR (k !) * (x - t0) ^^ k \}\
                  n \}\ t).
     { red. 
       exists ((dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n).
       auto. }
     apply (Theorem5_4_2 (\{\ λ t0 y, y = f [x] \}\)
            (\{\ λ t0 y, y =Σ\{\ λ k v, v =
                 (dN f k) [t0] / INR (k !) * (x - t0) ^^ k \}\
                  n \}\ ) t) in N1'; auto.
     assert (\{\ λ x0 y, y = 
             \{\ λ t0 y0, y0 = f [x] \}\ [x0] - 
             \{\ λ t0 y0, y0 = Σ \{\ λ k v, v = (dN f k) [t0] 
                 / INR (k !) * (x - t0) ^^ k \}\ n \}\ [x0] \}\
             = \{\ λ t0 y, y = f [x] - Σ \{\ λ k v, v = 
              (dN f k) [t0] / INR (k !) * (x - t0) ^^ k \}\ n \}\).
     { apply AxiomI; split; intros. 
       - applyAxiomII H13. destruct H13 as [x0'[y0'[H13 H13']]].
         apply AxiomII. exists x0', y0'. split; auto.
         assert (\{\ λ t0 y0 : R,y0 = f [x] \}\ [x0'] = f [x]).
         apply f_x. QED_function. apply AxiomII'. auto.
         rewrite H14 in H13'. clear H14.
         assert (\{\ λ t0 y0, y0 = Σ \{\ λ k v,v =
                (dN f k) [t0] / INR (k !) *
                 (x - t0) ^^ k \}\ n \}\ [x0'] = 
                 Σ \{\ λ k v,v = (dN f k) [x0'] / INR (k !) 
                 * (x - x0') ^^ k \}\ n).
         { apply f_x.
           QED_function.
           apply AxiomII'. auto. }
         rewrite H14 in H13'. auto.
        - applyAxiomII H13. destruct H13 as [x0'[y0'[H13 H13']]].
         apply AxiomII. exists x0', y0'. split; auto.
         assert (\{\ λ t0 y0 : R,y0 = f [x] \}\ [x0'] = f [x]).
         apply f_x. QED_function. apply AxiomII'. auto.
         rewrite H14. clear H14.
         assert (\{\ λ t0 y0, y0 = Σ \{\ λ k v,v =
                (dN f k) [t0] / INR (k !) *
                 (x - t0) ^^ k \}\ n \}\ [x0'] = 
                 Σ \{\ λ k v,v = (dN f k) [x0'] / INR (k !) 
                 * (x - x0') ^^ k \}\ n).
         { apply f_x.
           QED_function.
           apply AxiomII'. auto. }
         rewrite H14. auto. }
         rewrite H13 in N1'. clear H13.
     apply derEqual in N1 as N1''. rewrite N1'' in N1'.
     rewrite H11' in N1'. 
     replace (- (dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n)
     with (0 - (dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n).
     auto. field. pose proof (Lemma6_3_1 n).
     apply not_0_INR. intro. rewrite H14 in H13. inversion H13. }
  (**证毕F的一阶导数**) 
  
  (**F(t)在(x0,x)上可导**)
  assert (Q1: (∀ t, x0 < t < x -> derivable (F n) t)).
  { intros.  
    apply I2 in H10. applyAxiomII' H10. red. 
    exists (- (dN f (n + 1)) [t] / INR (n !) * (x - t) ^^ n).
    auto. }
  (**F在[x0,x]上连续**)  
   assert (P2: ∀k, (k <= n)%nat -> ContinuousClose (F k) x0 x). 
  { intros. applyAxiomII H2. applyAxiomII H2'. 
    destruct H2 as [H2 H2''']. destruct H2' as [H2' H2''''].
    induction k as [| k IHk].  
    - assert (Q2 :\{\ λ t y, y = f [x] - f [t] \}\ =
                   \{\ λ t y, y = f [x] \}\ \- 
                   \{\ λ t y, y =f [t] \}\).
      { apply AxiomI. split; intros. applyAxiomII H11.
        destruct H11 as [x0'[y0'[H11 H11']]].
        apply AxiomII. exists x0',y0'. split; auto. split. 
        apply AxiomII. exists f [x]. apply AxiomII'.
        auto. split. apply AxiomII. exists f[x0']. 
        apply AxiomII'. auto.
        assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
        apply f_x. red. intros. applyAxiomII' H12.
        applyAxiomII' H13. rewrite H12; auto.
        apply AxiomII'. auto. rewrite H12. clear H12.
        assert (\{\ λ t y, y = f [t] \}\ [x0'] = f [x0']).
        apply f_x. red. intros. applyAxiomII' H12.
        applyAxiomII' H13. rewrite H12; auto.
        apply AxiomII'. auto. rewrite H12. clear H12.
        auto.
        applyAxiomII H11. 
        destruct H11 as [x0'[y0'[H11[H11'[H11'' H11''']]]]].
        assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
        apply f_x. red. intros. applyAxiomII' H12.
        applyAxiomII' H13. rewrite H12; auto.
        apply AxiomII'. auto. rewrite H12 in H11'''. clear H12.
        assert (\{\ λ t y, y = f [t] \}\ [x0'] = f [x0']).
        apply f_x. red. intros. applyAxiomII' H12.
        applyAxiomII' H13. rewrite H12; auto.
        apply AxiomII'. auto. rewrite H12 in H11'''.
        clear H12. apply AxiomII. exists x0',y0'. auto. } 
      pose proof (H1 0%nat). pose proof H10 as H10''.
      apply H11 in H10. clear H11.
      destruct H10 as [H10 H10']. simpl in H10'. 
      rewrite H3. simpl.
      assert( \{\ λ t y, y = f [x] - \{\ λ k v, v = 
      (dN f k) [t] / INR (k !) * (x - t) ^^ k \}\
      [0%nat] \}\ = \{\ λ t y, y = f [x] - f[t] \}\ ).
      { apply AxiomI; split; intros. 
        - applyAxiomII H11. 
          destruct H11 as [x0'[y0'[H11 H11']]].
          assert (\{\λ k v, v = (dN f k) [x0'] / INR (k !) * 
                  (x - x0') ^^ k \}\[0%nat] = f [x0']).
          { apply f_x. red. intros.
            applyAxiomII' H12. applyAxiomII' H13.
            rewrite H12; auto. apply AxiomII'. simpl. lra. }
            rewrite H12 in H11'. clear H12. 
            apply AxiomII. exists x0', y0'. tauto.
        - applyAxiomII H11. 
          destruct H11 as [x0'[y0'[H11 H11']]].
          apply AxiomII. exists x0',y0'. split; auto. 
          assert (\{\λ k v, v = (dN f k) [x0'] / INR (k !) * 
                   (x - x0') ^^ k \}\[0%nat] = f [x0']).
          { apply f_x. red. intros.
            applyAxiomII' H12. applyAxiomII' H13.
            rewrite H12; auto. apply AxiomII'. simpl. lra. }
            rewrite H12. auto. } 
       rewrite H11. 
       apply (Lemma6_10_3 f a b x0 x); auto. apply AxiomII. 
       lra. apply AxiomII. lra. 
    - rewrite H3. 
      assert (\{\ λ t y, y = f [x] - Σ \{\ λ k0 v, v =
      (dN f k0) [t] / INR (k0 !) * (x - t) ^^ k0 \}\ (S k) \}\
      = \{\ λ t y, y = f [x] \}\ \-  
        \{\ λ t y, y = Σ \{\ λ k0 v, v = (dN f k0) [t] / 
            INR (k0 !) * (x - t) ^^ k0 \}\ (S k) \}\).
      { apply AxiomI. split; intros. 
        - applyAxiomII H11.
          destruct H11 as [x0'[y0'[H11 H11']]].
          apply AxiomII. exists x0',y0'. split; auto. split. 
          apply AxiomII. exists f [x]. apply AxiomII'.
          auto. split. apply AxiomII. 
          exists (Σ \{\ λ k0 v, v = (dN f k0) [x0'] /
                 INR (k0 !) * (x - x0') ^^ k0 \}\(S k)). 
          apply AxiomII'. auto.
          assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
          apply f_x. red. intros. applyAxiomII' H12.
          applyAxiomII' H13. rewrite H12; auto.
          apply AxiomII'. auto. rewrite H12. clear H12.
          assert (\{\ λ t y, y = Σ \{\ λ k0 v, 
           v = (dN f k0) [t] / INR (k0 !) * (x - t) ^^ k0 \}\
           (S k) \}\ [x0'] = Σ \{\ λ k0 v, v = (dN f k0) [x0'] 
                       / INR (k0 !) * (x - x0') ^^ k0 \}\(S k)).
          { apply f_x. red. intros. applyAxiomII' H12.
            applyAxiomII' H13. rewrite H12; auto.
            apply AxiomII'. auto. } 
          rewrite H12. clear H12. auto.
        - applyAxiomII H11. 
          destruct H11 as [x0'[y0'[H11[H11'[H11'' H11''']]]]].
          assert (\{\ λ t y,y = f [x] \}\[x0'] = f[x]).
          apply f_x. red. intros. applyAxiomII' H12.
          applyAxiomII' H13. rewrite H12; auto.
          apply AxiomII'. auto. rewrite H12 in H11'''. 
          clear H12.
          assert (\{\ λ t y, y = 
                     Σ \{\ λ k0 v,v = (dN f k0) [t] / 
                     INR (k0 !) * (x - t) ^^ k0 \}\ k 
                     + \{\ λ k0 v, v = (dN f k0) [t] / 
                INR (k0 !) * (x - t) ^^ k0 \}\ [ S k] \}\ [x0'] 
                      = Σ \{\ λ k0 v,v = (dN f k0) [x0'] / 
                     INR (k0 !) * (x - x0') ^^ k0 \}\ k 
                     + \{\ λ k0 v, v = (dN f k0) [x0'] / 
                INR (k0 !) * (x - x0') ^^ k0 \}\ [ S k]).
          { apply f_x. red. intros. applyAxiomII' H12.
            applyAxiomII' H13. rewrite H12; auto.
            apply AxiomII'. auto. }
          rewrite H12 in H11'''.
          clear H12. apply AxiomII. exists x0',y0'.
          split; auto. }
          rewrite H11. apply Lemma6_10_4.
      + apply Lemma6_10_5.
      + pose proof (I1 k) as I1'. rewrite I1'. 
        clear I1'. clear H11.
        assert (\{\ λ t2 y2, y2 = 
                 \{\ λ t1 y1, y1 = Σ \{\ λ n2 v,v =
                 (dN f n2) [t1] / INR (n2 !) * (x - t1) ^^ n2 
                 \}\ k \}\ [t2] +  \{\ λ t1 y1, y1 = 
                 (dN f (S k)) [t1] / INR ((S k) !) * (x - t1)
                  ^^ S k \}\[t2] \}\ =
                 \{\ λ t2 y2, y2 = \{\ λ t1 y1, y1 = 
                 Σ \{\ λ n2 v,v = (dN f n2) [t1] / INR (n2 !) 
                 * (x - t1) ^^ n2 \}\ k \}\ [t2] \}\ \+ 
                 \{\ λ t2 y2, y2 = \{\ λ t1 y1, y1 = 
                 (dN f (S k)) [t1] / 
                 INR ((S k) !) * (x - t1) ^^ S k \}\[t2] \}\).
         { apply AxiomI. split;intros.
           - apply AxiomII. applyAxiomII H11. 
             destruct H11 as [x'[y'[H11 H12]]].
             exists x', y'. split; auto. split.
             apply AxiomII.
             exists (\{\ λ t1 y1, y1 = Σ \{\ λ n2 v, v =
                     (dN f n2) [t1] / INR (n2 !) * 
                     (x - t1) ^^ n2 \}\ k \}\ [x']).
             apply AxiomII'. auto. split.
             apply AxiomII. 
             exists (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] /
             INR ((S k) !) * (x - t1) ^^ S k \}\[x']).
             apply AxiomII'; auto.
             assert (\{\ λ t2 y2, y2 = \{\ λ t1 y1, 
                        y1 = Σ \{\ λ n2 v, v = (dN f n2) [t1] 
                        / INR (n2 !) * (x - t1) ^^ n2 \}\ k \}\
                         [t2] \}\[x'] = 
                      \{\ λ t1 y1, y1 = Σ \{\ λ n2 v,
                        v = (dN f n2) [t1] / INR (n2 !) *
                        (x - t1) ^^ n2 \}\ k \}\ [x']).
             { apply f_x. 
               red. intros.
               applyAxiomII' H13. applyAxiomII' H14.
               rewrite H13; auto. apply AxiomII'.
               auto. }
             rewrite H13. clear H13. 
             assert (\{\ λ t2 y2 ,y2 = \{\ λ t1 y1, y1 =
                      (dN f (S k)) [t1] / INR ((S k) !) * 
                      (x - t1) ^^ S k \}\[t2] \}\ [x']
                   = \{\ λ t1 y1, y1 = \{\ λ x y, 
                      derivative (dN f k) x y \}\ [t1] /
                      INR (k ! + k * k !) * ((x - t1) * 
                      (x - t1) ^^ k) \}\ [x'] ).
             { apply f_x. red. intros.
               applyAxiomII' H13. applyAxiomII' H14.
               rewrite H13; auto. apply AxiomII'.
               auto. }
             rewrite H13. clear H13. auto.
           - apply AxiomII. applyAxiomII H11. 
             destruct H11 as [x'[y' H11]].
             exists x', y'. 
             destruct H11 as [H11 [H12 [H13 H14]]].
             split; auto.
             assert (\{\ λ t2 y2, y2 = \{\ λ t1 y1, 
                        y1 = Σ \{\ λ n2 v, v = (dN f n2) [t1] 
                        / INR (n2 !) * (x - t1) ^^ n2 \}\ k \}\
                         [t2] \}\[x'] = 
                      \{\ λ t1 y1, y1 = Σ \{\ λ n2 v,
                        v = (dN f n2) [t1] / INR (n2 !) *
                        (x - t1) ^^ n2 \}\ k \}\ [x']).
             { apply f_x. 
               red. intros.
               applyAxiomII' H15. applyAxiomII' H16.
               rewrite H15; auto. apply AxiomII'.
               auto. }
             rewrite H15 in H14. clear H15.  
             assert (\{\ λ t2 y2 ,y2 = \{\ λ t1 y1, y1 =
                      \{\ λ x y, derivative (dN f k) x y \}\
                     [t1] / INR (k ! + k * k !) * 
                    ((x - t1) * (x - t1) ^^ k) \}\ [t2] \}\ [x']
                   = \{\ λ t1 y1, y1 = (dN f (S k)) [t1] / 
                     INR ((S k) !) * (x - t1) ^^ S k \}\ [x'] ).
             { apply f_x. red. intros.
               applyAxiomII' H15. applyAxiomII' H16.
               rewrite H15; auto. apply AxiomII'.
               auto. }
             rewrite H15 in H14. clear H15. auto. }
        rewrite H11. apply Lemma6_10_4'.   
        assert ( (k <= n)%nat). 
        { apply le_Sn_le. auto. }
        apply IHk in H12. rewrite H3 in H12.
      * assert (ContinuousClose \{\ λ t y, y = f [x] \}\ x0 x).
        { apply Lemma6_10_5. }
        apply (Lemma6_10_4 \{\ λ t y, y = f [x] \}\
        \{\ λ t y, y = f [x] - Σ \{\ λ k v, v =
           (dN f k) [t] / INR (k !) * (x - t) ^^ k \}\ k \}\
        x0 x) in H13; auto.
        assert ((\{\ λ t y : R,y = f [x] \}\ \-
         \{\ λ t y, y = f [x] - Σ \{\ λ k v, v =
         (dN f k) [t] / INR (k !) * (x - t) ^^ k \}\ k \}\) =
         \{\ λ t y : R,y = Σ \{\ λ k v, v =
         (dN f k) [t] / INR (k !) * (x - t) ^^ k \}\ k  \}\ ).
         { apply AxiomI. split; intros.
          - applyAxiomII H14. 
           destruct H14 as [x'[y'[H14[H14'[H14'' H14''']]]]].
           apply AxiomII. exists x',y'. split; auto.
           assert (\{\ λ t y : R,y = f [x] \}\ [x'] = f [x]).
           { apply f_x. red. intros. applyAxiomII' H15.
             applyAxiomII' H16. rewrite H15; auto.
             apply AxiomII'. auto. }
           rewrite H15 in H14'''. clear H15.
           assert (\{\ λ t y : R,y = f [x] - Σ \{\
                    λ k v, v =(dN f k) [t] / INR (k !) * 
                    (x - t) ^^ k \}\ k \}\ [x'] = f [x] - 
                    Σ \{\ λ k v, v =(dN f k) [x'] / INR (k !) * 
                    (x - x') ^^ k \}\ k). 
           { apply f_x. red. intros. applyAxiomII' H15.
             applyAxiomII' H16. rewrite H15. auto.
             apply AxiomII'. auto. }
           rewrite H15 in H14'''. clear H15.
           rewrite H14'''. lra.
          - applyAxiomII H14. 
            destruct H14 as [x'[y'[H14 H14']]].
            apply AxiomII. exists x',y'. split; auto.
            split. apply AxiomII. exists f[x].
            apply AxiomII'. auto. split.
            apply AxiomII. 
            exists (f [x] - Σ \{\ λ k0 v,v = (dN f k0) [x'] /
             INR (k0 !) * (x - x') ^^ k0 \}\ k). apply AxiomII'.
            auto. 
            assert (\{\ λ t y : R,y = f [x] \}\ [x'] = f [x]).
            { apply f_x. red. intros. applyAxiomII' H15.
             applyAxiomII' H16. rewrite H15; auto.
             apply AxiomII'. auto. }
            rewrite H15. clear H15.
            assert (\{\ λ t y : R,y = f [x] - Σ \{\
                    λ k v, v =(dN f k) [t] / INR (k !) * 
                    (x - t) ^^ k \}\ k \}\ [x'] = f [x] - 
                    Σ \{\ λ k v, v =(dN f k) [x'] / INR (k !) * 
                    (x - x') ^^ k \}\ k). 
            { apply f_x. red. intros. applyAxiomII' H15.
              applyAxiomII' H16. rewrite H15. auto.
              apply AxiomII'. auto. }
            rewrite H15. clear H15. 
            rewrite H14'. lra.  }
            rewrite H14 in H13. clear H14.
            assert (\{\ λ t2 y2, y2 = \{\ λ t1 y1,y1 =
                      Σ \{\ λ n2 v, v = (dN f n2) [t1] / 
                INR (n2 !) * (x - t1) ^^ n2 \}\ k \}\ [t2] \}\ =
                \{\ λ t y : R,y = Σ \{\ λ k v, v =
             (dN f k) [t] / INR (k !) * (x - t) ^^ k \}\ k \}\).
            { apply AxiomI. split; intros.
              - applyAxiomII H14. 
                destruct H14 as [x'[y'[H14 H14']]].
                apply AxiomII. exists x',y'. split; auto.
                rewrite H14'. apply f_x. 
                red. intros. applyAxiomII' H15.
                applyAxiomII' H16. rewrite H15. auto.
                apply AxiomII'. auto.
              - applyAxiomII H14. 
                destruct H14 as [x'[y'[H14 H14']]].
                apply AxiomII. exists x',y'. split; auto. 
                rewrite H14'.  symmetry. apply f_x.
                red. intros. applyAxiomII' H15.
                applyAxiomII' H16. rewrite H15. auto.
                apply AxiomII'. auto. }
             rewrite H14. auto.
      * clear H11.
        assert (\{\ λ t2 y2, y2 = \{\ λ t1 y1,y1 =
                 (dN f (S k)) [t1] / INR ((S k) !) * 
                 (x - t1) ^^ S k \}\[t2]\}\ = \{\ λ t1 y1,y1 =
                 (dN f (S k)) [t1] / INR ((S k) !) * 
                 (x - t1) ^^ S k \}\).
        { apply AxiomI. split; intros.
          - applyAxiomII H11. 
            destruct H11 as [x'[y'[H11 H11']]].
            apply AxiomII. exists x',y'. split; auto.
            rewrite H11'. apply f_x.
            red. intros. applyAxiomII' H12.
            applyAxiomII' H13. rewrite H12; auto.
            apply AxiomII'. 
            simpl. auto.
          - applyAxiomII H11. apply AxiomII.
            destruct H11 as [x'[y'[H11 H11']]].
            exists x',y'. split; auto.
            rewrite H11'. symmetry. apply f_x.
            red. intros. applyAxiomII' H12.
            applyAxiomII' H13. rewrite H12; auto.
            apply AxiomII'. 
            simpl. auto. }
         rewrite H11. clear H11. 
         apply H1 in H10. destruct H10 as [H10 H10'].
         (**buqueding**)
        apply (Lemma6_10_6 (dN f (S k)) a b x0 x ) in H10';auto.
         assert (ContinuousClose \{\ λ t1 y1, 
                 y1 = INR ((S k) !) \}\ x0 x).
         { apply Lemma6_10_8; auto. }
         assert (ContinuousClose \{\ λ t1 y1, 
                 y1 = (x - t1) ^^ S k  \}\ x0 x).
         { apply Lemma6_10_9; auto. }
         assert ( \{\ λ t1 y1, y1 = (dN f (S k)) [t1] / 
         INR ((S k) !) * (x - t1) ^^ S k \}\ = 
         \{\ λ t1 y1, y1 = (dN f (S k)) [t1] / 
         INR ((S k) !)\}\ ** 
         \{\ λ t1 y1, y1 = (x - t1) ^^ S k\}\).
         { apply AxiomI. split; intros.
           applyAxiomII H13. 
           destruct H13 as [x'[y'[H13 H13']]].
           apply AxiomII. exists x',y'. split; auto.
           split. apply AxiomII. 
           exists ((dN f (S k)) [x'] / INR ((S k) !)).
           apply AxiomII'. auto. split. apply AxiomII. 
           exists ((x - x') ^^ S k).
           apply AxiomII'. auto.
           assert (\{\ λ t1 y1,
           y1 = (dN f (S k)) [t1] / INR ((S k) !) \}\ [x'] =
           (dN f (S k)) [x'] / INR ((S k) !)).
           apply f_x. red. intros. applyAxiomII' H14.
           applyAxiomII' H15. rewrite H14; auto.
           apply AxiomII'. auto. rewrite H14. clear H14.
           assert (\{\ λ t1 y1, y1 = (x - t1) ^^ S k \}\ [x']
           = (x - x') ^^ S k).
           apply f_x. red. intros. applyAxiomII' H14.
           applyAxiomII' H15. rewrite H14; auto.
           apply AxiomII'. auto. rewrite H14. clear H14.
           rewrite H13'. simpl. auto. 
           applyAxiomII H13.  
           destruct H13 as [x'[y'[H13 [H13'[H13'' H13''']]]]].
           apply AxiomII. exists x',y'. split; auto.
           assert (\{\ λ t1 y1,
           y1 = \{\ λ x y,derivative (dN f k) x y \}\ [t1] 
           / INR (k ! + k * k !) \}\ [x'] =
           \{\ λ x y,derivative (dN f k) x y \}\ [x'] 
           / INR (k ! + k * k !)).
           apply f_x. red. intros. applyAxiomII' H14.
           applyAxiomII' H15. rewrite H14; auto.
           apply AxiomII'. auto. rewrite H14 in H13'''.
           clear H14.
           assert (\{\ λ t1 y1, y1 = (x - t1) * (x - t1) ^^ k \}\ [x']
           = (x - x') * (x - x') ^^ k).
           apply f_x. red. intros. applyAxiomII' H14.
           applyAxiomII' H15. rewrite H14; auto.
           apply AxiomII'. auto. rewrite H14 in H13'''.
           clear H14.
           rewrite H13'''. simpl. auto. 
         }
         rewrite H13. clear H13.
         apply Lemma6_10_7'; auto.  
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] / 
         INR ((S k) !) \}\ = 
         \{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\ //
         \{\ λ t1 y1, y1 = INR ((S k) !) \}\).
         { apply AxiomI. split; intros.
           applyAxiomII H13. 
           destruct H13 as [x''[y''[H13 H13']]].
           apply AxiomII. exists x'',y''. split; auto.
           split. apply AxiomII. exists ((dN f (S k)) [x'']).
           apply AxiomII'. auto. split. apply AxiomII.
           exists (INR ((S k) !)). apply AxiomII'. auto.
           split. intro.
           assert (\{\ λ t1 y1, 
           y1 = INR ((S k) !) \}\ [x''] = INR ((S k) !)).
           Function_ass. rewrite H15 in H14. 
           pose proof (Lemma6_3_1 (S k)).
           apply lt_0_INR in H16. rewrite H14 in H16. 
           lra. rewrite H13'. simpl; auto. 
           assert (\{\ λ t1 y1, y1 = \{\ λ x1 y,
           derivative (dN f k) x1 y \}\ [t1] \}\ [x''] = 
           \{\ λ x1 y, derivative (dN f k) x1 y \}\[x'']).
           Function_ass. rewrite H14. clear H14.
           assert (\{\ λ x1 y1, y1 = 
           INR (k ! + k * k !) \}\ [x''] = INR (k ! + k * k !)).
           Function_ass. rewrite H14. clear H14.
           auto. 
           applyAxiomII H13. 
           destruct H13 as [x''[y''[H13 [H13'[H13'' [H13''' H13'''']]]]]].
           apply AxiomII. exists x'',y''. split; auto.
           cut (\{\ λ t1 y1, y1 = \{\ λ x1 y,
           derivative (dN f k) x1 y \}\ [t1] \}\ [x''] = 
           \{\ λ x1 y, derivative (dN f k) x1 y \}\[x'']).
           intros. rewrite H14 in H13''''.
           cut (\{\ λ x1 y1, y1 = 
           INR (k ! + k * k !) \}\ [x''] = INR (k ! + k * k !)).
           intros. rewrite H15 in H13''''.
           rewrite H13''''. simpl. auto. Function_ass. 
           Function_ass. 
         } 
         rewrite H13. clear H13. apply Lemma6_10_7; auto.
         
         red in H10'.
         destruct H10' as [A1 [A2 A3]].
         red in A1. red. split. red. intros. apply A1 in H13.
         red in H13. destruct H13 as [H13 H13'].
         red in H13'. 
         destruct H13' as [H13'[δ [H13''[H13''' H13'''']]]].
         red. split. apply AxiomII. 
         exists ((dN f (S k)) [x1]). apply AxiomII'. auto.
         red. split. QED_function. exists δ. split. lra.
         split. red. intros. apply AxiomII. 
         exists ((dN f (S k)) [z]). apply AxiomII'. auto.
         intros. apply H13'''' in H14.
         destruct H14 as [δ'[H14 H14']].
         exists (δ'). split. auto.
         intros. apply H14' in H15.
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x2] = (dN f (S k)) [x2]). Function_ass.
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x1] = (dN f (S k)) [x1]). Function_ass. 
         rewrite H16, H17. auto. split. 
         red. split. apply AxiomII. exists ((dN f (S k)) [x0]).
         apply AxiomII'. auto.
         red. split. QED_function. red in A2. 
         destruct A2 as [A2 A2']. red in A2'.
         destruct A2' as [A2'[δ [A2''[A2''' A2'''']]]].
         exists δ. split. auto. split. red. intros.
         apply AxiomII. exists ((dN f (S k)) [z]).
         apply AxiomII'. auto. intros.
         apply A2'''' in H13.
         destruct H13 as [δ'[H13 H13']].
         exists δ'. split. auto. intros.
         apply H13' in H14. 
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x0] = (dN f (S k)) [x0]). Function_ass.
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x1] = (dN f (S k)) [x1]). Function_ass. 
         rewrite H15, H16. auto. 
         red. split. apply AxiomII. exists ((dN f (S k)) [x]).
         apply AxiomII'. auto.
         red. split. QED_function. red in A3. 
         destruct A3 as [A3 A3']. red in A3'.
         destruct A3' as [A3'[δ [A3''[A3''' A3'''']]]].
         exists δ. split. auto. split. red. intros.
         apply AxiomII. exists ((dN f (S k)) [z]).
         apply AxiomII'. auto. intros.
         apply A3'''' in H13.
         destruct H13 as [δ'[H13 H13']].
         exists δ'. split. auto. intros.
         apply H13' in H14. 
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x] = (dN f (S k)) [x]). Function_ass.
         assert (\{\ λ t1 y1, y1 = (dN f (S k)) [t1] \}\
                 [x1] = (dN f (S k)) [x1]). Function_ass. 
         rewrite H15, H16. auto.  
         intros. intro. 
         assert (\{\ λ t1 y1, y1 = INR ((S k) !) \}\ [a0]
                 = INR ((S k) !)).
         { apply f_x. QED_function. apply AxiomII'. auto. } 
         rewrite H14 in H13. pose proof (Lemma6_3_1 (S k)).
         apply lt_0_INR in H15. rewrite H13 in H15. 
         lra. apply AxiomII. lra. apply AxiomII. lra. } 
  (**证毕F在[x0,x]上连续**)
     pose proof (P2 n). assert ((n <= n)%nat).  
     apply Nat.le_refl. apply H10 in H11 as Q2. 
     clear H10. clear H11. 
   
   (**G(t)在(x0,x)上可导**)
    assert (P3: (∀ t, x0 < t < x -> 
           derivative G t (- (INR(n+1))*(x-t)^^n))). 
  { intros. rewrite J1. 
    assert (derivative \{\ λ t0 y, y = (t0 - x) ^^ S n \}\ 
             t ( INR (S n) * (t - x) ^^ (S n - 1))).
    apply (Lemma5_4 x t (S n)). 
    assert (derivative \{\ λ t0 y, y = (- 1)^^(S n) * 
            (t0 - x) ^^ S n \}\  t 
            ((- 1)^^(S n) * INR (S n) * (t - x) ^^ (S n - 1))).
    apply (Lemma5_5 x ((- 1)^^(S n)) t (S n)).
    assert (\{\ λ t0 y, y = (-1) ^^ S n * (t0 - x) ^^ S n \}\ 
     = \{\ λ t0 y, y = (x - t0) ^^ S n \}\).
    { apply AxiomI. split; intros.
      - applyAxiomII H13. destruct H13 as [x'[y'[H13 H13']]].
        apply AxiomII. exists x',y'. split; auto.
        rewrite H13'.
        cut ((-1) ^^ S n * (x' - x) ^^ S n = 
        -1 * (-1) ^^ n * ((x' - x) * (x' - x) ^^ n)).
        intros. rewrite <- H14.
        rewrite (Lemma_pow4 (-1) (x' - x) (S n)).
        cut ((-1 * (x' - x)) = (x - x')). intros.
        rewrite H15. auto. lra. simpl. auto.
      - applyAxiomII H13. destruct H13 as [x'[y'[H13 H13']]].
        apply AxiomII. exists x',y'. split; auto.
        rewrite H13'. 
        cut ((x - x') * (x - x') ^^ n = (x - x') ^^ S n).
        intros. rewrite H14. 
        rewrite (Lemma_pow4 (-1) (x' - x) (S n)). 
        cut ((x - x') = (-1 * (x' - x))). intros.
        rewrite H15. auto. lra. simpl. auto. }
    rewrite H13 in H12. clear H13.
    assert (((-1) ^^ S n * INR (S n) * (t - x) ^^ (S n - 1))
     = (- INR (n + 1) * (x - t) ^^ n)).
    { rewrite Rmult_assoc. rewrite Rmult_comm.
      rewrite Rmult_assoc. 
      cut (((t - x) ^^ (S n - 1) * (-1) ^^ S n) = 
      - (x - t) ^^ n).
      intros. rewrite H13. rewrite Rmult_comm.
      cut (INR (S n) = INR (n + 1)). intros.
      rewrite H14. rewrite <- Ropp_mult_distr_l. 
      symmetry. rewrite <- Ropp_mult_distr_l. symmetry.
      apply (Ropp_eq_compat ((x - t) ^^ n * INR (n + 1)) 
      (INR (n + 1) * (x - t) ^^ n)). rewrite Rmult_comm.
       auto. rewrite S_INR. rewrite plus_INR.
       cut (INR 1 = 1). intros. rewrite H14. auto.
       simpl. auto. 
       cut ((t - x) ^^ (S n - 1) = (t - x) ^^ n).
       intros. rewrite H13. cut ((-1) ^^ S n = - (-1) ^^ n).
       intros. rewrite H14. rewrite Rmult_comm.
       rewrite <- Ropp_mult_distr_l. 
       cut ( ((-1) ^^ n * (t - x) ^^ n) = (x - t) ^^ n).
       intros. rewrite H15. auto. rewrite Lemma_pow4.
       cut ((-1 * (t - x)) = (x - t)). intros.
       rewrite H15. auto. lra. simpl. lra. simpl. 
       cut ((n - 0)%nat = n). intros. rewrite H13.
       auto. rewrite Nat.sub_0_r. auto. }
    rewrite H13 in H12.
    auto. } 
  assert (P4: (∀ t, x0 < t < x -> derivable G t)).
  { intros. apply P3 in H10. red. 
    exists ((- INR (n + 1) * (x - t) ^^ n)). auto. }
  (**G在[x0,x]上连续**)
  assert (P5: ContinuousClose G x0 x).
  { red. split.
    - red. intros. apply P4 in H10. apply Theorem5_1 in H10.
      auto.
    - split.
      + rewrite J1.   
        assert(C1: ∀k : nat, Continuous \{\ λ t y, y = (x - t) ^^ k\}\ x0).
        { intros. 
          red. split. apply AxiomII. exists ((x - x0) ^^ k).
          apply AxiomII'; auto. 
          assert(∀t : R, (x - t) ^^ k = (-1 * (t - x)) ^^ k).
          { intros. replace (-1 * (t - x)) with (x - t). auto.
            lra. } 
          assert(\{\ λ t y,y = (x - t) ^^ k \}\ = \{\ λ t y, y = (-1) ^^ k * (t - x) ^^ k \}\). 
          { apply AxiomI. split; intros.
           - applyAxiomII H11. 
             destruct H11 as [x'[y'[H11 H12]]].
             apply AxiomII. exists x', y'. split; auto.
             rewrite Lemma_pow4. 
             replace (-1 * (x' - x)) with (x - x').
             auto. lra.
           - applyAxiomII H11. 
             destruct H11 as [x'[y'[H11 H12]]].
             apply AxiomII. exists x', y'. split; auto.
             rewrite Lemma_pow4 in H12. 
             replace (-1 * (x' - x)) with (x - x') in H12.
             auto. lra. }  
           rewrite H11. 
         assert(∀t : R,\{\ λ t y,y = (-1) ^^ k * (t - x) ^^ k \}\ [t] = (-1) ^^ k * (t - x) ^^ k). 
         intros. apply f_x. red. intros.
         applyAxiomII' H12. applyAxiomII' H13. rewrite H12.
         auto. apply AxiomII'. auto. rewrite H12.
         apply Lemma7'. }
        pose proof (C1 (S n)). apply Theorem4_1 in H10.
        tauto.  
      + rewrite J1.
        assert(C1: ∀k : nat, Continuous \{\ λ t y, y = (x - t) ^^ k\}\ x).
        { intros. 
          red. split. apply AxiomII. exists ((x - x) ^^ k).
          apply AxiomII'; auto. 
          assert(∀t : R, (x - t) ^^ k = (-1 * (t - x)) ^^ k).
          { intros. replace (-1 * (t - x)) with (x - t). auto.
            lra. } 
          assert(\{\ λ t y,y = (x - t) ^^ k \}\ = \{\ λ t y, y = (-1) ^^ k * (t - x) ^^ k \}\). 
          { apply AxiomI. split; intros.
           - applyAxiomII H11. 
             destruct H11 as [x'[y'[H11 H12]]].
             apply AxiomII. exists x', y'. split; auto.
             rewrite Lemma_pow4. 
             replace (-1 * (x' - x)) with (x - x').
             auto. lra.
           - applyAxiomII H11. 
             destruct H11 as [x'[y'[H11 H12]]].
             apply AxiomII. exists x', y'. split; auto.
             rewrite Lemma_pow4 in H12. 
             replace (-1 * (x' - x)) with (x - x') in H12.
             auto. lra. }  
           rewrite H11. 
         assert(∀t : R,\{\ λ t y,y = (-1) ^^ k * (t - x) ^^ k \}\ [t] = (-1) ^^ k * (t - x) ^^ k). 
         intros. apply f_x. red. intros.
         applyAxiomII' H12. applyAxiomII' H13. rewrite H12.
         auto. apply AxiomII'. auto. rewrite H12.
         apply Lemma7'. }
        pose proof (C1 (S n)). apply Theorem4_1 in H10.
        tauto. } 
  (**G的一阶导数不为0**)
  assert (P6:∀ t, x0 < t < x -> G '[t] <> 0).
  { intros. pose proof H10 as H10'. 
    apply P3 in H10. apply derEqual in H10.
    rewrite H10. 
    apply Rmult_integral_contrapositive_currified.
    apply Ropp_neq_0_compat.
    cut ((n + 1)%nat = S n). intros. rewrite H11. 
    rewrite S_INR. intro. pose proof (pos_INR n).
    lra. apply Nat.add_1_r. 
    apply Lemma6_3_5. lra. }
  assert (P7:(∀ t, x0 < t < x -> ~((F n)'[t] = 0 /\ G '[t] = 0))).
  { intros. apply P6 in H10. intro. destruct H11.
    contradiction. }
  (**F(x) = G(x) = 0**)
  assert ((F n)[x] = 0 /\ G [x] = 0).
  { split. 
    - rewrite H5.
      assert (∀n, f [x] - Σ \{\ λ k v,v = (dN f k) [x] / 
      INR (k !) * (x - x) ^^ k \}\ n = 0). 
      { intros. induction n0. 
        + simpl.  
          assert (\{\ λ k v, v = (dN f k) [x] / INR (k !) *
                (x - x) ^^ k \}\ [0%nat] = f[x]).
          apply f_x. red. intros. applyAxiomII' H10. 
          applyAxiomII' H11. rewrite H10. auto.
          apply AxiomII'. simpl. lra. rewrite H10. lra.
        + simpl. 
          assert (\{\ λ k v,v = (dN f k) [x] / INR (k !) * 
                     (x - x) ^^ k \}\ [S n0] = 0). 
          { apply f_x. red. intros. applyAxiomII' H10.
            applyAxiomII' H11. rewrite H10. auto.
            apply AxiomII'. 
            cut ((x - x) ^^ S n0 = 0).
            intros. rewrite H10. lra.
            cut (x -x = 0). intros. rewrite H10.
            apply (Lemma6_3_4 (S n0)). 
            apply Nat.lt_0_succ. lra. }
          rewrite H10. lra. }
      pose proof (H10 n). auto.
    - rewrite J3. cut (x - x = 0). intros. rewrite H10.
      apply (Lemma6_3_4 (S n)). apply Nat.lt_0_succ. lra. }
  assert (P8: G[x0] <> G[x]).
  { destruct H10. rewrite H11. 
    rewrite J3. apply (Lemma6_3_5 (x - x0) (S n)). lra. } 
  assert (∃ ξ, x0 < ξ < x /\ 
          ((F n) '[ξ])/(G '[ξ]) = (((F n)[x] - (F n)[x0]) / (G[x] - G[x0]))).
  { apply Theorem6_6; auto. }
  destruct H11 as [ξ [H11 H11']].
  exists ξ. split. apply AxiomII. 
  applyAxiomII H2. applyAxiomII H2'.  
  destruct H2 as [I2' I2'']. destruct H2' as [K2 K2'].
  destruct H11. 
  lra.
  destruct H10 as [H10 H10']. rewrite H10 in H11'. rewrite H10' in H11'.
  rewrite Rminus_0_l in H11'. rewrite Rminus_0_l in H11'.
  assert (J5: - (F n) [x0] / - G [x0] = (F n) [x0] / G [x0]).
  { unfold Rdiv. rewrite <- Ropp_inv_permute; lra. }
  rewrite J5 in H11'. clear J5.
  assert (∀t, x0 < t < x -> F n '[t] = - ((dN f (S n)) [t] / INR (n!)) * (x - t) ^^ n).
  { intros. apply I2 in H12. applyAxiomII' H12. 
    apply derEqual in H12. rewrite H12. 
    cut ((n + 1)%nat = S n). intros. rewrite H13. lra.
    cut ((n + 1)%nat = (1 + n)%nat). intros. rewrite H13. 
    apply Nat.add_1_l. apply Nat.add_comm. } 
  assert (∀t, x0 < t < x -> G '[t] = - INR(S n ) * (x - t) ^^ n).
  { intros. apply P3 in H13. apply derEqual in H13. 
    rewrite H13. cut ((n + 1)%nat = S n). intros. rewrite H14. 
    auto. cut ((n + 1)%nat = (1 + n)%nat). intros. rewrite H14. 
    apply Nat.add_1_l. apply Nat.add_comm. }
  pose proof (H12 ξ) as H12'. pose proof (H13 ξ) as H13'.
  clear H12. clear H13.
  assert (F n '[ ξ] / G '[ ξ] = ((dN f (S n)) [ξ] / INR ((S n)!))).
  { rewrite H12'. rewrite H13'. unfold Rdiv. 
    rewrite <- (Ropp_mult_distr_l (INR (S n)) ((x - ξ) ^^ n)).
    rewrite <- (Ropp_inv_permute (INR (S n) * (x - ξ) ^^ n)).
    rewrite Rmult_assoc. 
    rewrite (Rmult_comm ((x - ξ) ^^ n) (- / (INR (S n) * (x - ξ) ^^ n))).
    rewrite <- Rmult_assoc. rewrite Rmult_opp_opp. 
    rewrite (Rmult_assoc ((dN f (S n)) [ξ] * / INR (n !)) 
    (/ (INR (S n) * (x - ξ) ^^ n)) ((x - ξ) ^^ n)). 
    rewrite (Rmult_comm (/ (INR (S n) * (x - ξ) ^^ n)) ((x - ξ) ^^ n)).
    rewrite (Rmult_comm (INR (S n)) ((x - ξ) ^^ n)).
    rewrite Rinv_mult_distr.
    rewrite <- (Rmult_assoc ((x - ξ) ^^ n) (/ (x - ξ) ^^ n) (/ INR (S n))).
    rewrite (Rinv_r_simpl_r ((x - ξ) ^^ n) (/INR (S n))).
    rewrite Rmult_assoc.
    rewrite <- (Rinv_mult_distr (INR (n !)) (INR (S n))).
    assert ((INR (n !) * INR (S n)) = INR ((S n) !)).
    { pose proof (Lemma6_3_6 (S n)). intros. 
      cut ((S n > 0)%nat). intros. apply H12 in H13. 
      rewrite H13. cut ((S n - 1)%nat = n). intros.
      rewrite H14. rewrite mult_INR. auto.
      simpl. apply Nat.sub_0_r. apply gt_Sn_O. } 
    rewrite H12. auto. 
    apply not_0_INR. apply not_eq_sym. apply lt_0_neq. apply Lemma6_3_1. 
    apply not_0_INR. apply not_eq_sym. apply lt_0_neq. auto.
    apply Lemma6_3_5. lra. apply Lemma6_3_5. lra.
    apply not_0_INR. apply not_eq_sym. apply lt_0_neq. auto.
    apply Rmult_integral_contrapositive. split.
    apply not_0_INR. apply not_eq_sym. apply lt_0_neq. auto.
    apply Lemma6_3_5. lra. auto. lra. }
  assert ((F n) [x0] = F n '[ ξ] / G '[ ξ] * G [x0]).
  { apply (Rmult_eq_compat_r  (G [ x0]) (F n '[ ξ] / G '[ ξ]) 
    ((F n) [x0] / G [x0])) in H11'. rewrite H11'.
    unfold Rdiv. 
    rewrite Rmult_comm. rewrite <- Rmult_assoc.
    rewrite (Rinv_r_simpl_m (G [x0]) ((F n) [x0])). auto.
    lra. }
  pose proof (J3 x0) as H14. rewrite H14 in H13. rewrite H12 in H13.
  rewrite <- H13. pose proof (H5 x0 n). rewrite H15. 
  rewrite Rplus_minus. auto.  
Qed.
  
  














End A6_3.

Export A6_3.