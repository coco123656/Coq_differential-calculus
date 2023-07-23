Require Export A_2_2.

Module A2_3.

(* 2.3 数列极限存在的条件 *)

(* 定义:单调增数列 *)
Definition IncreaseSeq (x : Seq) : Prop :=
    IsSeq x /\ (∀ n : nat, x[n] <= x[S n]).

(* 定义:单调减数列 *)
Definition DecreaseSeq (x : Seq) : Prop :=
    IsSeq x /\ (∀ n : nat, x[n] >= x[S n]).

(* 定义: 单调数列 *)
Definition MonotonicSeq (x : Seq) : Prop := IncreaseSeq x \/ DecreaseSeq x.

(* 定理:单调增数列的等价性 *)
Theorem EqualIncrease : ∀ (x : Seq), IncreaseSeq x <->
  (IsSeq x /\ (∀ (n1 n2 : nat), (n1 < n2)%nat -> x[n1] <= x[n2])).
Proof.
  intro x; split; intro H0.
  - destruct H0 as [H0 H1]. split; auto. intros n1 n2.
    induction n2 as [|n2 IHn2].
    + intro H2. exfalso. apply (Nat.nlt_0_r n1). auto.
    + destruct (Nat.lt_total n1 n2) as [H2 | [H2 | H2]]; intro H3.
      * apply Rle_trans with (r2 := x[n2]); auto.
      * rewrite <- H2. auto.
      * apply lt_n_Sm_le in H3. exfalso. apply lt_not_le in H2. auto.
  - destruct H0 as [H0 H1]. split; auto.
Qed.

(* 定理:单调减数列的等价性 *)
Theorem EqualDecrease : ∀ (x : Seq), DecreaseSeq x <->
  (IsSeq x /\ (∀ (n1 n2 : nat), (n1 < n2)%nat -> x[n1] >= x[n2])).
Proof.
  intro x; split; intro H0.
  - destruct H0 as [H0 H1]. split; auto. intros n1 n2.
    induction n2 as [|n2 IHn2].
    + intro H2. exfalso. apply (Nat.nlt_0_r n1). auto.
    + destruct (Nat.lt_total n1 n2) as [H2 | [H2 | H2]]; intro H3.
      * apply Rge_trans with (r2 := x[n2]); auto.
      * rewrite <- H2. auto.
      * apply lt_n_Sm_le in H3. exfalso. apply lt_not_le in H2. auto.
  - destruct H0 as [H0 H1]. split; auto.
Qed.

(* 定义: 有界数列 *)
Definition BoundedSeq (x : Seq) : Prop := IsSeq x /\
  (∃ M, ∀ n, Abs[x[n]] <= M).

(* 定理2.9 单调有界定理 *)
Theorem Theorem2_9 : ∀ (x : Seq), MonotonicSeq x ->
  BoundedSeq x -> Convergence x.
Proof.
  intros x H0 H1. destruct H1 as [H [M H1]].
  assert (H2 : IsSeq x).
  { destruct H0 as [H0 | H0]; apply H0. }
  destruct H2 as [H2 H3].
  assert (H4 : NotEmpty ran[x]).
  { unfold NotEmpty. exists (x[0%nat]). apply fx_ran; auto.
    rewrite H3. apply AxiomII. auto. }
  apply Sup_inf_principle in H4 as H5. destruct H5 as [H5 H6].
  destruct H0 as [H0 | H0].
  - assert (H7 : ∃M : R,Upper ran[x] M).
    { exists M. unfold Upper. intros xn I1. applyAxiomII I1.
      destruct I1 as [n I1]. apply f_x in I1 as I2; auto.
      rewrite <- I2. generalize (H1 n). intro I3.
      apply Abs_le_R in I3. apply I3. }
    apply H5 in H7 as H8. destruct H8 as [a H8]. exists a. unfold sup in H8.
    destruct H8 as [H8 H9]. unfold limit_seq. repeat split; auto.
    intros ε H10. assert (H11 : a - ε < a).
    { apply Ropp_lt_gt_0_contravar in H10 as H11.
      apply Rplus_lt_compat_l with (r := a) in H11 as H12.
      rewrite Rplus_0_r in H12. auto. }
    apply H9 in H11 as H12. destruct H12 as [xN [H12 H13]].
    applyAxiomII H12. destruct H12 as [N H12]. exists N.
    apply EqualIncrease in H0 as H14. destruct H14 as [H14 H15].
    apply f_x in H12 as H16; auto. rewrite <- H16 in H13.
    intros n H17. apply H15 in H17 as H18.
    apply Rlt_le_trans with (r1 := a - ε) in H18 as H19; auto.
    apply Abs_R. unfold Upper in H8. assert (H20 : x[n] ∈ ran[x]).
    { apply fx_ran; auto. rewrite H3. apply AxiomII. auto. }
    apply H8 in H20 as H21. assert (H22 : a < a + ε).
    { apply Rplus_lt_compat_l with (r := a) in H10.
      rewrite Rplus_0_r in H10. auto. }
    assert (H24 : x[n] < a + ε).
    { apply Rle_lt_trans with (r2 := a); auto. }
    split.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
  - assert (H7 : ∃L : R,Lower ran[ x] L).
    { exists (-M). unfold Lower. intros xn I1. applyAxiomII I1.
      destruct I1 as [n I1]. apply f_x in I1 as I2; auto.
      rewrite <- I2. generalize (H1 n). intro I3.
      apply Abs_le_R in I3. apply Rle_ge. apply I3. }
    apply H6 in H7 as H8. destruct H8 as [a H8]. exists a. unfold inf in H8.
    destruct H8 as [H8 H9]. unfold limit_seq. repeat split; auto.
    intros ε H10. assert (H11 : a < a + ε).
    { apply Rplus_lt_compat_l with (r := a) in H10 as H12.
      rewrite Rplus_0_r in H12. auto. }
    apply H9 in H11 as H12. destruct H12 as [xN [H12 H13]].
    applyAxiomII H12. destruct H12 as [N H12]. exists N.
    apply EqualDecrease in H0 as H14. destruct H14 as [H14 H15].
    apply f_x in H12 as H16; auto. rewrite <- H16 in H13.
    intros n H17. apply H15 in H17 as H18. apply Rge_le in H18.
    apply Rle_lt_trans with (r3 := a + ε) in H18 as H19; auto.
    apply Abs_R. unfold Lower in H8. assert (H20 : x[n] ∈ ran[x]).
    { apply fx_ran; auto. rewrite H3. apply AxiomII. auto. }
    apply H8 in H20 as H21. assert (H22 : a - ε < a).
    { apply Ropp_lt_gt_0_contravar in H10 as H22.
      apply Rplus_lt_compat_l with (r := a) in H22.
      rewrite Rplus_0_r in H22. auto. }
    assert (H24 : a - ε < x[n]).
    { apply Rlt_le_trans with (r2 := a); auto. apply Rge_le. auto. }
    split.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
    + apply Rplus_lt_reg_l with (r := a).
      assert (H23 : a + (x [n] - a) = x[n]). field. rewrite H23. auto.
Qed.


(* 定义: 数列 x 第 n 项之后的最大项 *)
Definition Max_Seq_n (x : Seq) (n m : nat) :=
  IsSeq x /\ (n <= m)%nat /\ (∀ (i : nat), (n <= i)%nat -> x[i] <= x[m]).

Fixpoint Fun_Lemma2_10 (x : Seq) (n : nat) :=
  match n with
  | 0%nat => cN \{ λ (m : nat), Max_Seq_n x 1%nat m \}
  | S n => cN \{ λ (m : nat), Max_Seq_n x (S (Fun_Lemma2_10 x n)) m \}
  end.

Fixpoint Fun_Lemma2_10' (x : Seq) (n k : nat) :=
  match n with
  | 0%nat => k
  | S n => cN \{ λ (m : nat), (m > (Fun_Lemma2_10' x n k))%nat /\
      x[m] > x[Fun_Lemma2_10' x n k] \}
  end.

(* 定理: 任何数列都存在单调子列 *)

(* 引理2-10-1: x是有界数列,y是x的子列,推得y是有界数列 *)
Lemma Lemma2_10_1 : ∀ (x y : Seq), BoundedSeq x ->
    SubSeq x y -> BoundedSeq y.
Proof.
  intros x y H0 H1. unfold BoundedSeq in *. unfold SubSeq in H1.
  destruct H0 as [H0 H2]. destruct H1 as [H1 [H3 [f [H4 [H5 H6]]]]].
  clear H1. split; auto. destruct H2 as [M H2].
  exists M. intro n. rewrite H6. apply H2.
Qed.

(* 引理2-10-2: 数列x存在一个最大项x[k] *)
Lemma Lemma2_10_2 : ∀ (x : Seq) (m n : nat), IsSeq x -> (m >= n)%nat ->
  (∃ (k : nat), (k >= n)%nat /\ (k <= m)%nat  /\ (∀ (i : nat), (i >= n)%nat ->
  (i <= m)%nat -> x[i] <= x[k] )).
Proof.
  intros x m n H0 H1. induction m as [|m IHm].
  - apply le_n_0_eq in H1. rewrite <- H1. exists 0%nat. repeat split; auto.
    intros i I1 I2. apply le_n_0_eq in I2. rewrite I2. right. reflexivity.
  - generalize (Nat.lt_ge_cases m n). intro H2.
    destruct H2 as [H2 | H2].
    + apply lt_le_S in H2. apply Nat.le_antisymm in H2 as H3; auto.
      rewrite <- H3. exists n. repeat split; auto. intros i I1 I2.
      apply Nat.le_antisymm in I2 as I3; auto. rewrite I3.
      right; reflexivity.
    + apply IHm in H2 as H3. destruct H3 as [k [H3 [H4 H5]]].
      generalize (Rlt_or_le x[k] x[S m]). intro H6.
      destruct H6 as [H6 | H6].
      * exists (S m). repeat split; auto. intros i H7 H8.
        apply le_lt_or_eq in H8. destruct H8 as [H8 | H8].
        -- apply lt_n_Sm_le in H8. generalize (H5 i H7 H8). intro H9.
          apply Rlt_le. apply Rle_lt_trans with (r2 := x[k]); auto.
        -- rewrite H8. right; reflexivity.
      * exists k. repeat split; auto. intros i H7 H8.
        apply le_lt_or_eq in H8. destruct H8 as [H8 | H8].
        -- apply lt_n_Sm_le in H8. auto.
        -- rewrite H8. apply H6.
Qed.

(* 引理2-10-3: x是一个数列,存在一个y数列是x的子列,且这个子列是单调数列 *)
Lemma Lemma2_10_3 : ∀ (x : Seq), IsSeq x ->
  (∃ (y : Seq), SubSeq x y /\ MonotonicSeq y).
Proof.
  intros x H0. destruct classic with (P := ∀ (k : nat),
    ∃ (m : nat), Max_Seq_n x k m) as [H1 | H1].
  - assert (H2 : ∃ (y : Seq), y = \{\ λ n v, v = x [Fun_Lemma2_10 x n] \}\).
    { exists \{\ λ n v, v = x [Fun_Lemma2_10 x n] \}\; auto. }
    destruct H2 as [y H2]. exists y.
    assert (H3 : ∀ (n : nat),
      ((Fun_Lemma2_10 x n) < (Fun_Lemma2_10 x (S n)))%nat).
    { intro n. induction n as [|n IHn].
      - simpl. assert (I1 :  cN \{ λ m : nat, Max_Seq_n x (S (cN \{ λ m0 : nat,
        Max_Seq_n x 1 m0 \})) m \} ∈ \{ λ m : nat, Max_Seq_n x
        (S (cN \{ λ m0 : nat, Max_Seq_n x 1 m0 \})) m \}).
        { apply AxiomcN. unfold NotEmpty.
          generalize (H1 (S (cN \{ λ m0 : nat, Max_Seq_n x 1 m0 \}))).
          intro I1. destruct I1 as [m I1]. exists m.
          apply <- AxiomII. auto. }
        applyAxiomII I1. destruct I1 as [I1 [I2 I3]].
        apply le_S_gt in I2. auto.
      - simpl. assert (I1 : cN \{ λ m : nat, Max_Seq_n x
          (S (cN \{ λ m0 : nat, Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \})) m \}
              ∈ \{ λ m : nat, Max_Seq_n x (S (cN \{ λ m0 : nat,
           Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \})) m \}).
        { apply AxiomcN. unfold NotEmpty. generalize (H1 (S (cN \{ λ m0 : nat,
          Max_Seq_n x (S (Fun_Lemma2_10 x n)) m0 \}))). intro I1.
          destruct I1 as [m I1]. exists m. apply AxiomII. auto. }
        applyAxiomII I1. destruct I1 as [I1 [I2 I3]].
        apply le_S_gt in I2. auto. }
    assert (H4 : ∃ f, f = \{\ λ n v, v = Fun_Lemma2_10 x n \}\).
    { exists \{\ λ n v, v = Fun_Lemma2_10 x n \}\; auto. }
    destruct H4 as [f H4]. assert (H5 : StrictlyIncreaseFun_nat f).
    { assert (I1 : Function f).
      { unfold Function. intros x0 y0 z0 I1 I2. rewrite H4 in *.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. auto. }
      split; auto. intros x1 y1 x2. induction x2 as [|x2 IHx2].
      - intros y2 I2 I3 I4. exfalso. apply (Nat.nlt_0_r x1). auto.
      - destruct (Nat.lt_total x1 x2) as [I2 | [I2 | I2]]; intros y2 I3 I4 I5.
        + assert (I6 : [x2, f\[x2\]] ∈ f).
          { apply x_fx_N; auto. apply AxiomII.
            exists (Fun_Lemma2_10 x x2). rewrite H4. apply AxiomII'.
            auto. }
          apply Nat.lt_trans with (m := f\[x2\]).
          * apply IHx2; auto.
          * rewrite H4 in I4. apply -> AxiomII' in I4; lazy beta in I4.
            pattern f at 2 in I6. rewrite H4 in I6. applyAxiomII' I6.
            rewrite I6. rewrite I4. apply H3.
        + rewrite <- I2 in *. rewrite H4 in I3. applyAxiomII' I3.
          rewrite H4 in I4. apply -> AxiomII' in I4. lazy beta in I4.
          rewrite I3; rewrite I4. apply H3.
        + apply lt_n_Sm_le in I5. exfalso. apply lt_not_le in I2. auto. }
    assert (H6 : IsSeq y).
    { split.
      - unfold Function. intros x0 y0 z0 I1 I2. rewrite H2 in *.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. auto.
      - apply AxiomI; intro z; split; intro I1.
        + apply AxiomII. auto.
        + apply AxiomII. exists (x[Fun_Lemma2_10 x z]).
          rewrite H2. apply AxiomII'. auto. }
    assert (H7 : dom[f] = Full nat).
    { apply AxiomI; intro z; split; intro I1.
      - apply AxiomII. auto.
      - apply AxiomII. exists (Fun_Lemma2_10 x z).
        rewrite H4. apply AxiomII'. auto. }
    split.
    + unfold SubSeq. split; auto; split; auto. exists f.
      split; auto; split; auto.
      intro n. assert (I1 : n ∈ dom[y]).
      { destruct H6 as [H6 I1]. rewrite I1. apply AxiomII; auto. }
      apply x_fx in I1 as I2; try apply H6. pattern y at 2 in I2.
      rewrite H2 in I2. applyAxiomII' I2. rewrite I2.
      assert (I3 : n ∈ dom[f]).
      { rewrite H7. apply AxiomII; auto. }
      apply x_fx_N in I3 as I4; try apply H5. pattern f at 2 in I4.
      rewrite H4 in I4. applyAxiomII' I4. rewrite I4. reflexivity.
    + unfold MonotonicSeq. right. unfold DecreaseSeq. split; auto.
      intro n. assert (I1 : ∀ m : nat, m ∈ dom[y]).
      { intro m. destruct H6 as [H6 I1]. rewrite I1. apply AxiomII; auto. }
      generalize (I1 n). intro I2. generalize (I1 (S n)). intro I3.
      apply x_fx in I2 as I4; try apply H6.
      apply x_fx in I3 as I5; try apply H6.
      pattern y at 2 in I4; rewrite H2 in I4.
      pattern y at 2 in I5; rewrite H2 in I5.
      applyAxiomII' I4. apply -> AxiomII' in I5. lazy beta in I5.
      destruct n as [|n].
      * assert (I6 : Max_Seq_n x 1%nat (Fun_Lemma2_10 x 0)).
        { assert (I6 : (Fun_Lemma2_10 x 0) ∈
            \{ λ (m : nat), Max_Seq_n x 1%nat m \}).
          { simpl. apply AxiomcN. unfold NotEmpty. generalize (H1 1%nat).
            intro I6. destruct I6 as [m I6]. exists m. apply AxiomII.
            apply I6. }
          apply -> AxiomII in I6. lazy beta in I6. auto. }
        rewrite I4. rewrite I5. unfold Max_Seq_n in I6.
        destruct I6 as [I6 [I7 I8]].
        assert (I9 : (1 <= (Fun_Lemma2_10 x 1))%nat).
        { apply Nat.le_trans with (m := (Fun_Lemma2_10 x 0)); auto.
          apply Nat.lt_le_incl. apply H3. }
        apply I8 in I9. apply Rle_ge. auto.
      * rewrite I4. rewrite I5.
        assert (I6 : Max_Seq_n x (S (Fun_Lemma2_10 x n))
          (Fun_Lemma2_10 x (S n))).
        { assert (I6 : (Fun_Lemma2_10 x (S n)) ∈
            \{ λ (m : nat), Max_Seq_n x (S (Fun_Lemma2_10 x n)) m \}).
          { simpl Fun_Lemma2_10 at 1.
            apply AxiomcN. unfold NotEmpty.
            generalize (H1 (S (Fun_Lemma2_10 x n))).
            intro I6. destruct I6 as [m I6]. exists m. apply AxiomII.
            apply I6. }
          apply -> AxiomII in I6. lazy beta in I6. auto. }
        unfold Max_Seq_n in I6. destruct I6 as [I6 [I7 I8]].
        assert (I9 : ((S (Fun_Lemma2_10 x n)) <=
          (Fun_Lemma2_10 x (S (S n))))%nat).
        { apply Nat.le_trans with (m := (Fun_Lemma2_10 x (S n))); auto.
          apply Nat.lt_le_incl. apply H3. }
        apply I8 in I9. apply Rle_ge. auto.
  - apply not_all_ex_not in H1. destruct H1 as [k H1].
    assert (H2 : ∀ m : nat, ~ (Max_Seq_n x k m)).
    { apply not_ex_all_not. auto. }
    assert (H3 : ∃ (y : Seq), y = \{\ λ n v, v = x[Fun_Lemma2_10' x n k] \}\).
    { exists \{\ λ n v, v = x[Fun_Lemma2_10' x n k] \}\; auto. }
    destruct H3 as [y H3]. exists y.
    assert (H4 : ∀ (n1 : nat), (n1 >= k)%nat ->
      (∃ (n2 : nat), (n2 > n1)%nat /\ x[n2] > x[n1])).
    { intros n1 I1. apply not_all_not_ex. intro I2. apply H1.
      generalize (Lemma2_10_2 x n1 k H0 I1). intro I3.
      destruct I3 as [m [I3 [I4 I5]]].
      exists m. unfold Max_Seq_n. split; auto; split; auto.
      intros i I6. generalize (Nat.lt_ge_cases n1 i). intro I7.
      destruct I7 as [I7 | I7]; auto.
      generalize (I2 i). intro I8. apply not_and_or in I8.
      destruct I8 as [I8 | I8]; [exfalso | idtac]; auto.
      apply Rnot_gt_le in I8. apply Rle_trans with (r2 := x[n1]); auto. }
    assert (H5 : ∀ (n : nat), ((Fun_Lemma2_10' x n k) >= k)%nat).
    { intro n. induction n as [|n IHn].
      - simpl. auto.
      - assert (I1 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
          (m > (Fun_Lemma2_10' x n k))%nat /\
           x[m] > x[Fun_Lemma2_10' x n k] \}).
        { apply AxiomcN. unfold NotEmpty. apply H4 in IHn as I1.
          destruct I1 as [m [I1 I2]]. exists m. apply AxiomII.
          split; auto. }
        apply -> AxiomII in I1. lazy beta in I1. destruct I1 as [I1 I2].
        apply Nat.lt_le_incl. eapply Nat.le_lt_trans; eauto. }
    assert (H6 : ∀ (n : nat),
      ((Fun_Lemma2_10' x n k) < (Fun_Lemma2_10' x (S n) k))%nat).
    { intro n.
      assert (I1 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
        (m > (Fun_Lemma2_10' x n k))%nat /\
        x[m] > x[Fun_Lemma2_10' x n k] \} ).
      { apply AxiomcN. unfold NotEmpty.
        generalize (H4 (Fun_Lemma2_10' x n k) (H5 n)). intro I1.
        destruct I1 as [n2 [I1 I2]]. exists n2. apply AxiomII.
        split; auto. }
      apply -> AxiomII in I1. lazy beta in I1. apply I1. }
    assert (H7 : ∃ f, f = \{\ λ n v, v = Fun_Lemma2_10' x n k \}\).
    { exists \{\ λ n v, v = Fun_Lemma2_10' x n k \}\; auto. }
    destruct H7 as [f H7]. assert (H8 : StrictlyIncreaseFun_nat f).
    { assert (I1 : Function f).
      { unfold Function. intros x0 y0 z0 I1 I2. rewrite H7 in *.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. auto. }
      split; auto. intros x1 y1 x2. induction x2 as [|x2 IHx2].
      - intros y2 I2 I3 I4. exfalso. apply (Nat.nlt_0_r x1). auto.
      - destruct (Nat.lt_total x1 x2) as [I2 | [I2 | I2]]; intros y2 I3 I4 I5.
        + assert (I6 : [x2, f\[x2\]] ∈ f).
          { apply x_fx_N; auto. apply AxiomII.
            exists (Fun_Lemma2_10' x x2 k). rewrite H7. apply AxiomII'.
            auto. }
          apply Nat.lt_trans with (m := f\[x2\]).
          * apply IHx2; auto.
          * rewrite H7 in I4. apply -> AxiomII' in I4; lazy beta in I4.
            pattern f at 2 in I6. rewrite H7 in I6. applyAxiomII' I6.
            rewrite I6. rewrite I4. apply H6.
        + rewrite <- I2 in *. rewrite H7 in I3. applyAxiomII' I3.
          rewrite H7 in I4. apply -> AxiomII' in I4. lazy beta in I4.
          rewrite I3; rewrite I4. apply H6.
        + apply lt_n_Sm_le in I5. exfalso. apply lt_not_le in I2. auto. }
    assert (H9 : IsSeq y).
    { split.
      - unfold Function. intros x0 y0 z0 I1 I2. rewrite H3 in *.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. auto.
      - apply AxiomI; intro z; split; intro I1.
        + apply AxiomII. auto.
        + apply AxiomII. exists (x[Fun_Lemma2_10' x z k]).
          rewrite H3. apply AxiomII'. auto. }
    assert (H10 : dom[f] = Full nat).
    { apply AxiomI; intro z; split; intro I1.
      - apply AxiomII. auto.
      - apply AxiomII. exists (Fun_Lemma2_10' x z k).
        rewrite H7. apply AxiomII'. auto. }
    split.
    + unfold SubSeq. split; auto; split; auto. exists f.
      split; auto; split; auto.
      intro n. assert (I1 : n ∈ dom[y]).
      { destruct H9 as [H9 I1]. rewrite I1. apply AxiomII; auto. }
      apply x_fx in I1 as I2; try apply H9. pattern y at 2 in I2.
      rewrite H3 in I2. applyAxiomII' I2. rewrite I2.
      assert (I3 : n ∈ dom[f]).
      { rewrite H10. apply AxiomII; auto. }
      apply x_fx_N in I3 as I4; try apply H8. pattern f at 2 in I4.
      rewrite H7 in I4. applyAxiomII' I4. rewrite I4. reflexivity.
    + left. unfold IncreaseSeq. split; auto. intro n.
      assert (I1 : ∀ m : nat, m ∈ dom[y]).
      { intro m. destruct H9 as [H9 I1]. rewrite I1. apply AxiomII; auto. }
      generalize (I1 n). intro I2. generalize (I1 (S n)). intro I3.
      apply x_fx in I2 as I4; try apply H9.
      apply x_fx in I3 as I5; try apply H9.
      pattern y at 2 in I4. rewrite H3 in I4. applyAxiomII' I4.
      pattern y at 2 in I5. rewrite H3 in I5.
      apply -> AxiomII' in I5; lazy beta in I5.
      rewrite I4; rewrite I5.
      assert (I6 : (Fun_Lemma2_10' x (S n) k) ∈ \{ λ (m : nat),
        (m > (Fun_Lemma2_10' x n k))%nat /\
        x[m] > x[Fun_Lemma2_10' x n k] \}).
      { apply AxiomcN. generalize (H4 (Fun_Lemma2_10' x n k) (H5 n)).
        intro I6. destruct I6 as [m [I6 I7]]. exists m.
        apply AxiomII; split; auto. }
      apply -> AxiomII in I6; lazy beta in I6.
      destruct I6 as [I6 I7]. left; auto.
Qed.

(* 定理2.10 致密性定理——有界数列必有收敛的子数列 *)
Theorem Theorem2_10 : ∀ (x : Seq), BoundedSeq x ->
  (∃ (y : Seq), SubSeq x y /\ Convergence y).
Proof.
  intros x H0. assert (H1 : ∀ (y : Seq), SubSeq x y -> BoundedSeq y).
  { intro y. apply Lemma2_10_1. auto. }
  destruct H0 as [H0 [M H2]]. apply Lemma2_10_3 in H0 as H3.
  destruct H3 as [y [H3 H4]]. exists y. split; auto.
  apply H1 in H3. apply Theorem2_9; auto.
Qed.

(* 定理2.11 柯西收敛准则 *)
Theorem Theorem2_11 : ∀ (x : Seq), IsSeq x ->
  (Convergence x <-> (∀ ε, ε > 0 -> ∃ N : nat, ∀ (n m : nat),
    (n > N)%nat -> (m > N)%nat -> Abs[x[n] - x[m]] < ε)).
Proof.
  intros x H0. split.
  - intros H1 ε H2. destruct H1 as [A H1]. assert (H3 : ε / 2 > 0).
    { generalize (Rinv_0_lt_compat 2 Rlt_0_2). intro I1.
      apply Rmult_gt_0_compat; auto. }
    apply H1 in H3 as H4. destruct H4 as [N H4].
    exists N. intros n m H5 H6. apply H4 in H5 as H7.
    apply H4 in H6 as H8.
    assert (H9 : Abs[x[n] - x[m]] <= Abs[x[n] - A] + Abs[x[m] - A]).
    { assert (I1 : x[n] - x[m] = (x[n] - A) - (x[m] - A)). field.
      rewrite I1. apply Abs_minus_le. }
    apply Rle_lt_trans with (r2 := Abs[x[n] - A] + Abs[x[m] - A]); auto.
    assert (H10 : ε = ε/2 + ε/2). field. rewrite H10.
    apply Rplus_lt_compat; auto.
  - intro H1. assert (H2 : BoundedSeq x).
    { unfold BoundedSeq. split; auto.
      generalize (H1 1 Rlt_0_1). intro I1. destruct I1 as [N0 I1].
      assert (I2 : ∀ n : nat, (n > N0)%nat -> Abs[x[n] - x[S N0]] < 1).
      { intros n I2. apply I1; auto. }
      assert (I3 : ∀ n : nat, (n > N0)%nat -> Abs[x[n]] < Abs[x[S N0]] + 1).
      { intros n I3. apply I2 in I3 as I4.
        apply Rplus_lt_compat_l with (r := Abs[x[S N0]]) in I4 as I5.
        apply Rle_lt_trans with (r2 := Abs[x[S N0]] + Abs[x[n] - x[S N0]]);
        auto. assert (I6 : x[n] = x[S N0] + (x[n] - x[S N0])). field.
        pattern x[n] at 1. rewrite I6. apply Abs_plus_le. }
      assert (I4 : ∀ N : nat, ∃ M0, ∀ n : nat,
        (n <= N)%nat -> Abs[x[n]] <= M0).
      { intro N. induction N as [|N IHN].
        - exists (Abs[x[0%nat]]). intros n J1. apply le_n_0_eq in J1.
          rewrite <- J1. right. reflexivity.
        - destruct IHN as [M0 IHN].
          destruct (Rlt_or_le M0 Abs[x[S N]]) as [J1 | J1].
          + exists (Abs[x[S N]]). intros n J2. apply le_lt_or_eq in J2.
            destruct J2 as [J2 | J2].
            * apply lt_n_Sm_le in J2. left.
              apply Rle_lt_trans with (r2 := M0); auto.
            * rewrite J2. right; reflexivity.
          + exists M0. intros n J2. apply le_lt_or_eq in J2.
            destruct J2 as [J2 | J2].
            * apply lt_n_Sm_le in J2. auto.
            * rewrite J2. auto. }
      generalize (I4 N0). intro I5. destruct I5 as [M0 I5].
      destruct (Rlt_or_le M0 (Abs[x[S N0]] + 1)) as [I6 | I6].
      - exists (Abs[x[S N0]] + 1). intro n. generalize (Nat.le_gt_cases n N0).
        intro I7. destruct I7 as [I7 | I7].
        + left. apply Rle_lt_trans with (r2 := M0); auto.
        + left. auto.
      - exists M0. intro n. generalize (Nat.le_gt_cases n N0).
        intro I7. destruct I7 as [I7 | I7]; auto.
        left. apply Rlt_le_trans with (r2 := (Abs[x[S N0]] + 1)); auto. }
    apply Theorem2_10 in H2 as H3. destruct H3 as [y [H3 H4]].
    destruct H4 as [a H4]. exists a. unfold limit_seq. split; auto.
    intros ε H5. assert (H6 : ε / 2 > 0).
    { generalize (Rinv_0_lt_compat 2 Rlt_0_2). intro I1.
      apply Rmult_gt_0_compat; auto. }
    apply H1 in H6 as H7. destruct H7 as [N H7]. exists N.
    intros n H8. assert (H9 : ∀ m, (m > N)%nat -> Abs[x[n] - y[m]] < ε/2).
    { intros m I6. assert (I7 : ∃ m1, (m1 > N)%nat /\ y[m] = x[m1]).
      { unfold SubSeq in H3. destruct H3 as [H3 [I1 [f [I2 [I3 I4]]]]].
        exists (f\[m\]). split; auto.
        apply fn_ge_n with (n := m) in I2 as I5; auto.
        apply Nat.lt_le_trans with (m := m); auto. }
      destruct I7 as [m1 [I7 I8]]. rewrite I8. auto. }
    assert (H10 : ∃ z : Seq, z = \{\ λ m v, v = Abs [x[n] - y[m]] \}\).
    { exists \{\ λ m v, v = Abs [x[n] - y[m]] \}\; auto. }
    destruct H10 as [z H10]. assert (H11 : IsSeq z).
    { unfold IsSeq. split.
      - unfold Function. rewrite H10. intros x0 y0 z0 I1 I2.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. apply I1.
      - apply AxiomI. intro z0; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (Abs [x[n] - y[z0]]). rewrite H10.
          apply AxiomII'. reflexivity. }
    assert (H12 : limit_seq z (Abs[x[n] - a])).
    { unfold limit_seq in H4. destruct H4 as [H4 I1]. split; auto.
      intros ε0 I2. apply I1 in I2 as I3. destruct I3 as [N0 I3].
      exists N0. intros n0 I4. apply I3 in I4 as I5.
      assert (I6 : z[n0] = Abs [x[n] - y[n0]]).
      { apply f_x; try apply H11. rewrite H10. apply AxiomII'.
        reflexivity. }
      rewrite I6. apply Rle_lt_trans with (r2 := Abs[y[n0] - a]); auto.
      assert (I7 : y[n0] - a = -((x[n] - y[n0])-(x[n] - a))). field.
      rewrite I7. rewrite <- Abs_eq_neg. apply Abs_abs_minus. }
    assert (H13 : ∃ w : Seq, w = \{\ λ m v, v = ε/2 \}\).
    { exists \{\ λ m v, v = ε/2 \}\. reflexivity. }
    destruct H13 as [w H13]. assert (H14 : IsSeq w).
    { split.
      - unfold Function. rewrite H13. intros x0 y0 z0 I1 I2.
        applyAxiomII' I1. applyAxiomII' I2. rewrite I2. apply I1.
      - apply AxiomI. intro z0; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (ε/2). rewrite H13. apply AxiomII'.
          reflexivity. }
    assert (H15 : limit_seq w (ε/2)).
    { split; auto. intros ε0 I1. exists 0%nat. intros n0 I2.
      assert (I3 : w[n0] = ε/2).
      { apply f_x; try apply H14. rewrite H13. apply AxiomII'.
        reflexivity. }
      rewrite I3. unfold Rminus. rewrite Rplus_opp_r. rewrite Abs_ge; auto.
      right; auto. }
    assert (H16 : lim z <= lim w).
    { apply Theorem2_5; [exists (Abs[x[n] - a]) | exists (ε/2) | idtac]; auto.
      exists N. intros n0 I1. assert (I2 : z[n0] = Abs[x[n] - y[n0]]).
      { apply f_x; try apply H11. rewrite H10. apply AxiomII'.
        reflexivity. }
      assert (I3 : w[n0] = ε/2).
      { apply f_x; try apply H14. rewrite H13. apply AxiomII'.
        reflexivity. }
      rewrite I2. rewrite I3. left. apply H9. apply I1. }
    rewrite lim_a with (a := (Abs[x[n] - a])) in H16; auto.
    rewrite lim_a with (a := (ε/2)) in H16; auto.
    apply Rle_lt_trans with (r2 := ε/2); auto. lra.
Qed.

End A2_3.

Export A2_3.