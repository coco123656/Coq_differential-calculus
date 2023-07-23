Require Export A_1.

Module A2_1.

(* 2.1 数列极限的概念 *)

(* 定义：数列 *)
Definition Seq := set (prod nat R).

Definition IsSeq (x : Seq) := Function x /\ dom[x] = Full nat.

(* 定义1: 数列极限 *)
Definition limit_seq (x : Seq) (a : R) := IsSeq x /\ ∀ ε : R, ε > 0 ->
    (∃ N : nat, ∀ n : nat, (n > N)%nat -> Abs[x[n] - a] < ε).

Definition limit_seq' (x : Seq) (a : R) := IsSeq x /\ ∀ ε : R, ε > 0 ->
    (Finite \{ λ u, x[u] ∉ (Neighbor a ε) \}).


Definition lim (x : Seq) : R := cR (\{ λ a, limit_seq x a \}).

(* 两种定义等价 *)
Theorem EqualLimit : ∀ (x : Seq) (a : R), (limit_seq x a <-> limit_seq' x a).
Proof.
  intros x a. unfold limit_seq; unfold limit_seq'. split; intro H1.
  - destruct H1 as [J1 H1]. split; auto.
    intros ε H2. apply H1 in H2 as H3. destruct H3 as [N H3].
    assert (H4 : ∃ A, A = \{ λ u, (u <= N)%nat \}).
    { exists \{ λ u, (u <= N)%nat \}. auto. }
    destruct H4 as [A H4]. assert (H5 : \{ λ u, x [u] ∉ (Neighbor a ε) \} ⊂ A).
    { intros z H5. applyAxiomII H5. rewrite H4. apply <- AxiomII.
      apply NNPP. intro H6. apply Nat.nle_gt in H6. apply H3 in H6 as H7.
      apply H5. apply <- AxiomII. auto. }
    apply SubSetFinite_N with (A := A); auto. unfold Finite.
    left. rewrite H4. apply NatFinite.
  - destruct H1 as [J1 H1]. split; auto.
    intros ε H2. apply H1 in H2 as H3. destruct H3 as [H3 | H3].
    + apply finite_maxN in H3 as H4. destruct H4 as [N H4].
      exists N. intros n H5. unfold maxN in H4.
      destruct H4 as [H4 H6]. apply NNPP. intro H7.
      assert (H8 : n ∈ \{ λ u : nat, x [u] ∉ (Neighbor a ε) \}).
      { apply <- AxiomII. intro I1. applyAxiomII I1. auto. }
      apply H6 in H8 as H9. apply le_not_gt in H9. auto.
    + exists 0%nat. intros n H4. apply NNPP. intro H5.
      assert (H6 : n ∈ \{ λ u : nat, x [u] ∉ (Neighbor a ε) \}).
      { apply <- AxiomII. intro I1. apply H5. applyAxiomII I1. auto. }
      rewrite H3 in H6. applyAxiomII H6. auto.
Qed.

(* 定义: 收敛数列 *)
Definition Convergence (x : Seq) := ∃ a : R, limit_seq x a.

(* 定义: 发散数列 *)
Definition Divergence (x : Seq) := IsSeq x /\ (∀ a : R, ~ limit_seq x a).

(* 定义2：无穷小数列 *)
Definition Infinitesimal (x : Seq) : Prop := limit_seq x 0.

(* 定理2.1 *)
Theorem Theorem2_1 : ∀ (x : Seq) (a : R), IsSeq x -> limit_seq x a <->
  Infinitesimal \{\ λ u v, v = x[u] - a \}\.
Proof.
  intros x a H0. split; intro H1.
  - unfold Infinitesimal. unfold limit_seq in *. destruct H1 as [H1 H2].
    assert (H10 : IsSeq \{\ λ u v, v = x [u] - a \}\ ).
    { unfold IsSeq in *. destruct H1 as [H1 H3]. split.
      - unfold Function. intros x0 y0 z0 I1 I2. applyAxiomII' I1.
        applyAxiomII' I2. rewrite I2. auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply <- AxiomII. auto.
        + apply <- AxiomII. exists (x[z] - a). apply <- AxiomII'. auto. }
    split; auto.
    intros ε H3. apply H2 in H3 as H4. destruct H4 as [N H4].
    exists N. intros n H5. apply H4 in H5 as H6. apply Abs_R.
    apply Abs_R in H6 as H7.
    destruct H10 as [H10 H11].
    assert (H8 : \{\ λ u v, v = x [u] - a \}\ [n] = x[n] - a).
    { apply f_x; auto. apply <- AxiomII'. auto. }
    rewrite H8. rewrite Rminus_0_r. auto.
  - unfold Infinitesimal in H1. unfold limit_seq in *. destruct H1 as [H1 H2].
    split; auto. intros ε H3. apply H2 in H3 as H4.
    destruct H4 as [N H4]. exists N. intros n H5. apply H4 in H5 as H6.
    rewrite Rminus_0_r in H6.
    assert (H7 : \{\ λ u v, v = x [u] - a \}\ [n] = x[n] - a).
    { apply f_x; try apply H1. apply <- AxiomII'. auto. }
    rewrite H7 in H6. auto.
Qed.

(* 定义3：无穷大数列 *)
Definition Infiniteseries (x : Seq) := IsSeq x /\ ∀ M : R, M >0 ->
    (∃ N : nat, ∀ n : nat, (n > N)%nat -> Abs [x[n]] > M ).

(* 定义4：正无穷大数列 *)
Definition PosInfiniteseries (x : Seq) := IsSeq x /\ ∀ M : R, M >0 ->
    (∃ N : nat, ∀ n : nat, (n > N)%nat -> x[n] > M ).

(* 定义4'：负无穷大数列 *)
Definition NegInfiniteseries (x : Seq) := IsSeq x /\ ∀ M : R, M >0 ->
    (∃ N : nat, ∀ n : nat, (n > N)%nat -> x[n] < -M ).



End A2_1.

Export A2_1.