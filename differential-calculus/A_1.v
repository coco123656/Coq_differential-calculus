Require Export A_0.

Module A1.

(* 1.1 实数 *)

(* 阿基米德性 *)
Theorem Archimedes : ∀ a b, 0 < a -> 0 < b
  -> ∃ (n : nat), (INR n) * a > b.
Proof.
  intros a b H0 H7. 
  assert (H1 : b/a > 0).
  { apply Rmult_gt_0_compat; try lra.
    apply Rinv_0_lt_compat. apply H0. }
  generalize (archimed (b/a)). intros [H2 H3].
  clear H3.
  assert (H3 : IZR (up (b / a)) > 0). lra.
  apply lt_0_IZR in H3 as H4.
  exists (Z.to_nat (up (b / a))).
  rewrite INR_IZR_INZ.
  apply Z.lt_le_incl in H4.
  rewrite Z2Nat.id; auto.
  apply Rmult_lt_compat_r with (r := a) in H2; auto.
  assert (H6 : b/a*a = b). field. lra.
  rewrite H6 in H2. apply H2.
Qed.

(* 绝对值不等式 *)
Theorem Abs_Rge0 : ∀ x, Abs[x] >= 0.
Proof.
  intro x. destruct (total_order_T x 0) as [[H0 | H0] | H0].
  - assert (H1 : [x, -x] ∈ Abs).
    { apply <- AxiomII'. left. auto. }
    apply f_x in H1; try apply Fun_Abs. rewrite H1. left.
    apply Ropp_gt_lt_0_contravar. auto.
  - assert (H1 : [x, -x] ∈ Abs).
    { apply <- AxiomII'. right. split.
      - right; auto.
      - rewrite H0. apply Ropp_0. }
    rewrite H0 in *. rewrite Ropp_0 in H1. apply f_x in H1; try apply Fun_Abs.
    rewrite H1. right; auto.
  - assert (H1 : [x, x] ∈ Abs).
    { apply <- AxiomII'. right. split; auto. left; auto. }
    apply f_x in H1; try apply Fun_Abs. rewrite H1. left; auto.
Qed.

Theorem Abs_ge : ∀ a, a >= 0 -> Abs[a] = a.
Proof.
  intros a H0. assert (H1 : [a, a] ∈ Abs).
  { apply <- AxiomII'. right. split; auto. }
  apply f_x; auto. apply Fun_Abs.
Qed.

Theorem Abs_gt : ∀ a, a > 0 -> Abs[a] = a.
Proof.
  intros a H0. apply Rgt_ge in H0. apply Abs_ge; auto.
Qed.

Theorem Abs_lt : ∀ a, a < 0 -> Abs[a] = -a.
Proof.
  intros a H0. assert (H1 : [a, -a] ∈ Abs).
  { apply <- AxiomII'. left. split; auto. }
  apply f_x; auto. apply Fun_Abs.
Qed.

Theorem Abs_not_eq_0 : ∀ a, a <> 0 <-> Abs[a] > 0.
Proof.
  intro a. split; intro H0.
  - apply Rdichotomy in H0 as H1.
    destruct H1 as [H1 | H1].
    + rewrite Abs_lt; auto. apply Ropp_gt_lt_0_contravar; auto.
    + rewrite Abs_gt; auto.
  - intro H1. rewrite Abs_ge in H0.
    + apply Rgt_not_eq in H0. auto.
    + right; auto.
Qed.



Theorem Abs_eq_neg : ∀ a, Abs[a] = Abs[-a].
Proof.
  intro a. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. rewrite H1. destruct H0 as [H0 | H0].
    + apply Ropp_lt_gt_0_contravar in H0 as H2. apply Abs_lt in H2 as H3.
      rewrite H3. rewrite Ropp_involutive; auto.
    + rewrite H0. rewrite Ropp_0. symmetry. apply Abs_ge. right; auto.
  - apply Abs_lt in H0 as H1. apply Ropp_gt_lt_0_contravar in H0 as H2.
    apply Rgt_ge in H2 as H3. apply Abs_ge in H3 as H4.
    rewrite H4. auto.
Qed.

Theorem Abs_neg_pos : ∀ a, -Abs[a] <= a <= Abs[a].
Proof.
  intro a. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. rewrite H1. split.
    + destruct H0 as [H0 | H0].
      * left. apply (Ropp_lt_gt_0_contravar a) in H0 as H2.
        apply Rlt_trans with (r2 := 0); auto.
      * rewrite H0. rewrite Ropp_0. right; auto.
    + right; auto.
  - apply Abs_lt in H0 as H1. rewrite H1. rewrite Ropp_involutive. split.
    + right; auto.
    + apply Ropp_gt_lt_0_contravar in H0 as H2. left.
      apply Rlt_trans with (r2 := 0); auto.
Qed.


Theorem Abs_eq_0 : ∀ a, a = 0 <-> Abs[a] = 0.
Proof.
  intros. split; intro H0.
  - rewrite H0. apply Abs_ge. lra. 
  - pose proof (Abs_not_eq_0 a).
    pose proof (Req_dec a 0).
    destruct H1. auto. rewrite H0 in H. apply H in H1. 
    lra.
Qed.



Theorem Abs_R : ∀ a b, Abs[a] < b <-> -b < a < b.
Proof.
  intros a b. split.
  - intro H0. assert (H2 : b > 0).
    { destruct (Abs_Rge0 a) as [H1 | H1].
      - apply Rlt_trans with (r2 := Abs[a]); auto.
      - rewrite <- H1. auto. }
    destruct (total_order_T a 0) as [[H1 | H1] | H1].
    + apply Abs_lt in H1 as H3. rewrite H3 in H0. split.
      * apply Ropp_lt_cancel. rewrite Ropp_involutive. auto.
      * apply Rlt_trans with (r2 := 0); auto.
    + rewrite H1. split; auto. apply Ropp_lt_gt_0_contravar. auto.
    + assert (H3 : Abs[a] = a).
      { apply Abs_ge. left; auto. }
      rewrite H3 in H0. split; auto. apply Rlt_trans with (r2 := 0); auto.
      apply Ropp_lt_gt_0_contravar. auto.
  - intro H0. destruct H0 as [H0 H1].
    destruct (total_order_T a 0) as [[H2 | H2] | H2].
    + apply Abs_lt in H2 as H3. rewrite H3. apply Ropp_lt_cancel.
      rewrite Ropp_involutive. auto.
    + assert (H3 : Abs[a] = a).
      { apply Abs_ge. right; auto. }
      rewrite H3. auto.
    + assert (H3 : Abs[a] = a).
      { apply Abs_ge. left; auto. }
      rewrite H3. auto.
Qed.

Theorem Abs_le_R : ∀ a b, Abs[a] <= b <-> -b <= a <= b.
Proof.
  intros a b. split; intro H0.
  - destruct H0 as [H0 | H0].
    + apply Abs_R in H0 as H1. split.
      * left; apply H1.
      * left; apply H1.
    + rewrite <- H0. apply Abs_neg_pos.
  - assert (H5 : b >= 0).
    { apply NNPP. destruct H0 as [H0 H1].
      intro H2. destruct (Rge_lt b 0) as [H3 | H3]; auto.
      apply Ropp_gt_lt_0_contravar in H3 as H4.
      assert (I1 : -b <= b).
      { apply Rle_trans with (r2 := a); auto. }
      apply (Rle_not_gt (-b) b); auto.
      apply Rlt_trans with (r2 := 0); auto. }
    destruct H0 as [H0 H1]. destruct H0 as [H0 | H0].
    + destruct H1 as [H1 | H1].
      * left. apply Abs_R. split; auto.
      * rewrite H1 in *. right. apply Abs_ge; auto.
    + apply Ropp_eq_compat in H0. rewrite Ropp_involutive in H0.
      rewrite H0 in *. destruct H5 as [H5 | H5].
      * apply Ropp_lt_gt_0_contravar in H5. rewrite Ropp_involutive in H5.
        right. apply Abs_lt; auto.
      * rewrite H5. apply Ropp_eq_compat in H5.
        rewrite Ropp_involutive in H5. rewrite Ropp_0 in H5.
        rewrite H5. right. apply Abs_ge. right; auto.
Qed.

Theorem Abs_plus_le : ∀ a b, Abs[a+b] <= Abs[a] + Abs[b].
Proof.
  intros a b. generalize (Abs_neg_pos a). intro H0.
  generalize (Abs_neg_pos b). intro H1.
  destruct H0 as [H0 H2]. destruct H1 as [H1 H3].
  apply Abs_le_R. split.
  - rewrite Ropp_plus_distr. apply Rplus_le_compat; auto.
  - apply Rplus_le_compat; auto.
Qed.

Theorem Abs_minus_le : ∀ a b, Abs[a-b] <= Abs[a] + Abs[b].
Proof.
  intros a b. generalize (Abs_neg_pos a). intro H0.
  generalize (Abs_neg_pos (-b)). intro H1.
  rewrite <- Abs_eq_neg in H1.
  destruct H0 as [H0 H2]. destruct H1 as [H1 H3].
  apply Abs_le_R. split.
  - rewrite Ropp_plus_distr. apply Rplus_le_compat; auto.
  - apply Rplus_le_compat; auto.
Qed.

Theorem Abs_abs_minus : ∀ a b, Abs[Abs[a]-Abs[b]] <= Abs[a-b].
Proof.
  intros a b. destruct (Rlt_or_le a 0) as [H0 | H0].
  - apply Abs_lt in H0 as H1.
    destruct (Rlt_or_le b 0) as [H2 | H2].
    + apply Abs_lt in H2 as H3. rewrite H1; rewrite H3.
      right. assert (H4 : -a - -b = - (a-b)). field.
      rewrite H4. rewrite <- Abs_eq_neg. reflexivity.
    + apply Rle_ge in H2. apply Abs_ge in H2 as H3.
      rewrite H1; rewrite H3. assert (H4 : a-b < 0).
      { apply Rge_le in H2. apply Ropp_0_le_ge_contravar in H2 as H4.
        apply Rge_le in H4. unfold Rminus. assert (H5 : 0 = 0 + 0). field.
        rewrite H5. apply Rplus_lt_le_compat; auto. }
      apply Abs_lt in H4 as H5. rewrite H5. assert (H6 : -(a-b) = -a + b).
      field. rewrite H6. generalize (Rlt_or_le (-a-b) 0). intro H7.
      destruct H7 as [H7 | H7].
      * apply Abs_lt in H7 as H8. rewrite H8. assert (H9 : -(-a-b) = a + b).
        field. rewrite H9. apply Rplus_le_compat_r.
        apply Ropp_gt_lt_0_contravar in H0 as H10. left.
        apply Rlt_trans with (r2 := 0); auto.
      * apply Rle_ge in H7. apply Abs_ge in H7 as H8. rewrite H8.
        unfold Rminus. apply Rplus_le_compat_l. apply Rge_le in H2.
        apply Ropp_0_le_ge_contravar in H2 as H9.
        apply Rge_le in H9. eapply Rle_trans; eauto.
  - apply Rle_ge in H0 as H1. apply Abs_ge in H1 as H2.
    rewrite H2. destruct (Rlt_or_le b 0) as [H3 | H3].
    + apply Abs_lt in H3 as H4. rewrite H4. assert (H5 : a-b > 0).
      { apply Ropp_gt_lt_0_contravar in H3 as I1. unfold Rminus.
        assert (I2 : 0 = 0 + 0). field. rewrite I2.
        apply Rplus_ge_gt_compat; auto. }
      apply Abs_gt in H5 as H6. rewrite H6.
      generalize (Rlt_or_le (a--b) 0). intro H7.
      destruct H7 as [H7 | H7].
      * apply Abs_lt in H7 as H8. rewrite H8.
        assert (H9 : -(a--b) = -a -b). field. rewrite H9.
        unfold Rminus. apply Rplus_le_compat_r.
        apply Ropp_0_le_ge_contravar in H0 as H10. apply Rge_le in H10.
        eapply Rle_trans; eauto.
      * apply Rle_ge in H7. apply Abs_ge in H7 as H8. rewrite H8.
        assert (H9 : a--b = a+b). field. rewrite H9. unfold Rminus.
        apply Rplus_le_compat_l. lra.
    + apply Rle_ge in H3 as H4. apply Abs_ge in H4 as H5.
      rewrite H5. right. reflexivity.
Qed.

Theorem Abs_abs_minus' : ∀ a b, Abs[a]-Abs[b] <= Abs[a-b].
Proof.
  intros a b. generalize (Abs_neg_pos (Abs[a] - Abs[b])). intro H0.
  destruct H0 as [H0 H1]. generalize (Abs_abs_minus a b). intro H2.
  lra.
Qed.

Theorem Abs_mult : ∀ a b, Abs[a*b] = Abs[a]*Abs[b].
Proof.
  intros a b. destruct (Rge_lt a 0) as [H0 | H0].
  - apply Abs_ge in H0 as H1. destruct (Rge_lt b 0) as [H2 | H2].
    + apply Abs_ge in H2 as H3. rewrite H1; rewrite H3.
      apply Rmult_ge_compat_r with (r := b) in H0 as H4; auto.
      rewrite Rmult_0_l in H4. apply Abs_ge in H4 as H5. auto.
    + apply Abs_lt in H2 as H3. rewrite H1; rewrite H3.
      destruct H0 as [H0 | H0].
      * apply Rmult_lt_gt_compat_neg_l with (r := b) in H0 as H4; auto.
        rewrite (Rmult_comm b a) in H4. rewrite Rmult_0_r in H4.
        apply Abs_lt in H4 as H5. rewrite H5.
        apply Ropp_mult_distr_r.
      * rewrite H0 in *. repeat rewrite Rmult_0_l. auto.
  - apply Abs_lt in H0 as H1. rewrite H1. destruct (Rge_lt b 0) as [H2 | H2].
    + destruct H2 as [H2 | H2].
      * apply Rmult_lt_gt_compat_neg_l with (r := a) in H2 as H4; auto.
        rewrite Rmult_0_r in H4.
        apply Abs_lt in H4 as H5. rewrite H5.
        assert (H6 : Abs[b] = b).
        { apply Abs_ge. left; auto. }
        rewrite H6. apply Ropp_mult_distr_l.
      * rewrite H2 in *. rewrite Rmult_0_r. assert (H3 : Abs[0] = 0).
        { apply Abs_ge. right; auto. }
        rewrite H3. rewrite Rmult_0_r. auto.
    + apply Rmult_lt_gt_compat_neg_l with (r := a) in H2 as H3; auto.
      rewrite Rmult_0_r in H3. apply Abs_lt in H2 as H4.
      rewrite H4. assert (H5 : Abs[a*b] = a*b).
      { apply Abs_ge. left; auto. }
      rewrite H5. rewrite Rmult_opp_opp. auto.
Qed.

Theorem Abs_div : ∀ a b, b <> 0 -> Abs[a/b] = Abs[a]/Abs[b].
Proof.
  intros a b H0. unfold Rdiv in *. rewrite Abs_mult.
  assert (H1 : Abs[/b] = /Abs[b]).
  { destruct (Rge_lt b 0) as [H1 | H1].
    - destruct H1 as [H1 | H1].
      + apply Rinv_0_lt_compat in H1 as H2. assert (H3 : Abs[/b] = /b).
        { apply Abs_ge. left; auto. }
        rewrite H3. assert (H4 : Abs[b] = b).
        { apply Abs_ge. left; auto. }
        rewrite H4. auto.
      + exfalso; auto.
    - apply Rinv_lt_0_compat in H1 as H2. apply Abs_lt in H1.
      apply Abs_lt in H2. rewrite H1. rewrite H2.
      apply Ropp_inv_permute. auto. }
  rewrite H1. auto.
Qed.

Lemma Lemma1 : ∀ a b, a > 0 -> b > 0 -> 
   ∃ c, c > 0 /\ c < a /\ c < b.
Proof.
  intros a b H0 H1.
  destruct (Rlt_or_le a b) as [H2 | H2].
  - exists (a/2). repeat split; lra.
  - exists (b/2). repeat split; lra.
Qed.

Lemma Lemma1' : ∀ a b c, a > 0 -> b > 0 -> c > 0 -> 
   ∃ d, d > 0 /\ d < a /\ d < b /\ d < c.
Proof.
  intros a b c H0 H1 H2.
  destruct (Rlt_or_le a b) as [H3 | H3].
  - destruct (Rlt_or_le a c) as [H4 | H4].
    + exists (a/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
  - destruct (Rlt_or_le b c) as [H4 | H4].
    + exists (b/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
Qed.

Lemma Lemma1'' : ∀ a b c d, a > 0 -> b > 0 -> c > 0 -> d > 0 ->
   ∃ e, e > 0 /\ e < a /\ e < b /\ e < c /\ e < d.
Proof.
  intros a b c d H H1 H2 H3.
  destruct (Rlt_or_le a b). 
      - destruct (Rlt_or_le a c).
        + destruct (Rlt_or_le a d);
          [ exists (a / 2) | exists (d / 2)]; repeat split; lra.
        + destruct (Rlt_or_le c d);
          [ exists (c / 2)| exists (d / 2)]; repeat split; lra.
      - destruct (Rlt_or_le b c) as [L1 | L1].
        + destruct (Rlt_or_le d b) as [L2|L2];
          [ exists (d / 2) | exists (b / 2)]; repeat split; lra.
        + destruct (Rlt_or_le c d) as [L2|L2];
          [ exists (c / 2) | exists (d / 2)]; repeat split; lra.
Qed.

Lemma Lemma2 : ∀ a b, 0 < Abs[a] < b ->
  a <> 0 /\ -b < a < b.
Proof.
  intros a b [H0 H1].
  apply Abs_not_eq_0 in H0.
  apply Abs_R in H1. split; assumption.
Qed.



(* 1.2 数集 *)

(* 1.2.1 区间 *)

(* 开区间 *)
Definition OpenInterval1 (a b : R) := \{ λ x : R, x > a /\ x < b \}.
Notation "\( a , b \)" := (OpenInterval1 a b) (at level 5).

(* 闭区间 *)
Definition CloseInterval (a b : R) := \{ λ x : R, x >= a /\ x <= b \}.
Notation "\[ a , b \]" := (CloseInterval a b) (at level 5).

(* 半开半闭区间 *)
Definition CloseOpen (a b : R) := \{ λ x : R, x >= a /\ x < b \}.
Notation "\[ a , b \)" := (CloseOpen a b)(at level 5).

Definition OpenClose (a b : R) := \{ λ x : R, x > a /\ x <= b \}.
Notation "\( a , b \]" := (OpenClose a b)(at level 5).

(* 正无穷 *)
Definition ClosePositiveInf (a : R) := \{ λ x : R, x >= a \}.
Notation "\[ a , +∞ \)" := (ClosePositiveInf a)(at level 5).

Definition OpenPositiveInf (a : R) := \{ λ x : R, x > a \}.
Notation "\( a , +∞ \)" := (OpenPositiveInf a)(at level 5).

(* 负无穷 *)
Definition CloseNegativeInf (a : R) := \{ λ x : R, x <= a \}.
Notation "\( -∞ , a \]" := (CloseNegativeInf a)(at level 5).

Definition OpenNegativeInf (a : R) := \{ λ x : R, x < a \}.
Notation "\( -∞ , a \)" := (OpenNegativeInf a)(at level 5).

(* 邻域 *)
Definition Neighbor (a δ : R) := \{ λ x : R, Abs[x-a] < δ \}.

(* 左邻域 *)
Definition leftNeighbor (a δ : R) := \(a-δ, a\].

(* 右邻域 *)
Definition rightNeighbor (a δ : R) := \[a, a+δ\).

(* 去心邻域 *)
Definition Neighbor0 (a δ : R) := \{ λ x : R, 0 < Abs[x-a] < δ \}.

(* 左去心邻域 *)
Definition leftNeighbor0 (a δ : R) := \(a-δ, a\).

(* 右去心邻域 *)
Definition rightNeighbor0 (a δ : R) := \(a, a+δ\).


(* 1.2.2 有界集 确界原理 *)

(* 上界 *)
Definition Upper (A : sR) (M : R) := ∀ x, x ∈ A -> x <= M.

(* 下界 *)
Definition Lower (A : sR) (L : R) := ∀ x, x ∈ A -> x >= L.

(* 有界集 *)
Definition Bounded (A : sR) := ∃ M L : R, (Upper A M) /\ (Lower A L).

(* 上确界 *)
Definition sup (A : sR) (η : R) :=
    (Upper A η) /\ (∀ a : R, a < η -> (∃ x0, x0 ∈ A /\ x0 > a)).

(* 下确界 *)
Definition inf (A : sR) (ξ : R) :=
    (Lower A ξ) /\ (∀ b : R, b > ξ -> (∃ x0, x0 ∈ A /\ x0 < b)).

(* 区间上的上界函数*)
Definition UpIntervalBoundedFun (f : sR2) (D : sR) : Prop :=
    Function f /\ D = dom[f]
    /\ ∃ M : R, (∀ x : R, x ∈ D -> f[x] <= M).

(* 区间上的下界函数*)
Definition LowIntervalBoundedFun (f : sR2) (D : sR) : Prop :=
    Function f /\ D = dom[f]
    /\ ∃ L : R, (∀ x : R, x ∈ D -> f[x] >= L).

(* 定理1.1 确界原理 *)

(* 引理: 上确界原理 *)
Lemma Sup_principle : ∀ (A : sR), NotEmpty A ->
    ((∃ M, Upper A M) -> (∃ η, sup A η)).
Proof.
  intros A H0 H1.
  destruct H1 as [M H1]. unfold Upper in H1.
  assert (H2 : ∃ E, E = (fun x => x ∈ A)).
  { exists (fun x => x ∈ A). auto. }
  destruct H2 as [E H2]. assert (H3 : is_upper_bound E M).
  { unfold is_upper_bound. intros x H3. apply H1. rewrite H2 in H3. auto. }
  assert (H4 : bound E).
  { unfold bound. exists M. auto. }
  unfold NotEmpty in H0. assert (H5 : ∃ x : R, E x).
  { destruct H0 as [x H0]. exists x. rewrite H2. auto. }
  apply completeness in H5 as η; auto.
  destruct η as [η H6]. exists η. unfold is_lub in H6.
  destruct H6 as [H6 H7]. unfold sup. split.
  - unfold Upper. intros x H8. unfold is_upper_bound in H6. apply H6.
    rewrite H2. auto.
  - intros a H8. apply NNPP. intro H9.
    assert (H10 : ∀ x0 : R, ~ (x0 ∈ A /\ x0 > a)).
    { apply not_ex_all_not. auto. }
    assert (H11 : is_upper_bound E a).
    { unfold is_upper_bound. intros x H11.
      assert (H12 : ~ (x ∈ A /\ x > a)).
      { apply H10. }
      apply not_and_or in H12. rewrite H2 in H11.
      destruct H12 as [H12 | H12].
      - exfalso; auto.
      - apply Rnot_gt_le. auto. }
    apply H7 in H11 as H12. apply Rle_not_gt in H12. auto.
Qed.

(* 定理: 确界原理 *)
Theorem Sup_inf_principle : ∀ (A : sR), NotEmpty A ->
    ((∃ M, Upper A M) -> (∃ η, sup A η)) /\
    ((∃ L, Lower A L) -> (∃ ξ, inf A ξ)).
Proof.
  intros A H0. split.
  - apply Sup_principle. auto.
  - assert (H1 : ∃ B, B = \{ λ x, (-x) ∈ A \}).
    { exists \{ λ x, (-x) ∈ A \}; auto. }
    destruct H1 as [B H1].
    assert (H2 : NotEmpty B).
    { unfold NotEmpty in *. destruct H0 as [x H0]. exists (-x).
      rewrite H1. apply <- AxiomII. rewrite Ropp_involutive. auto. }
    intro H3. destruct H3 as [L H3].
    assert (H4 : ∃ M, Upper B M).
    { exists (-L). unfold Upper. intros x H4. unfold Lower in H3.
      rewrite H1 in H4. applyAxiomII H4. apply H3 in H4.
      apply Ropp_ge_contravar in H4. rewrite Ropp_involutive in H4.
      apply Rge_le. auto. }
    apply Sup_principle in H4 as H5; auto.
    destruct H5 as [η H5]. exists (-η). unfold inf. unfold sup in H5.
    destruct H5 as [H5 H6]. split.
    + unfold Lower. unfold Upper in H5. intros x H7.
      apply Ropp_ge_cancel. rewrite Ropp_involutive.
      apply Rle_ge. apply H5. rewrite H1. apply <- AxiomII.
      rewrite Ropp_involutive. auto.
    + intros b H7. apply Ropp_gt_contravar in H7.
      rewrite Ropp_involutive in H7. apply H6 in H7 as H8.
      destruct H8 as [x [H8 H9]]. exists (-x). split.
      * rewrite H1 in H8. applyAxiomII H8. auto.
      * apply Ropp_lt_cancel. rewrite Ropp_involutive. auto.
Qed.

(* 1.4 函数特性 *)

(* 1.4.1 有界函数 *)
Definition BoundedFun (f : sR2) : Prop :=
    Function f /\ ∃ M : R, (∀ x y : R, [x, y] ∈ f -> Abs[y] <= M).

(* 1.4.2 单调函数 *)

(* 增函数 *)
Definition IncreaseFun (f : sR2) : Prop :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 < x2 -> y1 <= y2).
(* 严格增函数 *)
Definition StrictlyIncreaseFun (f : sR2) : Prop :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 < x2 -> y1 < y2).

(* 减函数 *)
Definition DecreaseFun (f : sR2) :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 < x2 -> y1 >= y2).
(* 严格减函数 *)
Definition StrictlyDecreaseFun (f : sR2) :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 < x2 -> y1 > y2).

(* 定理1.2 *)
Theorem Theorem1_2_1 : ∀ (f : sR2), StrictlyIncreaseFun f
    -> StrictlyIncreaseFun (f﹣¹).
Proof.
  intros f H0. unfold StrictlyIncreaseFun in *. destruct H0 as [H0 H1]. split.
  - unfold Function in *. intros x y z H2 H3. apply -> AxiomII' in H2;
    simpl in H2. apply -> AxiomII' in H3; simpl in H3.
    destruct (total_order_T y z) as [[H4 | H4] | H4].
    + apply (H1 y x z x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. right; auto.
    + auto.
    + apply (H1 z x y x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. right; auto.
  - intros x1 y1 x2 y2 H2 H3 H4. apply -> AxiomII' in H2;
    simpl in H2. apply -> AxiomII' in H3; simpl in H3.
    destruct (total_order_T y1 y2) as [[H5 | H5] | H5].
    + auto.
    + exfalso. rewrite <- H5 in H3. apply (H0 y1 x1 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. right; auto.
    + exfalso. apply (H1 y2 x2 y1 x1) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. left; auto.
Qed.

Theorem Theorem1_2_2 : ∀ (f : sR2), StrictlyDecreaseFun f
    -> StrictlyDecreaseFun (f﹣¹).
Proof.
  intros f H0. unfold StrictlyDecreaseFun in *. destruct H0 as [H0 H1]. split.
  - unfold Function in *. intros x y z H2 H3. apply -> AxiomII' in H2;
    simpl in H2. apply -> AxiomII' in H3; simpl in H3.
    destruct (total_order_T y z) as [[H4 | H4] | H4].
    + apply (H1 y x z x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. left; auto.
    + auto.
    + apply (H1 z x y x) in H4 as H5; auto. exfalso.
      apply Rlt_not_ge with (r1 := x) (r2 := x); auto. left; auto.
  - intros x1 y1 x2 y2 H2 H3 H4. apply -> AxiomII' in H2;
    simpl in H2. apply -> AxiomII' in H3; simpl in H3.
    destruct (total_order_T y1 y2) as [[H5 | H5] | H5].
    + exfalso. apply (H1 y1 x1 y2 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. left; auto.
    + exfalso. rewrite <- H5 in H3. apply (H0 y1 x1 x2) in H2 as H6; auto.
      apply Rlt_not_ge with (r1 := x1) (r2 := x2); auto. right; auto.
    + auto.
Qed.

(* 1.4.3 奇偶函数 *)
(* 奇函数 *)
Definition OddFun (f : sR2) :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 = -x2 -> y1 = -y2) /\ (∀ x : R, x ∈ dom[f] -> (-x) ∈ dom[f]).

(* 偶函数 *)
Definition EvenFun (f : sR2) :=
    Function f /\ (∀ x1 y1 x2 y2 : R, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 = -x2 -> y1 = y2) /\ (∀ x : R, x ∈ dom[f] -> (-x) ∈ dom[f]).

(* 1.4.4 周期函数 *)
Definition PeriodicFun (f : sR2) := Function f /\ (∃ (zeta : R), zeta > 0 /\
    (∀ (x : R), x ∈ dom[f] -> ((x + zeta) ∈ dom[f] -> f[x + zeta] = f[x])
    /\ ((x - zeta) ∈ dom[f] -> f[x - zeta] = f[x]))).

End A1.

Export A1.