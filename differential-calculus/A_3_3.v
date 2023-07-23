Require Export A_3_2.

Module A3_3.

(* 3.3 函数极限存在的条件 *)

(* 定理3.8 归结原则 *)
Theorem Theorem3_8 : ∀ (f : Fun) (x0 δ' A : R), Function f
  -> δ' > 0 -> Neighbor0 x0 δ' ⊂ dom[f]
  -> limit f x0 A
  <-> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ Neighbor0 x0 δ'
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2. split.
  - intro H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
    intros x H7 H8 H9. unfold limit_seq.
    assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
    { unfold IsSeq. split.
      - unfold Function. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1. applyAxiomII' I2.
        rewrite I2; auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (f[x[z]]).
          apply AxiomII'. reflexivity. }
    split; auto. intros ε H11.
    apply H6 in H11 as H12.
    destruct H12 as [δ [[H12 H13] H14]].
    apply H9 in H12 as H15.
    destruct H15 as [N H15]. exists N.
    intros n H16. apply H15 in H16 as H17.
    assert (H18 : Abs[x[n] - x0] > 0).
    { assert (I2 : x[n] ∈ ran[x]).
      { destruct H7 as [I2 I3].
        apply fx_ran; auto. rewrite I3.
        apply AxiomII. reflexivity. }
      apply H8 in I2. applyAxiomII I2.
      apply I2. }
    assert (H19 : 0 < Abs[x[n] - x0] < δ). lra.
    apply H14 in H19.
    assert (H20 : \{\ λ(n0 : nat)(v : R),
      v = f [x [n0]] \}\ [n] = f[x[n]]).
    { apply f_x; try apply H10. apply AxiomII'.
      reflexivity. }
    rewrite H20. apply H19.
  - intro H3. apply NNPP. intro H4.
    unfold limit in H4. apply not_and_or in H4.
    destruct H4 as [H4 | H4]; auto.
    apply not_ex_all_not with (n := δ') in H4.
    apply not_and_or in H4;
    destruct H4 as [H4 | H4]; auto.
    apply not_and_or in H4;
    destruct H4 as [H4 | H4]; auto.
    apply not_all_ex_not in H4.
    destruct H4 as [ε0 H4]. apply imply_to_and in H4.
    destruct H4 as [H4 H5].
    assert (H6 : ∀ δ, ~ (0 < δ < δ' /\
      (∀x : R,0 < Abs [x - x0] < δ -> Abs [f [x] - A] < ε0))).
    { apply not_ex_all_not; apply H5. }
    assert (H7 : ∃ (x : Seq), x = \{\ λ n v, v =
      cR \{λ u, 0 < Abs [u - x0] < δ'/(INR (n + 2))
      /\ Abs [f [u] - A] >= ε0 \} \}\).
    { exists (\{\ λ n v, v =
      cR \{λ u, 0 < Abs [u - x0] < δ'/(INR (n + 2))
      /\ Abs [f [u] - A] >= ε0 \} \}\); reflexivity. }
    destruct H7 as [x H7].
    assert (H8 : IsSeq x).
    { split.
      - unfold Function. rewrite H7. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2; apply I1.
      - apply AxiomI. intro z; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (cR \{λ u, 0 < Abs [u - x0]
            < δ'/(INR (z + 2)) /\ Abs [f [u] - A] >= ε0 \}).
          rewrite H7. apply AxiomII'. reflexivity. }
    generalize H8. intro H9.
    destruct H9 as [H9 H10].
    assert (H11 : ∀δ : R, 0 < δ < δ'
      -> NotEmpty \{λ u, 0 < Abs [u - x0] < δ
        /\ Abs [f [u] - A] >= ε0 \}).
    { intros δ I1. generalize (H6 δ). intro I2.
      apply not_and_or in I2.
      destruct I2 as [I2 | I2]; [exfalso; auto | idtac].
      apply not_all_ex_not in I2.
      destruct I2 as [u I2].
      apply imply_to_and in I2.
      destruct I2 as [I2 I3].
      exists u. apply AxiomII.
      split; auto; lra. }
    assert (H12 : ∀ n, 0 < δ' / INR (n + 2) < δ').
    { intro n. assert (I1 : 2 <= INR (n + 2)).
      { assert (I1 : 2 = INR (2%nat)).
        { simpl. field. }
        rewrite I1. apply le_INR.
        rewrite Nat.add_comm. apply Nat.le_add_r. }
      assert (I2 : INR (n + 2) > 1). lra.
      assert (I3 : 0 < 1 * INR (n + 2)). lra.
      apply Rinv_lt_contravar in I2; auto.
      apply Rmult_lt_compat_l with (r := δ') in I2; auto.
      assert (I4 : δ' * / 1 = δ'). field.
      rewrite I4 in I2. split; auto.
      apply Rmult_gt_0_compat; auto.
      apply Rinv_0_lt_compat. lra. }
    assert (H13 : ran[x] ⊂ Neighbor0 x0 δ').
    { intros u I1. applyAxiomII I1.
      destruct I1 as [n I1].
      rewrite H7 in I1. applyAxiomII' I1.
      generalize (H12 n). intro I2.
      apply H11 in I2 as I3.
      apply AxiomcR in I3. rewrite <- I1 in I3.
      applyAxiomII I3. destruct I3 as [I3 I4].
      apply AxiomII. lra. }
    assert (H14 : limit_seq x x0).
    { split; auto. intros ε I1.
      assert (I2 : ∃ N, δ' / INR (N + 2) < ε).
      { generalize (Archimedes ε δ' I1 H1).
        intros [N J1]. exists N.
        rewrite Rmult_comm in J1.
        assert (J2 : INR (N + 2) > INR N).
        { apply lt_INR. apply Nat.lt_add_pos_r.
          apply Nat.lt_0_2. }
        generalize (pos_INR N). intro J3.
        assert (J4 : 0 < INR (N + 2)). lra.
        apply Rmult_lt_compat_l with (r := ε) in J2; auto.
        assert (J5 : δ' < ε * INR (N + 2)). lra.
        apply Rinv_0_lt_compat in J4 as J6.
        apply Rmult_lt_compat_r with
          (r := / INR (N + 2)) in J5; auto.
        assert (J7 : ε * INR (N + 2) * /INR (N + 2) = ε).
        field. lra.
        rewrite J7 in J5. apply J5. }
      destruct I2 as [N I2]. exists N.
      intros n I3. assert (I4 : n ∈ dom[x]).
      { rewrite H10. apply AxiomII. reflexivity. }
      apply x_fx in I4 as I5; auto.
      pattern x at 2 in I5.
      rewrite H7 in I5. applyAxiomII' I5.
      generalize (H12 n). intro I6.
      apply H11 in I6 as I7.
      apply AxiomcR in I7. rewrite <- I5 in I7.
      applyAxiomII I7. destruct I7 as [I7 I8].
      assert (I9 : δ' / INR (n + 2) < δ' / INR (N + 2)).
      { apply Rmult_lt_compat_l; auto.
        assert (I9 : INR (n + 2) > INR (N + 2)).
        { apply lt_INR. apply plus_lt_compat_r.
          apply I3. }
        generalize (pos_INR N). intro I10.
        assert (I11 : INR (N + 2) > INR N).
        { apply lt_INR. apply Nat.lt_add_pos_r.
          apply Nat.lt_0_2. }
        apply Rinv_lt_contravar; auto.
        apply Rmult_gt_0_compat; lra. }
      lra. }
    generalize (H3 x H8 H13 H14). intros [H15 H16].
    generalize (H16 ε0 H4). intros [N H17].
    assert (H18 : (S N) ∈ dom[x]).
    { rewrite H10. apply AxiomII. reflexivity. }
    apply x_fx in H18 as H19; auto.
    pattern x at 2 in H19.
    rewrite H7 in H19. apply -> AxiomII' in H19.
    lazy beta in H19.
    generalize (H12 (S N)). intro H20.
    apply H11 in H20. apply AxiomcR in H20.
    rewrite <- H19 in H20.
    apply -> AxiomII in H20. lazy beta in H20.
    destruct H20 as [H20 H21].
    generalize (gt_Sn_n N). intro H22.
    apply H17 in H22.
    assert (H23 : \{\ λ n v, v = f[x[n]] \}\ [S N]
      = f[x[S N]]).
    { apply f_x; try apply H15. apply AxiomII'.
      reflexivity. }
    rewrite H23 in H22. lra.
Qed.

Theorem Theorem3_8' : ∀ (f : Fun) (x0 A : R), Function f
  -> x0 ∈ dom[f] -> f[x0] = A -> limit f x0 A
  -> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ dom[f]
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3.
  destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (f[x[z]]).
        apply AxiomII'. reflexivity. }
  split; auto. intros ε H11.
  apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]].
  apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N.
  intros n H16. apply H15 in H16 as H17.
  assert (H18 : Abs[x[n] - x0] >= 0).
  { apply Abs_Rge0. }
  assert (H19 : 0 <= Abs[x[n] - x0] < δ). lra.
  assert (H21 : Abs [f [x[n]] - A] < ε).
  { assert (I1 : 0 < Abs [x [n] - x0] < δ \/ Abs [x [n] - x0] = 0).
    lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - assert (I2 : x[n] - x0 = 0).
      { apply NNPP. intro J1. apply Abs_not_eq_0 in J1. lra. }
      apply Rminus_diag_uniq_sym in I2.
      rewrite <- I2. rewrite H2. unfold Rminus. rewrite Rplus_opp_r.
      rewrite Abs_ge; lra. }
  assert (H20 : \{\ λ(n0 : nat)(v : R),
    v = f [x [n0]] \}\ [n] = f[x[n]]).
  { apply f_x; try apply H10. apply AxiomII'.
    reflexivity. }
  rewrite H20. assumption.
Qed.

Theorem Theorem3_8_1' : ∀ (f : Fun) (x0 A : R), Function f
  -> x0 ∈ dom[f] -> f[x0] = A -> limit_pos f x0 A
  -> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ dom[f]
    -> (∀ n, x0 <= x[n])
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3.
  destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H8' H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (f[x[z]]).
        apply AxiomII'. reflexivity. }
  split; auto. intros ε H11.
  apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]].
  apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N.
  intros n H16. apply H15 in H16 as H17.
  assert (H19 : x0 <= x[n] < x0 + δ).
  { apply Abs_R in H17. generalize (H8' n); intro I1. lra. }
  assert (H21 : Abs [f [x[n]] - A] < ε).
  { assert (I1 : x0 < x[n] < x0 + δ \/ x[n] = x0).
    lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - rewrite I1. rewrite H2. unfold Rminus. rewrite Rplus_opp_r.
      rewrite Abs_ge; lra. }
  assert (H20 : \{\ λ(n0 : nat)(v : R),
    v = f [x [n0]] \}\ [n] = f[x[n]]).
  { apply f_x; try apply H10. apply AxiomII'.
    reflexivity. }
  rewrite H20. assumption.
Qed.

Theorem Theorem3_8_2' : ∀ (f : Fun) (x0 A : R), Function f
  -> x0 ∈ dom[f] -> f[x0] = A -> limit_neg f x0 A
  -> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ dom[f]
    -> (∀ n, x[n] <= x0)
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 A H0 H1 H2 H3.
  destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H8' H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (f[x[z]]).
        apply AxiomII'. reflexivity. }
  split; auto. intros ε H11.
  apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]].
  apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N.
  intros n H16. apply H15 in H16 as H17.
  assert (H19 : x0 - δ < x[n] <= x0 ).
  { apply Abs_R in H17. generalize (H8' n); intro I1. lra. }
  assert (H21 : Abs [f [x[n]] - A] < ε).
  { assert (I1 : x0 - δ < x[n] < x0 \/ x[n] = x0).
    lra. destruct I1 as [I1 | I1].
    - apply H14 in I1. assumption.
    - rewrite I1. rewrite H2. unfold Rminus. rewrite Rplus_opp_r.
      rewrite Abs_ge; lra. }
  assert (H20 : \{\ λ(n0 : nat)(v : R),
    v = f [x [n0]] \}\ [n] = f[x[n]]).
  { apply f_x; try apply H10. apply AxiomII'.
    reflexivity. }
  rewrite H20. assumption.
Qed.

Theorem Theorem3_8_1 : ∀ (f : Fun) (x0 δ' A : R), Function f
  -> δ' > 0 -> rightNeighbor0 x0 δ' ⊂ dom[f]
  -> limit_pos f x0 A
  -> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ rightNeighbor0 x0 δ'
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2 H3.
  destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (f[x[z]]).
        apply AxiomII'. reflexivity. }
  split; auto. intros ε H11.
  apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]].
  apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N.
  intros n H16. apply H15 in H16 as H17.
  assert (H18 : x0 < x[n]).
  { assert (I2 : x[n] ∈ ran[x]).
    { destruct H7 as [I2 I3].
      apply fx_ran; auto. rewrite I3.
      apply AxiomII. reflexivity. }
    apply H8 in I2. applyAxiomII I2. lra. }
  apply Abs_R in H17.
  assert (H19 : x0 < x[n] < x0 + δ). lra.
  apply H14 in H19.
  assert (H20 : \{\ λ(n0 : nat)(v : R),
    v = f [x [n0]] \}\ [n] = f[x[n]]).
  { apply f_x; try apply H10. apply AxiomII'.
    reflexivity. }
  rewrite H20. apply H19.
Qed.

Theorem Theorem3_8_2 : ∀ (f : Fun) (x0 δ' A : R), Function f
  -> δ' > 0 -> leftNeighbor0 x0 δ' ⊂ dom[f]
  -> limit_neg f x0 A
  -> ∀ (x : Seq), IsSeq x -> ran[x] ⊂ leftNeighbor0 x0 δ'
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2 H3.
  destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
  intros x H7 H8 H9. unfold limit_seq.
  assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
  { unfold IsSeq. split.
    - unfold Function. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2; auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (f[x[z]]).
        apply AxiomII'. reflexivity. }
  split; auto. intros ε H11.
  apply H6 in H11 as H12.
  destruct H12 as [δ [[H12 H13] H14]].
  apply H9 in H12 as H15.
  destruct H15 as [N H15]. exists N.
  intros n H16. apply H15 in H16 as H17.
  assert (H18 : x[n] < x0).
  { assert (I2 : x[n] ∈ ran[x]).
    { destruct H7 as [I2 I3].
      apply fx_ran; auto. rewrite I3.
      apply AxiomII. reflexivity. }
    apply H8 in I2. applyAxiomII I2. lra. }
  apply Abs_R in H17.
  assert (H19 : x0 - δ < x[n] < x0). lra.
  apply H14 in H19.
  assert (H20 : \{\ λ(n0 : nat)(v : R),
    v = f [x [n0]] \}\ [n] = f[x[n]]).
  { apply f_x; try apply H10. apply AxiomII'.
    reflexivity. }
  rewrite H20. apply H19.
Qed.

(* 定理3.9 归结原则(右极限) *)

Fixpoint Fun_Theorem3_9 (f : Fun) (n : nat) (x0 δ' A ε0 : R) :=
  match n with
  | O => cR \{λ u, x0 < u < x0 + δ'/2
      /\ Abs [f [u] - A] >= ε0 \}
  | S n' => cR \{λ u, x0 < u < x0 +
      ((Fun_Theorem3_9 f n' x0 δ' A ε0)-x0)/(INR (n' + 3))
      /\ Abs [f [u] - A] >= ε0 \}
  end.

(* 归结原则(右极限) *)
Theorem Theorem3_9 : ∀ (f : Fun) (x0 δ' A : R), Function f
  -> δ' > 0 -> rightNeighbor0 x0 δ' ⊂ dom[f]
  ->
    limit_pos f x0 A
  <->
    ∀ (x : Seq), DecreaseSeq x -> ran[x] ⊂ rightNeighbor0 x0 δ'
    -> limit_seq x x0
    -> limit_seq \{\ λ n v, v = f[x[n]] \}\ A.
Proof.
  intros f x0 δ' A H0 H1 H2. split.
  - intro H3. destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
    intros x [H7 H30] H8 H9. unfold limit_seq.
    assert (H10 : IsSeq \{\ λ n v, v = f[x[n]] \}\ ).
    { unfold IsSeq. split.
      - unfold Function. intros x1 y1 z1 I1 I2.
        applyAxiomII' I1. applyAxiomII' I2.
        rewrite I2; auto.
      - apply AxiomI. intro z; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (f[x[z]]).
          apply AxiomII'. reflexivity. }
    split; auto. intros ε H11.
    apply H6 in H11 as H12.
    destruct H12 as [δ [[H12 H13] H14]].
    apply H9 in H12 as H15.
    destruct H15 as [N H15]. exists N.
    intros n H16. apply H15 in H16 as H17.
    assert (H18 : x[n] - x0 > 0).
    { assert (I2 : x[n] ∈ ran[x]).
      { destruct H7 as [I2 I3].
        apply fx_ran; auto. rewrite I3.
        apply AxiomII. reflexivity. }
      apply H8 in I2. applyAxiomII I2.
      lra. }
    assert (H19 : x0 < x[n] < x0 + δ).
    { rewrite Abs_gt in H17; auto. lra. }
    apply H14 in H19.
    assert (H20 : \{\ λ(n0 : nat)(v : R),
      v = f [x [n0]] \}\ [n] = f[x[n]]).
    { apply f_x; try apply H10. apply AxiomII'.
      reflexivity. }
    rewrite H20. apply H19.
  - intro H3. apply NNPP. intro H4.
    unfold limit in H4. apply not_and_or in H4.
    destruct H4 as [H4 | H4]; auto.
    apply not_ex_all_not with (n := δ') in H4.
    apply not_and_or in H4;
    destruct H4 as [H4 | H4]; auto.
    apply not_and_or in H4;
    destruct H4 as [H4 | H4]; auto.
    apply not_all_ex_not in H4.
    destruct H4 as [ε0 H4]. apply imply_to_and in H4.
    destruct H4 as [H4 H5].
    assert (H6 : ∀ δ, ~ (0 < δ < δ' /\
      (∀x : R,x0 < x < x0 + δ -> Abs [f [x] - A] < ε0))).
    { apply not_ex_all_not; apply H5. }
    assert (H7 : ∃ (x : Seq), x =
      \{\ λ n v, v = Fun_Theorem3_9 f n x0 δ' A ε0 \}\).
    { exists (\{\ λ n v, v =
      Fun_Theorem3_9 f n x0 δ' A ε0 \}\); reflexivity. }
    destruct H7 as [x H7].
    assert (H8 : IsSeq x).
    { split.
      - unfold Function. rewrite H7.
        intros x1 y1 z1 J1 J2.
        applyAxiomII' J1. applyAxiomII' J2.
        rewrite J2. apply J1.
      - apply AxiomI. intro z; split; intro J1.
        + apply AxiomII. reflexivity.
        + apply AxiomII.
          exists (Fun_Theorem3_9 f z x0 δ' A ε0).
          rewrite H7. apply AxiomII'.
          reflexivity. }
    assert (H9 : ∀ n, x[n] = Fun_Theorem3_9 f n x0 δ' A ε0).
    { intro n. apply f_x; try apply H8.
      rewrite H7. apply AxiomII'.
      reflexivity. }
    assert (H10 : ∀ n, x0 < (Fun_Theorem3_9 f n x0 δ' A ε0) < x0 + δ'
      /\ NotEmpty \{λ u, x0 < u < x0 +
        ((Fun_Theorem3_9 f n x0 δ' A ε0)-x0)/(INR (n + 3))
        /\ Abs [f [u] - A] >= ε0 \}).
    { intro n. induction n as [|n IHn].
      - assert (I1 : x0 < Fun_Theorem3_9 f 0 x0 δ' A ε0 < x0 + δ').
        { simpl. generalize (H6 (δ'/2)). intro I1.
          apply not_and_or in I1.
          destruct I1 as [I1 | I1]; try lra.
          apply not_all_ex_not in I1.
          destruct I1 as [xn I1]. apply imply_to_and in I1.
          assert (I2 : NotEmpty \{ λ u : R, x0 < u < x0 + δ' / 2
              /\ Abs [f [u] - A] >= ε0 \}).
          { exists xn. apply AxiomII. split; lra. }
          apply AxiomcR in I2 as I3.
          applyAxiomII I3. lra. }
        split; auto. generalize (H6
          (((Fun_Theorem3_9 f 0 x0 δ' A ε0)-x0)/3)).
        intro I2. apply not_and_or in I2.
        destruct I2 as [I2 | I2]; try lra.
        apply not_all_ex_not in I2.
        destruct I2 as [xn I2].
        apply imply_to_and in I2.
        exists xn. apply AxiomII.
        assert (I3 : INR(0+3) = 3).
        { simpl. field. }
        rewrite I3. split; lra.
      - destruct IHn as [IHn1 IHn2].
        assert (I1 : x0 < Fun_Theorem3_9
            f (S n) x0 δ' A ε0 < x0 + δ').
        { apply AxiomcR in IHn2. applyAxiomII IHn2.
          simpl. split; try lra.
          assert (I1 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)
            / INR (n + 3) < (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)).
          { assert (J1 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0) > 0).
            lra. assert (J2 : INR (n+3) > 1).
            { assert (K1 : 1 = INR 1).
              { simpl. reflexivity. }
              rewrite K1. apply lt_INR.
              apply Nat.lt_lt_add_l.
              apply lt_n_S. apply Nat.lt_0_2. }
            assert (J3 : 0 < 1*INR (n+3)).
            { apply Rmult_gt_0_compat; try apply Rlt_0_1.
              lra. }
            apply Rinv_lt_contravar in J2; auto.
            apply Rmult_lt_compat_l with
              (r := (Fun_Theorem3_9 f n x0 δ' A ε0 - x0))
               in J2; auto. lra. }
          lra. }
        split; auto. generalize (H6
          (((Fun_Theorem3_9 f (S n) x0 δ' A ε0)-x0)/INR (S n + 3))).
        intro I2. apply not_and_or in I2.
        destruct I2 as [I2 | I2].
        + exfalso. apply I2.
          assert (I3 : (Fun_Theorem3_9 f (S n) x0 δ' A ε0 - x0)
            / INR ((S n) + 3) < (Fun_Theorem3_9 f (S n) x0 δ' A ε0 - x0)).
          { assert (J1 : (Fun_Theorem3_9 f (S n) x0 δ' A ε0 - x0) > 0).
            lra. assert (J2 : INR ((S n)+3) > 1).
            { assert (K1 : 1 = INR 1).
              { simpl. reflexivity. }
              rewrite K1. apply lt_INR.
              apply Nat.lt_lt_add_l.
              apply lt_n_S. apply Nat.lt_0_2. }
            assert (J3 : 0 < 1*INR ((S n)+3)).
            { apply Rmult_gt_0_compat; try apply Rlt_0_1.
              lra. }
            apply Rinv_lt_contravar in J2; auto.
            apply Rmult_lt_compat_l with
              (r := (Fun_Theorem3_9 f (S n) x0 δ' A ε0 - x0))
               in J2; auto. lra. }
          split; try lra. assert (I4 : INR (S n + 3) > 0).
          { assert (J1 : 0 = (INR 0%nat)). reflexivity.
            rewrite J1. apply lt_INR.
            apply lt_plus_trans. apply gt_Sn_O. }
          apply Rinv_0_lt_compat in I4.
          apply Rmult_gt_0_compat; lra.
        + apply not_all_ex_not in I2.
          destruct I2 as [xn I2].
          apply imply_to_and in I2.
          exists xn. apply AxiomII.
          split; lra. }
    assert (H11 : DecreaseSeq x).
    { split; auto.
      intro n. rewrite H9. rewrite H9.
      simpl. generalize (H10 n). intro I1.
      destruct I1 as [I1 I2].
      apply AxiomcR in I2. applyAxiomII I2.
      assert (I3 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)
            / INR (n + 3) < (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)).
      { assert (J1 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0) > 0).
        lra. assert (J2 : INR (n+3) > 1).
        { assert (K1 : 1 = INR 1).
          { simpl. reflexivity. }
          rewrite K1. apply lt_INR.
          apply Nat.lt_lt_add_l.
          apply lt_n_S. apply Nat.lt_0_2. }
        assert (J3 : 0 < 1*INR (n+3)).
        { apply Rmult_gt_0_compat; try apply Rlt_0_1.
          lra. }
        apply Rinv_lt_contravar in J2; auto.
        apply Rmult_lt_compat_l with
          (r := (Fun_Theorem3_9 f n x0 δ' A ε0 - x0))
           in J2; auto. lra. }
      lra. }
    assert (H12 : ran[ x] ⊂ rightNeighbor0 x0 δ').
    { intros z I1. applyAxiomII I1.
      destruct I1 as [n I1]. apply f_x in I1; try apply H8.
      rewrite <- I1. rewrite H9. apply AxiomII.
      apply H10. }
    assert (H13 : ∀ n, x0 < x[n] < x0 + δ'/(INR (n+2))).
    { intro n. rewrite H9. induction n as [|n IHn].
      - simpl. generalize (H10 0%nat). intro I1.
        destruct I1 as [I1 I2].
        assert (I3 : NotEmpty \{ λ u : R,x0 < u < x0 + δ' / 2
          /\ Abs [f [u] - A] >= ε0 \}).
        { destruct I2 as [xn I2]. exists xn.
          apply -> AxiomII in I2. lazy beta in I2.
          destruct I2 as [I2 I3]. apply AxiomII.
          split; auto. assert (I4 : INR (0+3) = 3).
          { simpl. field. }
          rewrite I4 in I2. lra. }
        apply AxiomcR in I3. applyAxiomII I3. lra.
      - simpl Fun_Theorem3_9.
        assert (I1 : (S n + 2 = n + 3)%nat).
        { assert (J1 : (3 = 1 + 2)%nat). reflexivity.
          rewrite J1. rewrite plus_assoc.
          assert (J2 : (S n = n + 1)%nat).
          { rewrite Nat.add_comm. reflexivity. }
          rewrite J2. reflexivity. }
        rewrite I1. generalize (H10 n). intro I2.
        destruct I2 as [I2 I3].
        apply AxiomcR in I3. applyAxiomII I3.
        assert (I4 : (Fun_Theorem3_9 f n x0 δ' A ε0 - x0)
          / INR (n + 3) < δ' / INR (n + 3)).
        { assert (J1 : INR (n + 3) > 0).
          { assert (K1 : 0 = INR 0).
            { simpl. reflexivity. }
            rewrite K1. apply lt_INR.
            apply Nat.lt_lt_add_l.
            apply Nat.lt_lt_succ_r.
            apply Nat.lt_0_2. }
          apply Rinv_0_lt_compat in J1.
          apply Rmult_lt_compat_r; auto. lra. }
        lra. }
    assert (H14 : limit_seq x x0).
    { split; auto. intros ε I1.
      generalize (Archimedes ε δ'). intro I2.
      generalize (I2 I1 H1). intro I3.
      destruct I3 as [N I3]. exists N.
      intros n I4. generalize (H13 n).
      intro I5. assert (I6 : INR (n + 2) > INR N).
      { apply lt_INR. apply lt_plus_trans. apply I4. }
      assert (I7 : x[n] - x0 > 0). lra.
      rewrite Abs_gt; auto.
      assert (I8 : 0 < INR N).
      { destruct (pos_INR N) as [J1 | J1]; auto.
        exfalso. rewrite <- J1 in I3.
        rewrite Rmult_0_l in I3. lra. }
      assert (I9 : 0 < INR (n + 2)). lra.
      assert (I10 : 0 < (INR N) * (INR (n + 2))).
      { apply Rmult_gt_0_compat; auto. }
      apply Rinv_lt_contravar in I6; auto.
      assert (I11 : δ' / INR (n + 2) < δ' / INR N).
      { apply Rmult_lt_compat_l; auto. }
      assert (I12 : δ' / INR N < ε).
      { apply Rmult_lt_reg_r with (r := INR N); auto.
        unfold Rdiv. rewrite Rmult_assoc.
        rewrite Rinv_l; lra. }
      lra. }
    generalize (H3 x H11 H12 H14). intro H15.
    unfold limit_seq in H15. destruct H15 as [H15 H16].
    generalize (H16 ε0 H4). intro H17.
    destruct H17 as [N H17].
    generalize (H17 (S N) (gt_Sn_n N)). intro H18.
    assert (H19 : \{\ λ n v, v = f [x [n]] \}\ [S N]
      = f[x[S N]]).
    { apply f_x; try apply H15. apply AxiomII'.
      reflexivity. }
    rewrite H19 in H18. generalize (H9 (S N)).
    intro H20. simpl in H20.
    generalize (H10 N). intros [H21 H22].
    apply AxiomcR in H22. rewrite <- H20 in H22.
    applyAxiomII H22. lra.
Qed.

(* 定理3.10 单调有界定理 *)
Theorem Theorem3_10 : ∀ (f : Fun) (x0 δ' : R),
  δ' > 0
  -> IntervalMonotonicFun f (rightNeighbor0 x0 δ')
  -> IntervalBoundedFun f (rightNeighbor0 x0 δ')
  -> (∃ A, limit_pos f x0 A).
Proof.
  intros f x0 δ' H0 [H1 | H1] [H2 [H3 [M H4]]].
  - assert (H5 : ∃ Range, Range = \{ λ y,
        ∃ x, (x ∈ rightNeighbor0 x0 δ') /\ y = f[x] \}).
    { exists \{ λ y, ∃ x, (x ∈ rightNeighbor0 x0 δ')
        /\ y = f[x] \}; reflexivity. }
    destruct H5 as [Range H5].
    assert (H6 : NotEmpty Range).
    { exists (f[x0+δ'/2]). rewrite H5.
      apply AxiomII. exists (x0+δ'/2).
      split; auto. apply AxiomII. split; lra. }
    assert (H7 : (∃ L, Lower Range L)).
    { exists (-M). unfold Lower. intros y I1.
      rewrite H5 in I1. applyAxiomII I1.
      destruct I1 as [x [I1 I2]].
      rewrite I2. apply H4 in I1.
      apply Abs_le_R in I1. lra. }
    apply Sup_inf_principle in H6 as [H8 H9].
    apply H9 in H7. destruct H7 as [A [H7 H10]].
    exists A. unfold limit_pos. split; auto.
    exists δ'. repeat split; auto.
    intros ε H11. assert (H12 : A + ε > A). lra.
    apply H10 in H12 as H13.
    destruct H13 as [y' [H13 H14]].
    unfold Lower in H7. apply H7 in H13 as H15.
    rewrite H5 in H13. applyAxiomII H13.
    destruct H13 as [x' [H13 H16]].
    exists (x'-x0). applyAxiomII H13.
    split; try lra. intros x H17. apply Abs_R.
    unfold IntervalIncreaseFun in H1.
    destruct H1 as [H1 [H18 H19]].
    assert (H20 : x ∈ rightNeighbor0 x0 δ').
    { apply AxiomII. lra. }
    assert (H21 : x' ∈ rightNeighbor0 x0 δ').
    { apply AxiomII. lra. }
    generalize (H19 x x' H20 H21). intro H22.
    assert (H23 : f[x] ∈ Range).
    { rewrite H5. apply AxiomII. exists x.
      split; auto. }
    apply H7 in H23. lra.
  - assert (H5 : ∃ Range, Range = \{ λ y,
        ∃ x, (x ∈ rightNeighbor0 x0 δ') /\ y = f[x] \}).
    { exists \{ λ y, ∃ x, (x ∈ rightNeighbor0 x0 δ')
        /\ y = f[x] \}; reflexivity. }
    destruct H5 as [Range H5].
    assert (H6 : NotEmpty Range).
    { exists (f[x0+δ'/2]). rewrite H5.
      apply AxiomII. exists (x0+δ'/2).
      split; auto. apply AxiomII. split; lra. }
    assert (H7 : (∃ M, Upper Range M)).
    { exists M. unfold Upper. intros y I1.
      rewrite H5 in I1. applyAxiomII I1.
      destruct I1 as [x [I1 I2]].
      rewrite I2. apply H4 in I1.
      apply Abs_le_R in I1. lra. }
    apply Sup_inf_principle in H6 as [H8 H9].
    apply H8 in H7. destruct H7 as [A [H7 H10]].
    exists A. unfold limit_pos. split; auto.
    exists δ'. repeat split; auto.
    intros ε H11. assert (H12 : A - ε < A). lra.
    apply H10 in H12 as H13.
    destruct H13 as [y' [H13 H14]].
    unfold Upper in H7. apply H7 in H13 as H15.
    rewrite H5 in H13. applyAxiomII H13.
    destruct H13 as [x' [H13 H16]].
    exists (x'-x0). applyAxiomII H13.
    split; try lra. intros x H17. apply Abs_R.
    unfold IntervalDecreaseFun in H1.
    destruct H1 as [H1 [H18 H19]].
    assert (H20 : x ∈ rightNeighbor0 x0 δ').
    { apply AxiomII. lra. }
    assert (H21 : x' ∈ rightNeighbor0 x0 δ').
    { apply AxiomII. lra. }
    generalize (H19 x x' H20 H21). intro H22.
    assert (H23 : f[x] ∈ Range).
    { rewrite H5. apply AxiomII. exists x.
      split; auto. }
    apply H7 in H23. lra.
Qed.

(* 定理3.11 柯西准则 *)
Theorem Theorem3_11 : ∀ (f : Fun) (x0 δ' : R), δ' > 0 -> Function f
  -> Neighbor0 x0 δ' ⊂ dom[f]
  ->
    (∃ A, limit f x0 A)
  <-> (∀ ε, ε > 0 -> (∃ δ, 0 < δ < δ' /\
        (∀ x' x'', x' ∈ Neighbor0 x0 δ -> x'' ∈ Neighbor0 x0 δ
          -> Abs[f[x'] - f[x'']] < ε))).
Proof.
  intros f x0 δ' H0 H1 H2. split; intro H3.
  - destruct H3 as [A H3].
    destruct H3 as [H3 [δ1' [H4 [H5 H6]]]].
    intros ε H7. assert (H8 : ε / 2 > 0). lra.
    apply H6 in H8 as H9.
    assert (H10 : ∃δ : R,0 < δ < δ' /\
      (∀x : R,0 < Abs [x - x0] < δ -> Abs [f [x] - A] < ε / 2)).
    { destruct H9 as [δ [I1 I2]].
      destruct (Rlt_or_le δ' δ1') as [I3 | I3].
      - destruct (Rlt_or_le δ δ') as [I4 | I4].
        + exists δ. split; auto; lra.
        + exists (δ' / 2). split; try lra.
          intros x I5. apply I2. lra.
      - exists δ. split; try lra. intros x I4.
        apply I2. apply I4. }
    destruct H10 as [δ [H10 H11]]. exists δ. split; auto.
    intros x' x'' H12 H13.
    applyAxiomII H12. applyAxiomII H13.
    apply H11 in H12. apply H11 in H13.
    assert (H14 : f[x'] - f[x''] = (f[x']-A)-(f[x'']-A)).
    field. rewrite H14.
    generalize (Abs_minus_le (f[x']-A) (f[x'']-A)).
    intro H15. lra.
  - assert (H4 : ∀ (x : Seq), IsSeq x -> ran[x] ⊂ Neighbor0 x0 δ'
      -> limit_seq x x0 -> Convergence \{\ λ n v, v = f[x[n]] \}\).
    { intros x I1 I2 I3.
      assert (I4 : IsSeq \{\ λ n v, v = f[x[n]] \}\).
      { split.
        - unfold Function. intros x1 y1 z1 J1 J2.
          applyAxiomII' J1; applyAxiomII' J2.
          rewrite J2. assumption.
        - apply AxiomI. intro z; split; intro J1.
          + apply AxiomII. reflexivity.
          + apply AxiomII. exists (f[x[z]]). apply AxiomII'.
            reflexivity. }
      apply Theorem2_11; auto.
      intros ε I5. apply H3 in I5 as I6.
      destruct I6 as [δ [I6 I7]]. unfold limit_seq in I3.
      destruct I3 as [I3 I8]. destruct I6 as [I6 I9].
      apply I8 in I6 as I10. destruct I10 as [N I10].
      exists N. intros n m I11 I12. apply I10 in I11 as I13.
      apply I10 in I12 as I14.
      assert (I15 : ∀ n,  \{\ λ n0 v, v = f [x [n0]] \}\ [n] = f[x[n]]).
      { intro n0. apply f_x; try apply I4. apply AxiomII'.
        reflexivity. }
      rewrite I15. rewrite I15.
      assert (I16 : ∀ n, Abs [x [n] - x0] > 0).
      { intro n0.
        assert (J1 : x[n0] ∈ ran[x]).
        { apply fx_ran; try apply I1. destruct I1 as [I1 J1].
          rewrite J1. apply AxiomII. reflexivity. }
        apply I2 in J1. applyAxiomII J1.
        apply J1. }
      apply I7; apply AxiomII; split; try lra; apply I16. }
    assert (H5 : ∃ x1, x1 = \{\ λ n v, v = x0 + δ' / (INR (S (S n))) \}\).
    { exists \{\ λ n v, v = x0 + δ' / (INR (S (S n))) \}\.
      reflexivity. }
    destruct H5 as [x1 H5].
    assert (H6 : IsSeq x1).
    { unfold IsSeq. split.
      - unfold Function. rewrite H5. intros x y z I1 I2.
        applyAxiomII' I1. applyAxiomII' I2.
        rewrite I2. apply I1.
      - apply AxiomI. intro n; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (x0 + δ' / (INR (S (S n)))).
          rewrite H5. apply AxiomII'.
          reflexivity. }
    assert (H7 : ran[x1] ⊂ Neighbor0 x0 δ').
    { intros y I1. applyAxiomII I1. destruct I1 as [n I1].
      rewrite H5 in I1. apply -> AxiomII' in I1.
      assert (I2 : y = x0 + δ' / (INR (S (S n)))).
      { apply I1. }
      rewrite I2. apply AxiomII.
      assert (I4 : δ' / INR (S (S n)) > 0).
      { rewrite S_INR. apply Rdiv_lt_0_compat; auto.
        generalize (pos_INR (S n)). intro I4. lra. }
      assert (I3 : x0 + δ' / INR (S (S n)) - x0 = δ' / INR (S (S n))).
      lra. rewrite I3.
      split.
      - apply Abs_not_eq_0. apply Rgt_not_eq.
        auto.
      - apply Abs_gt in I4 as I5. rewrite I5. rewrite S_INR.
        rewrite S_INR. generalize (pos_INR n). intro I6.
        assert (I7 : INR n + 1 + 1 > 1). lra.
        unfold Rdiv. assert (I8 : 1 <= 1). right. reflexivity.
        apply Rinv_1_lt_contravar in I7 as I9; auto.
        rewrite Rinv_1 in I9.
        apply Rmult_lt_compat_l with (r := δ') in I9; auto.
        rewrite Rmult_1_r in I9. assumption. }
    assert (H8 : limit_seq x1 x0).
    { split; auto. intros ε I1.
      generalize (Archimedes ε δ' I1 H0).
      intro I2. destruct I2 as [N I2].
      exists N. intros n I3.
      assert (I4 : x1[n] = x0 + δ' / INR (S (S n))).
      { apply f_x; try apply H6. rewrite H5.
        apply AxiomII'. reflexivity. }
      rewrite I4.
      assert (I5 : x0 + δ' / INR (S (S n)) - x0 = δ' / INR (S (S n))).
      lra. rewrite I5.
      assert (I6 : δ' / INR (S (S n)) > 0).
      { rewrite S_INR. apply Rdiv_lt_0_compat; auto.
        generalize (pos_INR (S n)). intro I7. lra. }
      apply Abs_gt in I6. rewrite I6.
      rewrite S_INR. rewrite S_INR.
      assert (I7 : (INR n + 1 + 1) * ε > INR N * ε).
      { apply Rmult_gt_compat_r; auto.
        assert (I8 : INR n > INR N).
        { apply lt_INR. apply I3. }
        lra. }
      generalize (Rgt_trans ((INR n + 1 + 1) * ε) (INR N * ε) δ' I7 I2).
      intro I8. assert (I9 : (INR n + 1 + 1) > 0).
      { generalize (pos_INR n). intro I9. lra. }
      unfold Rdiv. apply Rinv_0_lt_compat in I9 as I10.
      apply Rmult_gt_compat_r with (r := / (INR n + 1 + 1)) in I8; auto.
      assert (I11 : (INR n + 1 + 1) * ε * / (INR n + 1 + 1)
        = ε).
      field. lra. rewrite I11 in I8. apply I8. }
    generalize (H4 x1 H6 H7 H8). intro H9.
    destruct H9 as [A H9]. exists A.
    apply (Theorem3_8 f x0 δ' A H1 H0 H2).
    intros x H10 H11 H12.
    assert (H13 : ∃ z, z = \{\ λ n v, ∃ m,
      ((n = m + m)%nat /\ v = x1[m]) \/
        ((n = m + m + 1)%nat /\ v = x[m]) \}\).
    { exists \{\ λ n v, ∃ m, ((n = m + m)%nat /\ v = x1[m]) \/
        ((n = m + m + 1)%nat /\ v = x[m]) \}\. reflexivity. }
    destruct H13 as [z H13].
    assert (H14 : ∀ n : nat, ∃ m, (n = m + m \/ n = m + m + 1)%nat).
    { intro n. induction n as [|n IHn].
      - exists 0%nat. left. simpl. reflexivity.
      - destruct IHn as [m [IHn | IHn]].
        + exists m. right. rewrite IHn. rewrite Nat.add_1_r.
          reflexivity.
        + exists (S m). left. rewrite IHn. rewrite Nat.add_1_r.
          simpl. rewrite (Nat.add_comm m (S m)).
          simpl. reflexivity. }
    assert (H15 : ∀ n m1 m2, (n = m1 + m1)%nat ->
      (n = m2 + m2 + 1)%nat -> False).
    { intros n m1 m2 I1 I2. rewrite I1 in I2.
      assert (I3 : (m1 + m1 - (m2 + m2))%nat = 1%nat).
      { rewrite I2. rewrite minus_plus. reflexivity. }
      assert (I4 : ∀ k, (2 * k = k + k)%nat).
      { intro k. induction k as [|k IHk].
        - simpl. reflexivity.
        - simpl. rewrite <- plus_n_O. reflexivity. }
      rewrite <- I4 in I3. rewrite <- I4 in I3.
      rewrite <- Nat.mul_sub_distr_l in I3.
      assert (I5 : ∀ k, (2 * k = 1)%nat -> False).
      { intros k J1. destruct k as [|k].
        - simpl in J1. discriminate.
        - generalize (gt_Sn_O k). intro J2.
          apply lt_le_S in J2 as J3.
          assert (J4 : (2 * S k > S k)%nat).
          { rewrite I4.
            apply plus_gt_compat_l with (p := S k) in J2.
            rewrite <- plus_n_O in J2. apply J2. }
          generalize (Nat.le_lt_trans 1%nat (S k) (2 * S k)%nat J3 J4).
          intro J5. apply Nat.lt_neq in J5. apply J5.
          rewrite J1. reflexivity. }
      apply (I5 (m1 - m2)%nat). assumption. }
    assert (H16 : ∀ k, (2 * k = k + k)%nat).
    { intro k. induction k as [|k IHk].
      - simpl. reflexivity.
      - simpl. rewrite <- plus_n_O. reflexivity. }
    assert (H17 : IsSeq z).
    { rewrite H13. split.
      - intros n v1 v2 I1 I2. applyAxiomII' I1. applyAxiomII' I2.
        destruct I1 as [m1 I1]. destruct I2 as [m2 I2].
        destruct I1 as [I1 | I1].
        + destruct I2 as [I2 | I2].
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            assert (I5 : m1 = m2).
            { rewrite I1 in I2. apply NNPP. intro I5.
              apply not_eq in I5. destruct I5 as [I5 | I5].
              - generalize (plus_lt_compat m1 m2 m1 m2 I5 I5).
                intro I6. apply Nat.lt_neq in I6. auto.
              - generalize (plus_lt_compat m2 m1 m2 m1 I5 I5).
                intro I6. apply Nat.lt_neq in I6. apply I6.
                rewrite I2. reflexivity. }
            rewrite I4. rewrite <- I5. assumption.
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            exfalso. apply (H15 n m1 m2); auto.
        + destruct I2 as [I2 | I2].
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            exfalso. apply (H15 n m2 m1); auto.
          * destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
            assert (I5 : m1 = m2).
            { rewrite I1 in I2. apply NNPP. intro I5.
              apply not_eq in I5. destruct I5 as [I5 | I5].
              - apply plus_lt_compat_r with (p := 1%nat) in I5 as I6.
                generalize (plus_lt_compat
                  m1 m2 (m1 + 1)%nat (m2 + 1)%nat I5 I6).
                intro I7. rewrite <- plus_assoc_reverse in I7.
                rewrite <- plus_assoc_reverse in I7.
                apply Nat.lt_neq in I7. auto.
              - apply plus_lt_compat_r with (p := 1%nat) in I5 as I6.
                generalize (plus_lt_compat
                  m2 m1 (m2 + 1)%nat (m1 + 1)%nat I5 I6).
                intro I7. rewrite <- plus_assoc_reverse in I7.
                rewrite <- plus_assoc_reverse in I7.
                apply Nat.lt_neq in I7. auto. }
            rewrite I4. rewrite <- I5. assumption.
      - apply AxiomI. intro k; split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. generalize (H14 k). intro I2.
          destruct I2 as [m [I2 | I2]].
          * exists (x1[m]). apply AxiomII'. exists m.
            left. split; auto.
          * exists (x[m]). apply AxiomII'. exists m.
            right. split; auto. }
    assert (H18 : ran[z] ⊂ Neighbor0 x0 δ').
    { intros v I1. applyAxiomII I1. destruct I1 as [k I1].
      rewrite H13 in I1. applyAxiomII' I1.
      destruct I1 as [m [[I1 I2] | [I1 I2]]].
      - apply H7. rewrite I2. destruct H6 as [H6 I3].
        apply fx_ran; auto. rewrite I3. apply AxiomII.
        reflexivity.
      - apply H11. rewrite I2. destruct H10 as [H10 I3].
        apply fx_ran; auto. rewrite I3. apply AxiomII.
        reflexivity. }
    assert (H19 : limit_seq z x0).
    { split; auto. intros ε I1. apply H8 in I1 as I2.
      apply H12 in I1 as I3. destruct I3 as [N2 I3].
      destruct I2 as [N1 I2].
      generalize (Max_nat_2 (N1 + N1)%nat (N2 + N2 + 1)%nat).
      intro I4. destruct I4 as [N [I4 I5]].
      exists N. intros n I6. generalize (H14 n).
      destruct H17 as [H17 I7].
      intros [m [I8 | I8]].
      - assert (I9 : z[n] = x1[m]).
        { apply f_x; auto. rewrite H13.
          apply AxiomII'. exists m. left. split; auto. }
        rewrite I9. generalize (Nat.lt_trans (N1 + N1)%nat N n I4 I6).
        intro I10. rewrite I8 in I10.
        assert (I11 : (N1 < m)%nat).
        { apply NNPP. intro J1. apply not_lt in J1.
          generalize (plus_le_compat m N1 m N1 J1 J1).
          intro J2. apply lt_not_le in I10. auto. }
        apply I2. assumption.
      - assert (I9 : z[n] = x[m]).
        { apply f_x; auto. rewrite H13.
          apply AxiomII'. exists m. right. split; auto. }
        rewrite I9. generalize (Nat.lt_trans
          (N2 + N2 + 1)%nat N n I5 I6).
        intro I10. rewrite I8 in I10.
        assert (I11 : (N2 < m)%nat).
        { apply NNPP. intro J1. apply not_lt in J1.
          apply plus_le_compat_r with (p := 1%nat) in J1 as J2.
          generalize (plus_le_compat m N2 (m + 1)%nat
            (N2 + 1)%nat J1 J2).
          rewrite <- plus_assoc_reverse.
          rewrite <- plus_assoc_reverse.
          intro J3.  apply lt_not_le in I10. auto. }
        apply I3. assumption. }
    generalize (H4 x H10 H11 H12). intro H20.
    generalize (H4 z H17 H18 H19). intros [B H21].
    assert (H22 : SubSeq \{\ λ (n : nat)(v : R), v = f [z [n]] \}\
      \{\ λ(n : nat)(v : R), v = f [x1 [n]] \}\).
    { unfold SubSeq. destruct H20 as [C [H20 H22]].
      destruct H21 as [H21 H23]. destruct H9 as [H9 H24].
      split; [idtac | split]; auto.
      exists \{\ λ m n, n = (m + m)%nat \}\.
      assert (I1 : StrictlyIncreaseFun_nat
        \{\ λ m n, n = (m + m)%nat \}\).
      { unfold StrictlyIncreaseFun_nat. split.
        - unfold Function. intros m n1 n2 I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        - intros m1 m2 n1 n2 I1 I2 I3.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I1. rewrite I2.
          apply plus_lt_compat; auto. }
      split; auto. split.
      - apply AxiomI. intro n; split; intro I2.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (n + n)%nat.
          apply AxiomII'. reflexivity.
      - intro n. assert (I2 : \{\ λ n0 v, v = f [x1 [n0]] \}\ [n]
          = f[x1[n]]).
        { apply f_x; try apply H9. apply AxiomII'.
          reflexivity. }
        rewrite I2. assert (I3 : \{\ λ m n0, n0 = (m + m)%nat \}\
          \[ n \] = (n + n)%nat).
        { apply f_x_N; try apply I1. apply AxiomII'.
          reflexivity. }
        rewrite I3. assert (I4 : \{\ λ n0 v, v = f [z [n0]] \}\
          [(n + n)%nat] = f[z[(n + n)%nat]]).
        { apply f_x; try apply H21. apply AxiomII'.
          reflexivity. }
        rewrite I4. assert (I5 : z[(n + n)%nat] = x1[n]).
        { apply f_x; try apply H17. rewrite H13.
          apply AxiomII'. exists n. left. split; reflexivity. }
        rewrite I5. reflexivity. }
    assert (H23 : SubSeq \{\ λ (n : nat)(v : R), v = f [z [n]] \}\
      \{\ λ(n : nat)(v : R), v = f [x [n]] \}\).
    { unfold SubSeq. destruct H20 as [C [H20 H23]].
      destruct H21 as [H21 H24].
      split; [idtac | split]; auto.
      exists \{\ λ m n, n = (m + m + 1)%nat \}\.
      assert (I1 : StrictlyIncreaseFun_nat
        \{\ λ m n, n = (m + m + 1)%nat \}\).
      { unfold StrictlyIncreaseFun_nat. split.
        - unfold Function. intros m n1 n2 I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        - intros m1 m2 n1 n2 I1 I2 I3.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I1. rewrite I2.
          generalize (plus_lt_compat_r m1 n1 1%nat I3).
          intro I4. rewrite plus_assoc_reverse.
          rewrite plus_assoc_reverse.
          apply plus_lt_compat; auto. }
      split; auto. split.
      - apply AxiomI. intro n; split; intro I2.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (n + n + 1)%nat.
          apply AxiomII'. reflexivity.
      - intro n. assert (I2 : \{\ λ n0 v, v = f [x [n0]] \}\ [n]
          = f[x[n]]).
        { apply f_x; try apply H20. apply AxiomII'.
          reflexivity. }
        rewrite I2. assert (I3 : \{\ λ m n0, n0 = (m + m + 1)%nat \}\
          \[ n \] = (n + n + 1)%nat).
        { apply f_x_N; try apply I1. apply AxiomII'.
          reflexivity. }
        rewrite I3. assert (I4 : \{\ λ n0 v, v = f [z [n0]] \}\
          [(n + n + 1)%nat] = f[z[(n + n + 1)%nat]]).
        { apply f_x; try apply H21. apply AxiomII'.
          reflexivity. }
        rewrite I4. assert (I5 : z[(n + n + 1)%nat] = x[n]).
        { apply f_x; try apply H17. rewrite H13.
          apply AxiomII'. exists n. right. split; reflexivity. }
        rewrite I5. reflexivity. }
    generalize (SubSeqEqual \{\ λ n v, v = f [z [n]] \}\ B H21).
    intro H24. apply H24 in H22. apply H24 in H23.
    generalize (Theorem2_2 \{\ λ n v, v = f [x1 [n]] \}\ A B H9 H22).
    intro H25. rewrite H25. assumption.
Qed.

End A3_3.

Export A3_3.