Require Export A_3_3.

Module A3_5.

(* 3.5 无穷小量与无穷大量 *)

(* 定义1: 无穷小量 *)
Definition Infinitesimal (f : Fun) (x0 : R) := limit f x0 0.


 (* 高阶无穷小量 *)
Definition InfinitesimalHigherOrder (f g : Fun) (x0 : R) :=
  Function f /\ Function g /\ (∃ δ, 0 < δ /\ Neighbor0 x0 δ ⊂ dom[f]
  /\ Neighbor0 x0 δ ⊂ dom[g] /\ (∀ x, x ∈ Neighbor0 x0 δ -> g[x] <> 0)) /\
  limit \{\ λ x y, y = f[x] / g[x] \}\ x0 0. 
  

(* 等价无穷小 *)
Definition InfinitesimalEquivalent (f g : Fun) (x0 : R) :=
  Function f /\ Function g /\ (∃ δ, 0 < δ /\ Neighbor0 x0 δ ⊂ dom[f]
  /\ Neighbor0 x0 δ ⊂ dom[g] /\ (∀ x, x ∈ Neighbor0 x0 δ -> g[x] <> 0)) /\
  limit \{\ λ x y, y = f[x] / g[x] \}\ x0 1.
  
(* 定理3.12 *)
Theorem Theorem3_12 : ∀ (f g h : Fun) (x0 A : R),
  InfinitesimalEquivalent f g x0
  -> limit \{\ λ x y, y = f[x] * h[x] \}\ x0 A
  -> limit \{\ λ x y, y = g[x] * h[x] \}\ x0 A.
Proof.
  intros f g h x0 A H7 H8.
  destruct H7 as [H7 [H9 [[δ1 [H10 [H11 [H12 H13]]]] H14]]].
  clear H7. clear H9.
  assert (H15 : Function \{\ λ x y, y = g [x] / f [x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2. assumption. }
  assert (H16 : ∃ δ2, δ2 > 0 /\ (∀ x, x ∈ (Neighbor0 x0 δ2)
    -> \{\ λ x y, y = f[x] / g[x] \}\[x] <> 0)).
  { assert (I1 : 1 > 0). lra.
    generalize (Theorem3_4_1 \{\ λ x y, y = f[x] / g[x] \}\ x0 1 H14 I1).
    intro I2. assert (I3 : 0 < 1/2 < 1). lra.
    apply I2 in I3 as I4.
    destruct I4 as [δ3 [I4 I5]].
    exists δ3. split; auto. intros x I6.
    apply I5 in I6. lra. }
  destruct H16 as [δ2 [H16 H17]].
  assert (H18 : ∃ δ3, δ3 > 0 /\ (∀ x, x ∈ (Neighbor0 x0 δ3)
    -> f[x] <> 0)).
  { assert (I2 : ∃ δ4, δ4 > 0 /\ δ4 <= δ1 /\ δ4 <= δ2).
    { destruct (Rlt_or_le δ1 δ2) as [I1 | I1].
      - exists δ1. split; lra.
      - exists δ2. split; lra. }
    destruct I2 as [δ4 [I2 [I3 I4]]]. exists δ4. split; auto.
    intros x I5.
    applyAxiomII I5.
    assert (I6 : x ∈ Neighbor0 x0 δ1).
    { apply AxiomII. lra. }
    assert (I7 : x ∈ Neighbor0 x0 δ2).
    { apply AxiomII. lra. }
    apply H13 in I6 as I8. apply H17 in I7 as I9.
    assert (I10 : \{\ λ x y, y = f [x] / g [x] \}\ [x] = f[x] / g[x]).
    { apply f_x; try apply H14. apply AxiomII'. reflexivity. }
    rewrite I10 in I9. clear I10. intro I10.
    apply I9. rewrite I10. apply Rmult_0_l. }
  destruct H18 as [δ3 [H18 H19]].
  assert (H20 : limit (\{\ λ x y, y = g [x] / f [x] \}\
    ** \{\ λ x y, y = f[x] * h[x] \}\) x0 A).
  { rewrite <- (Rmult_1_l A). apply Theorem3_7_3; auto.
    assert (I1 : 1 <> 0). lra.
    generalize (Theorem3_7_4' \{\ λ x y, y = f [x] / g [x] \}\
      x0 1 H14 I1). intro I2. rewrite Rinv_1 in I2. unfold limit.
    split; auto. destruct I2 as [I3 [δ4 [I4 [I5 I6]]]].
    assert (I2 : ∃ δ5, δ5 > 0 /\ δ5 <= δ4 /\ δ5 <= δ1 /\ δ5 <= δ3).
    { destruct (Rlt_or_le δ1 δ4) as [J1 | J1].
      - destruct (Rlt_or_le δ1 δ3) as [J2 | J2].
        + exists δ1. lra.
        + exists δ3. lra.
      - destruct (Rlt_or_le δ4 δ3) as [J2 | J2].
        + exists δ4. lra.
        + exists δ3. lra. }
    destruct I2 as [δ5 [I7 [I8 [I9 I10]]]].
    exists δ5. repeat split; auto.
    - intros x J1. apply AxiomII. exists (g[x] / f[x]).
      apply AxiomII'. reflexivity.
    - intros ε J1. apply I6 in J1 as J2.
      destruct J2 as [δ6 [J2 J3]].
      assert (I2 : ∃ δ7, δ7 > 0 /\ δ7 < δ5 /\ δ7 < δ6).
      { destruct (Rlt_or_le δ5 δ6) as [K1 | K1].
        - exists (δ5 / 2). split; lra.
        - exists (δ6 / 2). split; lra. }
      destruct I2 as [δ7 [I2 [I11 I12]]].
      exists δ7. split; try lra.
      intros x J4.
      assert (J5 : 0 < Abs [x - x0] < δ6). lra.
      apply J3 in J5 as J6.
      assert (J7 : (1 /// \{\ λ x0 y0,
        y0 = f [x0] / g [x0] \}\) [x] = g[x] / f[x]).
      { assert (J7 : \{\ λ x1 y0, y0 = f [x1] / g [x1] \}\ [x]
          = f[x] / g[x]).
        { apply f_x; try apply H14. apply AxiomII'.
          reflexivity. }
        apply f_x; auto. apply AxiomII'. repeat split.
        - apply AxiomII. exists (f[x] / g[x]).
          apply AxiomII'. reflexivity.
        - rewrite J7. apply Rmult_integral_contrapositive. split.
          + apply H19. apply AxiomII. lra.
          + apply Rinv_neq_0_compat. apply H13.
            apply AxiomII. lra.
        - rewrite J7. field. split.
          + apply H13. apply AxiomII. lra.
          + apply H19. apply AxiomII. lra. }
      rewrite J7 in J6.
      assert (J8 : \{\ λ x1 y, y = g [x1] / f [x1] \}\ [x] = g[x] / f[x]).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite J8. assumption. }
  unfold limit in H20. destruct H20 as [H20 [δ4 [H21 [H22 H23]]]].
  assert (H24 : Function \{\ λ x y, y = g [x] * h [x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2. assumption. }
  split; auto.
  assert (H25 : ∃ δ5, δ5 > 0 /\ δ5 < δ3 /\ δ5 < δ4).
  { destruct (Rlt_or_le δ3 δ4) as [K1 | K1].
    - exists (δ3 / 2). split; lra.
    - exists (δ4 / 2). split; lra. }
  destruct H25 as [δ5 [H25 [H26 H27]]].
  exists δ5. split; auto. split.
  - intros x H28. apply AxiomII. exists (g[x] * h[x]).
    apply AxiomII'. reflexivity.
  - intros ε H28. apply H23 in H28 as H29.
    destruct H29 as [δ6 [H29 H30]].
    assert (H31 : ∃ δ7, δ7 > 0 /\ δ7 < δ5 /\ δ7 < δ6).
    { destruct (Rlt_or_le δ5 δ6) as [K1 | K1].
      - exists (δ5 / 2). split; lra.
      - exists (δ6 / 2). split; lra. }
    destruct H31 as [δ7 [H31 [H32 H33]]].
    exists δ7. split; try lra.
    intros x H34.
    assert (H35 : 0 < Abs [x - x0] < δ6). lra.
    apply H30 in H35 as H36.
    assert (H37 : \{\ λ x1 y, y = g [x1] * h [x1] \}\ [x]
      = g[x] * h[x]).
    { apply f_x; auto. apply AxiomII'. reflexivity. }
    rewrite H37.
    assert (H38 : (\{\ λ x y, y = g [x] / f [x] \}\ **
      \{\ λ x y, y = f [x] * h [x] \}\) [x] = g[x] * h[x]).
    { apply f_x; auto. apply AxiomII'. repeat split.
      - apply AxiomII. exists (g[x] / f[x]).
        apply AxiomII'. reflexivity.
      - apply AxiomII. exists (f[x] * h[x]).
        apply AxiomII'. reflexivity.
      - assert (I1 : g[x] * h[x] = (g[x] / f[x]) * (f[x] * h[x])).
        { field. apply H19. apply AxiomII. lra. }
        rewrite I1.
        assert (I2 : \{\ λ x1 y, y = g [x1] / f [x1] \}\ [x]
          = g[x] / f[x]).
        { apply f_x; auto. apply AxiomII'. reflexivity. }
        assert (I3 : \{\ λ x1 y, y = f [x1] * h [x1] \}\ [x]
          = f[x] * h[x]).
        { apply f_x; try apply H8. apply AxiomII'.
          reflexivity. }
        rewrite I2; rewrite I3. reflexivity. }
    rewrite H38 in H36. assumption.
Qed.

(* 定义2：无穷大量 *)
Definition limit_infinite (f : Fun) (x0 : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂ dom[f] /\
     (∀ G : R, G > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, 0 < Abs[x-x0] < δ -> G < Abs[f[x]]))).

Definition limit_infinite_pos (f : Fun) (x0 : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ rightNeighbor0 x0 δ' ⊂ dom[f] /\
     (∀ G : R, G > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, x0 < x < x0+δ -> G < Abs[f[x]]))).

Definition limit_infinite_neg (f : Fun) (x0 : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ leftNeighbor0 x0 δ' ⊂ dom[f] /\
     (∀ G : R, G > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, x0-δ < x < x0 -> G < Abs[f[x]]))).


(* 定理3.13 *)
Theorem Theorem13 : ∀ (f : Fun) (x0 : R),
  (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂ dom[f] /\
    (∀ x, x ∈ Neighbor0 x0 δ' -> f[x] <> 0))
  -> Infinitesimal f x0 -> limit_infinite (1 /// f) x0.
Proof.
  intros f x0 [δ' [H0 [H1 H2]]] H3. unfold Infinitesimal in H3.
  unfold limit in H3. destruct H3 as [H3 [δ0' [H4 [H5 H6]]]].
  assert (H7 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]]. rewrite I4. apply I1. }
  split; auto.
  assert (H8 : ∃ δ1', δ1' > 0 /\ δ1' < δ' /\ δ1' < δ0').
  { destruct (Rlt_or_le δ' δ0') as [K1 | K1].
    - exists (δ' / 2). split; lra.
    - exists (δ0' / 2). split; lra. }
  destruct H8 as [δ1' [H8 [H9 H10]]].
  exists δ1'. assert (H11 : Neighbor0 x0 δ1' ⊂ dom[ 1 /// f]).
  { intros x I1. assert (I2 : x ∈ Neighbor0 x0 δ').
    { apply AxiomII. applyAxiomII I1. lra. }
    apply AxiomII. exists (1 / f[x]). apply AxiomII'.
    repeat split; auto. }
  repeat split; auto.
  intros G H12. apply Rinv_0_lt_compat in H12 as H13.
  apply H6 in H13 as H14. destruct H14 as [δ0 [H14 H15]].
  assert (H16 : ∃ δ, δ > 0 /\ δ < δ0 /\ δ < δ1').
  { destruct (Rlt_or_le δ0 δ1') as [K1 | K1].
    - exists (δ0 / 2). split; lra.
    - exists (δ1' / 2). split; lra. }
  destruct H16 as [δ [H16 [H17 H18]]].
  exists δ. split; try lra. intros x H19.
  assert (H20 : 0 < Abs [x - x0] < δ0). lra.
  apply H15 in H20 as H21.
  assert (H22 : x ∈ Neighbor0 x0 δ').
  { apply AxiomII. lra. }
  assert (H23 : (1 /// f) [x] = 1 / f[x]).
  { apply f_x; auto. apply AxiomII'.
    split; auto. }
  rewrite H23. apply H2 in H22 as H24. rewrite Abs_div; auto.
  assert (H25 : Abs [1] / Abs [f [x]] = / Abs [f [x]]).
  { rewrite Abs_gt; lra. }
  rewrite H25. rewrite Rminus_0_r in H21.
  assert (H26 : 0 < Abs[f[x]] * (/G)).
  { apply Rmult_lt_0_compat; auto.
    apply Abs_not_eq_0; assumption. }
  apply Rinv_lt_contravar in H21; auto.
  rewrite Rinv_involutive in H21;
    [assumption | apply Rgt_not_eq]; assumption.
Qed.


End A3_5.

Export A3_5.