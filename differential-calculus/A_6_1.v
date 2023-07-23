Require Export A_5_5.

Module A6_1.

(* 罗尔定理 *)
Theorem Theorem6_1 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∀ x, a < x < b -> derivable f x)
  -> f[a] = f[b]
  -> ∃ ξ, a < ξ < b /\ derivative f ξ 0.
Proof.
  intros f a b H0 H1 H2 H3.
  generalize (Theorem4_6 f a b H0 H1).
  intros [[M [H4 [H5 [ξ1 [H6 H10]]]]] [m [H7 [H8 [ξ2 [H9 H11]]]]]].
  assert (H12 : m <= M).
  { assert (I1 : a ∈ \[ a, b \]).
    { apply AxiomII. lra. }
    apply H5 in I1 as I2. apply H8 in I1 as I3. lra. }
  destruct H12 as [H12 | H12].
  - assert (I1 : a < ξ1 < b \/ a < ξ2 < b).
    { apply NNPP. intro J1. apply not_or_and in J1 as [J1 J2].
      applyAxiomII H6. applyAxiomII H9.
      assert (J3 : ξ1 = a \/ ξ1 = b). lra.
      assert (J4 : ξ2 = a \/ ξ2 = b). lra.
      destruct J3 as [J3 | J3]; rewrite J3 in *;
      destruct J4 as [J4 | J4]; rewrite J4 in *; lra. }
    destruct I1 as [I1 | I1].
    + exists ξ1. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * left. unfold localMax. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ1 - a /\ δ < b - ξ1).
        { destruct (Rlt_or_le (ξ1 - a) (b - ξ1)) as [J1 | J1].
          - exists ((ξ1 - a) / 2). repeat split; lra.
          - exists ((b - ξ1) / 2). repeat split; lra. }
        destruct J1 as [δ [J1 [J2 J3]]].
        exists δ. repeat split; auto.
        -- intros x K1. applyAxiomII K1.
          apply H4. apply AxiomII. apply Abs_R in K1. lra.
        -- intros x K1. applyAxiomII K1. apply Abs_R in K1.
          rewrite H10. apply H5. apply AxiomII. lra.
    + exists ξ2. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * right. unfold localMin. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ2 - a /\ δ < b - ξ2).
        { destruct (Rlt_or_le (ξ2 - a) (b - ξ2)) as [J1 | J1].
          - exists ((ξ2 - a) / 2). repeat split; lra.
          - exists ((b - ξ2) / 2). repeat split; lra. }
        destruct J1 as [δ [J1 [J2 J3]]].
        exists δ. repeat split; auto.
        -- intros x K1. applyAxiomII K1.
          apply H4. apply AxiomII. apply Abs_R in K1. lra.
        -- intros x K1. applyAxiomII K1. apply Abs_R in K1.
          rewrite H11. apply H8. apply AxiomII. lra.
  - assert (I1 : ∀ x, x ∈ \[ a, b \] -> f[x] = m).
    { intros x J1. apply H5 in J1 as J2.
      apply H8 in J1 as J3. lra. }
    exists ((a + b) / 2). split; try lra.
    apply Theorem5_3.
    + apply H2; lra.
    + left. unfold localMax. split; try apply H1.
      exists ((b - a) / 2). repeat split; try lra.
      * intros x J1. applyAxiomII J1. apply H4.
        apply Abs_R in J1. apply AxiomII. lra.
      * intros x J1. applyAxiomII J1. apply Abs_R in J1.
        rewrite I1. rewrite I1. lra.
        -- apply AxiomII. lra.
        -- apply AxiomII. lra.
Qed.

(* 拉格朗日中值定理 *)
Theorem Theorem6_2 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∀ x, a < x < b -> derivable f x)
  -> ∃ ξ, a < ξ < b /\ derivative f ξ ((f[b] - f[a]) / (b - a)).
Proof.
  intros f a b H0 H1 H2.
  assert (H3 : ∃ F, F = \{\ λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a) \}\).
  { exists \{\ λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a) \}\; reflexivity. }
  destruct H3 as [F H3].
  assert (H4 : Function F).
  { rewrite H3. unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    rewrite I2. assumption. }
  assert (H5 : ∀ x, F[x] = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a)).
  { intro x. apply f_x; auto. rewrite H3. apply AxiomII'.
    reflexivity. }
  destruct H1 as [H1 [H6 H7]].
  unfold ContinuousOpen in H1.
  assert (H8 : ContinuousClose F a b).
  { unfold ContinuousClose. split; [idtac | split].
    - unfold ContinuousOpen. intros x I1.
      unfold Continuous. split.
      + apply AxiomII. exists (f[x] - f[a]
          - (f[b] - f[a])/(b - a)*(x - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit. split; auto. apply H1 in I1 as I2.
        unfold Continuous in I2. destruct I2 as [I2 I3].
        unfold limit in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,0 < Abs [x0 - x] < δ2 ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - x)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K3; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K3. clear K5.
                assert (K5 : Abs [x0 - x] * (Abs [f [b] - f [a]] / (b - a))
                  = Abs [f [b] - f [a]] / (b - a) * Abs [x0 - x]).
                { field. lra. }
                rewrite K5 in K3. assumption. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [x] - f [a]
            - (f [b] - f [a]) / (b - a) * (x - a))
            = f[x0] - f[x] - (f [b] - f [a]) / (b - a) * (x0 - x)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[x])
            ((f [b] - f [a]) / (b - a) * (x0 - x))).
          intros J11. assert (J12 : 0 < Abs [x0 - x] < δ1). lra.
          apply J4 in J12. assert (J13 : 0 < Abs [x0 - x] < δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousRight. split.
      + apply AxiomII. exists (f[a] - f[a]
          - (f[b] - f[a])/(b - a)*(a - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit_pos. split; auto.
        unfold ContinuousRight in H6. destruct H6 as [I2 I3].
        unfold limit_pos in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,a < x0 < a + δ2 ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - a)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                assert (K6 : x0 - a < ε / 2 * ((b - a)
                  / Abs [f [b] - f [a]])). lra.
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K6; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K6. clear K5.
                rewrite (Abs_gt (x0 - a)); lra. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [a] - f [a]
            - (f [b] - f [a]) / (b - a) * (a - a))
            = f[x0] - f[a] - (f [b] - f [a]) / (b - a) * (x0 - a)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[a])
            ((f [b] - f [a]) / (b - a) * (x0 - a))).
          intros J11. assert (J12 : a < x0 < a + δ1). lra.
          apply J4 in J12. assert (J13 : a < x0 < a + δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousLeft. split.
      + apply AxiomII. exists (f[b] - f[a]
          - (f[b] - f[a])/(b - a)*(b - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit_neg. split; auto.
        unfold ContinuousLeft in H7. destruct H7 as [I2 I3].
        unfold limit_neg in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0, b - δ2 < x0 < b ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - b)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                assert (K6 : b - x0 < ε / 2 * ((b - a)
                  / Abs [f [b] - f [a]])). lra.
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K6; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K6. clear K5.
                rewrite (Abs_lt (x0 - b)); lra. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [b] - f [a]
            - (f [b] - f [a]) / (b - a) * (b - a))
            = f[x0] - f[b] - (f [b] - f [a]) / (b - a) * (x0 - b)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[b])
            ((f [b] - f [a]) / (b - a) * (x0 - b))).
          intros J11. assert (J12 : b - δ1 < x0 < b). lra.
          apply J4 in J12. assert (J13 : b - δ2 < x0 < b).
          lra. apply J6 in J13. lra. }
  assert (H9 : ∀ x, a < x < b -> derivable F x).
  { intros x I1. apply H2 in I1 as I2.
    destruct I2 as [y' [I2 [[δ' [I3 I4]] I5]]].
    exists (y' - (f [b] - f [a]) / (b - a)).
    split; auto. split.
    - exists δ'. split; auto. intros x0 J1.
      apply AxiomII. rewrite H3.
      exists (f [x0] - f [a] - (f [b] - f [a]) / (b - a) * (x0 - a)).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct I5 as [I5 [δ0' [I6 [I7 I8]]]].
      split.
      + unfold Function. intros x0 y0 z0 J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + exists δ0'. split; auto. split.
        * intros x0 J1. apply AxiomII.
          exists ((F [x0] - F [x]) / (x0 - x)).
          apply AxiomII'. reflexivity.
        * intros ε J1. apply I8 in J1 as J2.
          destruct J2 as [δ [J2 J3]]. exists δ. split; auto.
          intros x0 J4. apply J3 in J4 as J5.
          assert (J6 : \{\ λ x0 y, y =
            (f [x0] - f [x]) / (x0 - x) \}\ [x0]
            = (f [x0] - f [x]) / (x0 - x)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : \{\ λ x1 y, y = (F [x1] - F [x])
            / (x1 - x) \}\ [x0] = (F [x0] - F [x]) / (x0 - x)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6. clear J6.
          rewrite H5. rewrite H5.
          assert (J6 : (f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [x] - f [a]
            - (f [b] - f [a]) / (b - a) * (x - a))) /
            (x0 - x) - (y' - (f [b] - f [a]) / (b - a))
            = (f [x0] - f [x]) / (x0 - x) - y').
          { field. destruct J4 as [J4 K1]. split; try lra.
            intro K2. rewrite K2 in J4.
            rewrite Abs_ge in J4; lra. }
          rewrite J6. clear J6. assumption. }
  assert (H10 : F[a] = F[b]).
  { rewrite H5; rewrite H5. field. lra. }
  generalize (Theorem6_1 F a b H0 H8 H9 H10).
  intros [ξ [H11 H12]]. exists ξ. split; auto.
  apply H2 in H11 as H13. destruct H13 as [f' H13].
  assert (H14 : derivative F ξ (f' - (f [b] - f [a]) / (b - a))).
  { split; auto. split.
    - exists 1. split; try lra. intros x0 I1.
      rewrite H3. apply AxiomII.
      exists (f[x0] - f[a] - (f[b] - f[a]) / (b - a) * (x0 - a)).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct H13 as [H13 [[δ' [I1 I2]] I3]].
      destruct I3 as [I3 [δ0' [I4 [I5 I6]]]]. split.
      + intros x1 y1 z1 J1 J2. applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + exists δ0'. repeat split; auto.
        * intros x0 J1. apply AxiomII.
          exists ((F[x0] - F[ξ]) / (x0 - ξ)).
          apply AxiomII'. reflexivity.
        * intros ε J1. apply I6 in J1 as J2.
          destruct J2 as [δ [J2 J3]].
          exists δ. split; auto.
          intros x J4. apply J3 in J4 as J5.
          assert (J6 : \{\ λ x y, y = (f[x] - f[ξ]) / (x - ξ) \}\ [x]
            = (f[x] - f[ξ]) / (x - ξ)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : \{\ λ x y, y = (F[x] - F[ξ]) / (x - ξ) \}\ [x]
            = (F[x] - F[ξ]) / (x - ξ)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6. clear J6.
          assert (J6 : (F [x] - F [ξ]) / (x - ξ) -
            (f' - (f [b] - f [a]) / (b - a))
            = (f [x] - f [ξ]) / (x - ξ) - f').
          { rewrite H5. rewrite H5. field.
            destruct J4 as [J4 K1]. apply Abs_not_eq_0 in J4.
            split; lra. }
          rewrite J6. assumption. }
  generalize (derivativeUnique F ξ 0 (f' - (f [b] - f [a]) / (b - a))
    H12 H14). intro H15.
  assert (H16 : f' = (f [b] - f [a]) / (b - a)). lra.
  rewrite <- H16. assumption.
Qed.

Lemma Rmult_le_le : ∀ a b, a < 0 /\ b < 0 -> a * b > 0.
Proof. 
  intros. destruct H. 
  rewrite <- Rmult_opp_opp. 
  apply Ropp_gt_lt_0_contravar in H.
  apply Ropp_gt_lt_0_contravar in H0.
  apply Rmult_gt_0_compat; auto.
Qed.

Lemma Rmult_leq_le : ∀ a b, a <= 0 /\ b < 0 -> a * b >= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_le_le; auto.
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Lemma Rmult_le_gr : ∀ a b, a < 0 /\ b > 0 -> a * b < 0.
Proof.  
intros. destruct H. 
apply (Rmult_lt_gt_compat_neg_l a 0 b) in H; auto. lra.
Qed.



Lemma Rmult_gre_gr : ∀ a b, a >= 0 /\ b > 0 -> a * b >= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_gt_0_compat; auto.
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Lemma Rmult_gre_le : ∀ a b, a >= 0 /\ b < 0 -> a * b <= 0.
Proof.
  intros. destruct H. destruct H.
  - left. rewrite Rmult_comm. apply Rmult_le_gr; auto. 
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.

Lemma Rmult_leq_gre : ∀ a b, a <= 0 /\ b > 0 -> a * b <= 0.
Proof.
  intros. destruct H. destruct H.
  - left. apply Rmult_le_gr; auto. 
  - right. apply Rmult_eq_0_compat_r; auto.
Qed.


(* 函数在区间单调递增的充要条件 *)
Theorem Theorem6_3 : ∀ (f : Fun) (a b : R), (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) -> derivable f x) -> (IntervalIncreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] >= 0)). 
Proof. 
  intros. destruct H as [H' [H H0]]. split; intros.
  - apply H0 in H2 as H2'. red in H2'.
    destruct H2' as [y']. apply derEqual in H3 as H3'.
    rewrite <- H3' in H3. red in H3. red in H1. 
    destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
    red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
    pose proof (Rbasic_fun.Rcase_abs (f '[x])). 
    destruct H3. 
    + assert (Abs[f '[x]] > 0). 
      { apply Abs_not_eq_0; lra.  }
      apply H10 in H3. destruct H3 as [δ0[H3 H11]].
      assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
      { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
        unfold Rbasic_fun.Rmin. applyAxiomII H2; destruct Rle_dec; 
        lra. }
      destruct H12 as [δ'[H12 H12']]. 
      assert(∃x1, 0 < Abs [x1 - x] < δ0 /\ x1 ∈ \( a, b \)).
      { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x).
        split. rewrite Abs_gt. replace (Rbasic_fun.Rmin δ' δ0 / 2 + x - x)
        with ((Rbasic_fun.Rmin δ' δ0) / 2); unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. applyAxiomII H2; destruct H2.
        unfold Rbasic_fun.Rmin; destruct Rle_dec. 
        rewrite H12. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; apply AxiomII; lra. 
        apply AxiomII. apply Rnot_le_gt in n. 
        split. lra. unfold Rbasic_fun.Rmin in H12;
        destruct Rle_dec; lra. }
        destruct H13 as [x1[H13 H13']]. 
        apply H11 in H13 as H13''. 
        assert(\{\ λ x0 y,y = (f [x0] - f [x]) / (x0 - x) \}\ [x1] =
              (f [x1] - f [x]) / (x1 - x)).
        { apply f_x; auto. apply AxiomII'; auto. }
      rewrite H14 in H13''. clear H14.
      assert ((f [x1] - f [x]) / (x1 - x) >= 0).
      { destruct H13. apply <- Abs_not_eq_0 in H13. 
        apply Rdichotomy in H13. destruct H13. apply Rminus_lt in H13.
        - apply (H5 x1 x) in H13'; auto. unfold Rdiv.
          apply Rmult_leq_le; auto. split. lra.
          apply Rinv_lt_0_compat; lra.
        - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto.
          unfold Rdiv. apply Rmult_gre_gr. split. lra. 
          apply Rinv_0_lt_compat; lra. } 
      assert(Abs [(f [x1] - f [x]) / (x1 - x) - f '[ x]] = 
             (f [x1] - f [x]) / (x1 - x) - f '[ x]). 
      { apply Abs_gt. lra. } 
      rewrite H15 in H13''. rewrite Abs_lt in H13''; auto. lra.
    + auto.
  - red. split.
    + assert (∃x1, x1 ∈ \( a, b \)). { exists ((b+a)/2). apply AxiomII.
      split; lra. }
      destruct H2 as [x1 H2].
      apply H0 in H2. red in H2.
      destruct H2 as [y1 H2]. red in H2. destruct H2 as [H2 [H3 H4]].
      auto.
    + split; auto. intros.
      assert (ContinuousClose f x1 x2).
      { red. split.
        - red. intros.
          assert (x ∈ \( a, b \)).
          { apply AxiomII. applyAxiomII H2. applyAxiomII H3.
            destruct H2. destruct H3. lra. }
          apply H0 in H6. apply Theorem5_1 in H6. auto.
        - split.
          + apply H0 in H2. apply Theorem5_1 in H2. apply Theorem4_1 in H2.
            destruct H2; auto.
          + apply H0 in H3. apply Theorem5_1 in H3. apply Theorem4_1 in H3.
            destruct H3; auto. }
       apply (Theorem6_2 f x1 x2) in H4; auto.
       destruct H4 as [ξ H4]. destruct H4. apply derEqual in H6.
       assert (ξ ∈ \( a, b \)). apply AxiomII. destruct H4.
       applyAxiomII H2. applyAxiomII H3. lra. apply H1 in H7.
       rewrite H6 in H7. unfold Rdiv in H7. 
       
       pose proof (Rle_or_lt f [x1] f [x2]).
       destruct H8. auto.
       assert (/ (x2 - x1) > 0).
       { assert ((x2-x1) > 0). lra.
         apply Rinv_0_lt_compat. auto. }
       assert ((f [x2] - f [x1]) < 0). lra.
       assert (f [x2] - f [x1] < 0 /\ / (x2 - x1) > 0). lra.
       apply (Rmult_le_gr (f [x2] - f [x1]) (/ (x2 - x1))) in H11. lra.
       intros. assert (x ∈ \( a, b \)). apply AxiomII. applyAxiomII H2.
       applyAxiomII H3. destruct H2. destruct H3. destruct H6. lra.
       apply H0 in H7. auto.
Qed.

Theorem Theorem6_3': ∀ (f : Fun) (a b : R), (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) -> derivable f x) -> IntervalDecreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] <= 0). 
Proof.   
  - intros. destruct H as [H' [H H0]]. split; intros. 
    + apply H0 in H2 as H2'. red in H2'.
      destruct H2' as [y']. apply derEqual in H3 as H3'.
      rewrite <- H3' in H3. red in H3. red in H1. 
      destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
      red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]].  
      pose proof (Rge_gt_dec 0 (f '[x])). 
      destruct H3. lra. 
      assert (Abs[f '[x]] > 0).
      { apply Abs_not_eq_0; lra.  }
      apply H10 in H3. destruct H3 as [δ0[H3 H11]].
      assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
      { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
        unfold Rbasic_fun.Rmin. applyAxiomII H2; destruct Rle_dec; 
        lra. } destruct H12 as [δ'[H12 H12']]. 
      assert(∃x1, 0 < Abs [x1 - x] < δ0 /\ x1 ∈ \( a, b \)).
      { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x).
        split. rewrite Abs_gt. replace (Rbasic_fun.Rmin δ' δ0 / 2 + x - x)
        with ((Rbasic_fun.Rmin δ' δ0) / 2); unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; lra. applyAxiomII H2; destruct H2.
        unfold Rbasic_fun.Rmin; destruct Rle_dec. 
        rewrite H12. unfold Rbasic_fun.Rmin;
        destruct Rle_dec; apply AxiomII; lra. 
        apply AxiomII. apply Rnot_le_gt in n. 
        split. lra. unfold Rbasic_fun.Rmin in H12;
        destruct Rle_dec; lra. }
      destruct H13 as [x1[H13 H13']].  
      apply H11 in H13 as H13''. 
      assert(\{\ λ x0 y,y = (f [x0] - f [x]) / (x0 - x) \}\ [x1] = (f [x1] - f [x]) / (x1 - x)). 
      { apply f_x; auto. apply AxiomII'; auto. }
      rewrite H14 in H13''. clear H14.
      assert ((f [x1] - f [x]) / (x1 - x) <= 0). 
      { destruct H13. apply <- Abs_not_eq_0 in H13. 
        apply Rdichotomy in H13. destruct H13. apply Rminus_lt in H13.
        - apply (H5 x1 x) in H13'; auto. unfold Rdiv.
          apply Rmult_gre_le. split. lra. 
          apply Rinv_lt_0_compat; lra. 
        - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto.
          unfold Rdiv. apply Rmult_leq_gre. split. lra.
          apply Rinv_0_lt_compat; lra. } 
      assert(Abs [(f [x1] - f [x]) / (x1 - x) - f '[ x]] =  - ((f [x1] - f [x]) / (x1 - x) - f '[ x])). 
      { apply Abs_lt. lra. } 
      rewrite H15 in H13''.  
      rewrite Abs_gt in H13''; auto. lra.
    + red. split.
      * assert (∃x1, x1 ∈ \( a, b \)).
        { exists ((b+a)/2). apply AxiomII.
          split; lra. }
        destruct H2 as [x1 H2]. apply H0 in H2. red in H2.
        destruct H2 as [y1 H2]. red in H2. destruct H2 as [H2 [H3 H4]].
        auto.
      * split; auto. intros.
        assert (ContinuousClose f x1 x2).
        { red. split.
          - red. intros.
            assert (x ∈ \( a, b \)).
            { apply AxiomII. applyAxiomII H2. applyAxiomII H3.
              destruct H2. destruct H3. lra. }
            apply H0 in H6. apply Theorem5_1 in H6. auto.
          - split.
            + apply H0 in H2. apply Theorem5_1 in H2. apply Theorem4_1 in H2.
              destruct H2; auto.
            + apply H0 in H3. apply Theorem5_1 in H3. apply Theorem4_1 in H3.
              destruct H3; auto. } 
         apply (Theorem6_2 f x1 x2) in H4; auto.
         destruct H4 as [ξ H4]. destruct H4. apply derEqual in H6.
         assert (ξ ∈ \( a, b \)). apply AxiomII. destruct H4.
         applyAxiomII H2. applyAxiomII H3. lra. apply H1 in H7.
         rewrite H6 in H7. unfold Rdiv in H7. 
         pose proof (Rle_or_lt f [x2] f [x1]).
         destruct H8. lra.
         assert (/ (x2 - x1) > 0).
         { assert ((x2-x1) > 0). lra.
           apply Rinv_0_lt_compat. auto. }
         assert ((f [x2] - f [x1]) > 0). lra.
         apply (Rmult_gt_0_compat (f [x2] - f [x1]) (/ (x2 - x1))) in H10. lra.
         lra.
         intros. assert (x ∈ \( a, b \)). apply AxiomII. applyAxiomII H2.
         applyAxiomII H3. destruct H2. destruct H3. destruct H6. lra.
         apply H0 in H7. auto.
Qed.


(* 函数在区间严格单调递增的充要条件 *)
Theorem Theorem6_4 : ∀ (f : Fun) (a b : R), (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) -> derivable f x) -> IntervalStrictlyIncreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] >= 0) /\ ((∀a1 b1, a1 < b1 /\ \(a1,b1\) ⊂ \(a, b\) -> ~(∀x0, x0 ∈ \(a1,b1\) -> f '[x0] = 0))).
Proof.
intros. destruct H as [K1[H H0]]. split; intros.
- split.
  + intros. 
  apply H0 in H2 as H2'. red in H2'.
  destruct H2' as [y']. apply derEqual in H3 as H3'.
  rewrite <- H3' in H3. red in H3. red in H1. 
  destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
  red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]]. 
  pose proof (Rbasic_fun.Rcase_abs (f '[x])). 
  destruct H3. assert (Abs[f '[x]] > 0).
  { apply Abs_not_eq_0; lra.  }
  apply H10 in H3. destruct H3 as [δ0[H3 H11]].
  assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
  { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
    unfold Rbasic_fun.Rmin. applyAxiomII H2; destruct Rle_dec; 
    lra. } destruct H12 as [δ'[H12 H12']]. 
  assert(∃x1, 0 < Abs [x1 - x] < δ0 /\ x1 ∈ \( a, b \)).
  { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x).
    split. rewrite Abs_gt. replace (Rbasic_fun.Rmin δ' δ0 / 2 + x - x)
    with ((Rbasic_fun.Rmin δ' δ0) / 2); unfold Rbasic_fun.Rmin;
    destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
    destruct Rle_dec; lra. applyAxiomII H2; destruct H2.
    unfold Rbasic_fun.Rmin; destruct Rle_dec. 
    rewrite H12. unfold Rbasic_fun.Rmin;
    destruct Rle_dec; apply AxiomII; lra. 
    apply AxiomII. apply Rnot_le_gt in n. 
    split. lra. unfold Rbasic_fun.Rmin in H12;
    destruct Rle_dec; lra. }
  destruct H13 as [x1[H13 H13']]. 
  apply H11 in H13 as H13''. 
  assert(\{\ λ x0 y,y = (f [x0] - f [x]) / (x0 - x) \}\ [x1] = (f [x1] - f [x]) / (x1 - x)). { apply f_x; auto. apply AxiomII'; auto. }
  rewrite H14 in H13''. clear H14. 
 assert ((f [x1] - f [x]) / (x1 - x) > 0).
 { destruct H13. apply <- Abs_not_eq_0 in H13. 
   apply Rdichotomy in H13. destruct H13. apply Rminus_lt in H13.
   - apply (H5 x1 x) in H13'; auto. unfold Rdiv.
     apply Rmult_le_le; auto. split. lra.
     apply Rinv_lt_0_compat; lra.
   - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto.
     unfold Rdiv. apply Rmult_gt_0_compat. lra.
     apply Rinv_0_lt_compat; lra. } 
  assert(Abs [(f [x1] - f [x]) / (x1 - x) - f '[ x]] = (f [x1] - f [x]) / (x1 - x) - f '[ x]). 
  { apply Abs_gt. lra. } 
  rewrite H15 in H13''. rewrite Abs_lt in H13''; auto. lra.
  auto.
  + intros. destruct H2.  
    pose proof (classic (∀x0 : R,x0 ∈ \( a1, b1 \) -> f '[ x0] = 0)).  
    destruct H4; auto.  
    red in H1. destruct H1 as [H1[H7 H6]]. 
    assert(∀x : R,x ∈ \( a1, b1 \) -> Continuous f x).
    {  intros. apply Theorem5_1; auto. }
    assert(∃x1 x2, x1 < x2 /\ \[x1,x2\] ⊂ \( a1, b1 \)).
    { exists ((3*a1+b1)/4), ((3*b1+a1)/4). split. lra.
      intros z H8. applyAxiomII H8. apply AxiomII. split;
      lra. } destruct H8 as [x1[x2[H9 H10]]].
    assert(ContinuousClose f x1 x2).
    { red.  split. red. intros. apply H5. apply H10.
      apply AxiomII. lra. split. 
      - assert(Continuous f x1).
        apply H5; apply H10; apply AxiomII; lra.
         apply Theorem4_1 in H8. eapply H8.
      - assert(Continuous f x2).
        apply H5; apply H10; apply AxiomII; lra.
         apply Theorem4_1 in H8. eapply H8.  } 
    assert(∀x : R,x1 < x < x2 -> derivable f x).
    { intros. apply H0. apply H3; apply H10. 
      apply AxiomII; lra.  } 
   apply Theorem6_2 in H8; auto. destruct H8 as [ξ[H12 H13]].
   apply derEqual in H13. assert(f '[ξ] = 0).
   apply H4. apply H10. apply AxiomII; lra.
   rewrite H8 in H13. assert(x1  ∈ \( a, b \)).
   apply H3; apply H10. apply AxiomII. lra. 
   assert(x2  ∈ \( a, b \)).
   apply H3; apply H10. apply AxiomII. lra.
   apply (H6 x1 x2) in H14; auto.
   unfold Rdiv in H13.  symmetry in H13.
   apply Rmult_integral in H13. destruct H13. lra.
   assert(x2- x1 <>0). lra.
   apply Rinv_neq_0_compat in H16. lra.  
 - destruct H1. 
   assert(IntervalIncreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] >= 0)). apply Theorem6_3; auto. pose proof H1 as H1'.
   apply <- H3 in H1. clear H3. red in H1. 
   destruct H1 as [H1[_ H3]]. 
   red; split; auto. split; auto. intros. 
   apply H3 in H6 as H6'; auto. destruct H6'; auto.
   pose proof (H2 x1 x2). assert(\( x1, x2 \) ⊂ \( a, b \)).
   { intros z H9. applyAxiomII H9. apply AxiomII. 
    applyAxiomII H4. applyAxiomII H5. split; lra. }
   assert( x1 < x2 /\ \( x1, x2 \) ⊂ \( a, b \)).
   { split; auto.  } 
   apply H8 in H10 as H10'. clear H8 H10.
   assert(∀x0, x0 ∈ \( x1, x2 \) -> f[x0] = f[x1]).
   { intros. assert(x0 ∈ \( a, b \)).
    { apply AxiomII. applyAxiomII H4. applyAxiomII H5.
      applyAxiomII H8. split; lra.  } 
    applyAxiomII H8. destruct H8.
    apply (H3 x1 x0) in H4 as H4'; auto.  
    apply (H3 x0 x2) in H11 as H11'; auto. 
    rewrite <- H7 in H11'. lra. }
    assert(∀x0 : R,x0 ∈ \( x1, x2 \) -> f '[ x0] = 0).
    { intros. apply derEqual. repeat split; auto.
      - assert(J1: ∃δ, δ > 0 /\ δ = Rbasic_fun.Rmin (b - x0) (x0 - a)).
       { exists (Rbasic_fun.Rmin (b - x0) (x0 - a)). 
       split; auto. assert(x0 ∈\( a, b \)).
       { apply H9; auto.  } applyAxiomII H11.
       unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. } 
       destruct J1 as [δ0[J2 J3]]. exists δ0; split; auto.
       intros z J4. apply H. apply AxiomII. applyAxiomII J4.
       apply Abs_R in J4.  
       unfold Rbasic_fun.Rmin in J3; destruct Rle_dec in J3; lra.
      - QED_function.
      - assert(∃δ, δ > 0 /\ δ = Rbasic_fun.Rmin (x2 - x0) (x0 - x1)).
       { exists (Rbasic_fun.Rmin (x2 - x0) (x0 - x1)). 
       split; auto. applyAxiomII H10.
       unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. }
       destruct H11 as [δ'[H11 H12]].
       exists δ'; split; auto.
       split. intros z H13. apply AxiomII. 
       exists ((f [z] - f [x0]) / (z - x0)). 
       apply AxiomII'; auto. intros.
       assert(∃δ, δ > 0 /\ δ < δ').
       { exists (δ'/2). lra. } destruct H14 as [δ[H14 H15]].
       exists δ. split; auto. intros. 
       assert(x ∈ \( x1, x2 \)).
       { apply AxiomII. destruct H16.
       unfold Rbasic_fun.Rmin in H12;  
       destruct Rle_dec in H12.
       applyAxiomII H10; destruct H10;
       apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
       destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto.  
       lra. rewrite Abs_gt in H17; auto;lra.
       apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
       destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto.  
       lra. rewrite Abs_gt in H17; auto;lra. }
       assert(\{\ λ x3 y, y = (f [x3] - f [x0]) / (x3 - x0) \}\ [x] = (f [x] - f [x0]) / (x - x0)). 
       { apply f_x. QED_function. apply AxiomII'; auto.  } 
       rewrite H18. apply H8 in H17. apply H8 in H10.
       rewrite H17. rewrite H10.
       rewrite Abs_ge. lra. lra. } 
       elim H10'; auto. 
Qed.

(* 函数在区间严格单调递减的充要条件 *)
Theorem Theorem6_4' : ∀ (f : Fun) (a b : R), (a < b /\ \(a, b\) ⊂ dom[f] /\ ∀x, x ∈ \(a, b\) -> derivable f x) -> IntervalStrictlyDecreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] <= 0) /\ ((∀a1 b1, a1 < b1 /\ \(a1,b1\) ⊂ \(a, b\) -> ~(∀x0, x0 ∈ \(a1,b1\) -> f '[x0] = 0))).
Proof. 
intros. destruct H as [K1[H H0]]. split; intros.
- split.
  + intros. 
  apply H0 in H2 as H2'. red in H2'.
  destruct H2' as [y']. apply derEqual in H3 as H3'.
  rewrite <- H3' in H3. red in H3. red in H1. 
  destruct H1 as [H1[H4 H5]]. destruct H3 as [_[H6 H7]].
  red in H7. destruct H7 as [H7[δ[H8[H9 H10]]]].
  pose proof (Rge_gt_dec 0 (f '[x])). 
  destruct H3. lra. 
   assert (Abs[f '[x]] > 0).
  { apply Abs_not_eq_0; lra.  }
  apply H10 in H3. destruct H3 as [δ0[H3 H11]].
  assert(∃δ', δ' = Rbasic_fun.Rmin (b-x) (x-a) /\ δ' > 0).
  { exists (Rbasic_fun.Rmin (b - x) (x - a)). split; auto.
    unfold Rbasic_fun.Rmin. applyAxiomII H2; destruct Rle_dec; 
    lra. } destruct H12 as [δ'[H12 H12']]. 
  assert(∃x1, 0 < Abs [x1 - x] < δ0 /\ x1 ∈ \( a, b \)).
  { exists ((Rbasic_fun.Rmin δ' δ0)/2 + x).
    split. rewrite Abs_gt. replace (Rbasic_fun.Rmin δ' δ0 / 2 + x - x)
    with ((Rbasic_fun.Rmin δ' δ0) / 2); unfold Rbasic_fun.Rmin;
    destruct Rle_dec; lra. unfold Rbasic_fun.Rmin;
    destruct Rle_dec; lra. applyAxiomII H2; destruct H2.
    unfold Rbasic_fun.Rmin; destruct Rle_dec. 
    rewrite H12. unfold Rbasic_fun.Rmin;
    destruct Rle_dec; apply AxiomII; lra. 
    apply AxiomII. apply Rnot_le_gt in n. 
    split. lra. unfold Rbasic_fun.Rmin in H12;
    destruct Rle_dec; lra. } 
  destruct H13 as [x1[H13 H13']]. 
  apply H11 in H13 as H13''. 
  assert(\{\ λ x0 y,y = (f [x0] - f [x]) / (x0 - x) \}\ [x1] = (f [x1] - f [x]) / (x1 - x)). { apply f_x; auto. apply AxiomII'; auto. } 
  rewrite H14 in H13''. clear H14.
 assert ((f [x1] - f [x]) / (x1 - x) < 0).
 { destruct H13. apply <- Abs_not_eq_0 in H13. 
   apply Rdichotomy in H13. destruct H13. apply Rminus_lt in H13.
   - apply (H5 x1 x) in H13'; auto. unfold Rdiv.
     rewrite Rmult_comm.
     apply Rmult_le_gr. split.
     apply Rinv_lt_0_compat; lra. lra.
   - apply Rminus_gt in H13. apply (H5 x x1) in H2; auto.
     unfold Rdiv.  apply Rmult_le_gr. split. lra.
     apply Rinv_0_lt_compat; lra. }  
  assert(Abs [(f [x1] - f [x]) / (x1 - x) - f '[ x]] =  - ((f [x1] - f [x]) / (x1 - x) - f '[ x])). 
  {  apply Abs_lt. lra. } 
  rewrite H15 in H13''.  
   rewrite Abs_gt in H13''; auto. lra.
  + intros. destruct H2.  
    pose proof (classic (∀x0 : R,x0 ∈ \( a1, b1 \) -> f '[ x0] = 0)).  
    destruct H4; auto.  
    red in H1. destruct H1 as [H1[H7 H6]]. 
    assert(∀x : R,x ∈ \( a1, b1 \) -> Continuous f x).
    {  intros. apply Theorem5_1; auto. }
    assert(∃x1 x2, x1 < x2 /\ \[x1,x2\] ⊂ \( a1, b1 \)).
    { exists ((3*a1+b1)/4), ((3*b1+a1)/4). split. lra.
      intros z H8. applyAxiomII H8. apply AxiomII. split;
      lra. } destruct H8 as [x1[x2[H9 H10]]].
    assert(ContinuousClose f x1 x2).
    { red.  split. red. intros. apply H5. apply H10.
      apply AxiomII. lra. split. 
      - assert(Continuous f x1).
        apply H5; apply H10; apply AxiomII; lra.
         apply Theorem4_1 in H8. eapply H8.
      - assert(Continuous f x2).
        apply H5; apply H10; apply AxiomII; lra.
         apply Theorem4_1 in H8. eapply H8.  } 
    assert(∀x : R,x1 < x < x2 -> derivable f x).
    { intros. apply H0. apply H3; apply H10. 
      apply AxiomII; lra.  } 
   apply Theorem6_2 in H8; auto. destruct H8 as [ξ[H12 H13]].
   apply derEqual in H13. assert(f '[ξ] = 0).
   apply H4. apply H10. apply AxiomII; lra.
   rewrite H8 in H13. assert(x1  ∈ \( a, b \)).
   apply H3; apply H10. apply AxiomII. lra. 
   assert(x2  ∈ \( a, b \)).
   apply H3; apply H10. apply AxiomII. lra.
   apply (H6 x1 x2) in H14; auto.
   unfold Rdiv in H13.  symmetry in H13.
   apply Rmult_integral in H13. destruct H13. lra.
   assert(x2- x1 <>0). lra.
   apply Rinv_neq_0_compat in H16. lra.  
 - destruct H1. 
   assert(IntervalDecreaseFun f (\( a, b \)) <-> (∀x, x ∈ \(a, b\) -> f '[x] <= 0)). apply Theorem6_3'; auto. pose proof H1 as H1'.
   apply <- H3 in H1. clear H3. red in H1. 
   destruct H1 as [H1[_ H3]]. 
   red; split; auto. split; auto. intros. 
   apply H3 in H6 as H6'; auto. destruct H6'; auto.
   pose proof (H2 x1 x2). assert(\( x1, x2 \) ⊂ \( a, b \)).
   { intros z H9. applyAxiomII H9. apply AxiomII. 
    applyAxiomII H4. applyAxiomII H5. split; lra. }
   assert( x1 < x2 /\ \( x1, x2 \) ⊂ \( a, b \)).
   { split; auto.  } 
   apply H8 in H10 as H10'. clear H8 H10.
   assert(∀x0, x0 ∈ \( x1, x2 \) -> f[x0] = f[x1]).
   { intros. assert(x0 ∈ \( a, b \)).
    { apply AxiomII. applyAxiomII H4. applyAxiomII H5.
      applyAxiomII H8. split; lra.  } 
    applyAxiomII H8. destruct H8.
    apply (H3 x1 x0) in H4 as H4'; auto.  
    apply (H3 x0 x2) in H11 as H11'; auto. 
    rewrite <- H7 in H11'. lra. }
    assert(∀x0 : R,x0 ∈ \( x1, x2 \) -> f '[ x0] = 0).
    { intros. apply derEqual. repeat split; auto.
      - assert(J1: ∃δ, δ > 0 /\ δ = Rbasic_fun.Rmin (b - x0) (x0 - a)).
       { exists (Rbasic_fun.Rmin (b - x0) (x0 - a)). 
       split; auto. assert(x0 ∈\( a, b \)).
       { apply H9; auto.  } applyAxiomII H11.
       unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. } 
       destruct J1 as [δ0[J2 J3]]. exists δ0; split; auto.
       intros z J4. apply H. apply AxiomII. applyAxiomII J4.
       apply Abs_R in J4.  
       unfold Rbasic_fun.Rmin in J3; destruct Rle_dec in J3; lra.
      - QED_function.
      - assert(∃δ, δ > 0 /\ δ = Rbasic_fun.Rmin (x2 - x0) (x0 - x1)).
       { exists (Rbasic_fun.Rmin (x2 - x0) (x0 - x1)). 
       split; auto. applyAxiomII H10.
       unfold Rbasic_fun.Rmin; destruct Rle_dec; lra. }
       destruct H11 as [δ'[H11 H12]].
       exists δ'; split; auto.
       split. intros z H13. apply AxiomII. 
       exists ((f [z] - f [x0]) / (z - x0)). 
       apply AxiomII'; auto. intros.
       assert(∃δ, δ > 0 /\ δ < δ').
       { exists (δ'/2). lra. } destruct H14 as [δ[H14 H15]].
       exists δ. split; auto. intros. 
       assert(x ∈ \( x1, x2 \)).
       { apply AxiomII. destruct H16.
       unfold Rbasic_fun.Rmin in H12;  
       destruct Rle_dec in H12.
       applyAxiomII H10; destruct H10;
       apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
       destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto.  
       lra. rewrite Abs_gt in H17; auto;lra.
       apply Abs_not_eq_0 in H16; apply Rdichotomy in H16.
       destruct H16 as [H16|H16]. rewrite Abs_lt in H17; auto.  
       lra. rewrite Abs_gt in H17; auto;lra. }
       assert(\{\ λ x3 y, y = (f [x3] - f [x0]) / (x3 - x0) \}\ [x] = (f [x] - f [x0]) / (x - x0)). 
       { apply f_x. QED_function. apply AxiomII'; auto.  } 
       rewrite H18. apply H8 in H17. apply H8 in H10.
       rewrite H17. rewrite H10.
       rewrite Abs_ge. lra. lra. } 
       elim H10'; auto. 
Qed.

Theorem Theorem3_2' : ∀ (f : Fun) (x0 A B : R),
  limit_pos f x0 A -> limit_pos f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1. 
  assert (H2 : ∀ ε : R, ε > 0 -> Abs[A-B] < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, x0 < x < x0 + δ1 /\ x0 < x < x0 + δ2).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 + δ1 / 2). lra.
      - exists (x0 + δ2 / 2). lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14.
    apply I13 in I15. generalize (Abs_minus_le (f[x] - A) (f[x] - B)).
    intro I16. assert (I17 : f[x] - A - (f[x] - B) = -(A-B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A-B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : Abs[A - B] / 4 > 0). lra. apply H2 in H5. lra.
Qed.

Theorem derivativeUnique' : ∀ (f : Fun) (x0 A B : R),
  derivative_pos f x0 A -> derivative_pos f x0 B -> A = B.
Proof.
  unfold derivative_pos.
  intros f x0 A B [H0 [H1 H2]] [H3 [H4 H5]].
  eapply Theorem3_2'; eauto.
Qed.

Definition der' f x := cR \{ λ y', derivative_pos f x y' \}.

Notation "f '+ [ x ]" := (der' f x)(at level 20).

Theorem derEqual' : ∀ (f : Fun) (x y' : R),
  derivative_pos f x y' -> f '+ [x] = y'.
Proof.
  intros f x y' H0.
  assert (H1 : derivative_pos f x (f '+ [ x ])).
  { assert (I1 : NotEmpty \{ λ y', derivative_pos f x y' \}).
    { exists y'. apply AxiomII. assumption. }
    apply AxiomcR in I1. applyAxiomII I1.
    assumption. } 
  eapply derivativeUnique'; eauto.
Qed.

Theorem Theorem3_2'' : ∀ (f : Fun) (x0 A B : R),
  limit_neg f x0 A -> limit_neg f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1. 
  assert (H2 : ∀ ε : R, ε > 0 -> Abs[A-B] < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, x0 - δ1 < x < x0 /\ x0 - δ2 < x < x0).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 - δ1 / 2). lra.
      - exists (x0 - δ2 / 2). lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14.
    apply I13 in I15. generalize (Abs_minus_le (f[x] - A) (f[x] - B)).
    intro I16. assert (I17 : f[x] - A - (f[x] - B) = -(A-B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A-B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : Abs[A - B] / 4 > 0). lra. apply H2 in H5. lra.
Qed.

Theorem derivativeUnique'' : ∀ (f : Fun) (x0 A B : R),
  derivative_neg f x0 A -> derivative_neg f x0 B -> A = B.
Proof.
  unfold derivative_pos.
  intros f x0 A B [H0 [H1 H2]] [H3 [H4 H5]].
  eapply Theorem3_2''; eauto.
Qed.

Definition der'' f x := cR \{ λ y', derivative_neg f x y' \}.

Notation "f '_ [ x ]" := (der'' f x)(at level 20).

Theorem derEqual'' : ∀ (f : Fun) (x y' : R),
  derivative_neg f x y' -> f '_ [x] = y'.
Proof.
  intros f x y' H0.
  assert (H1 : derivative_neg f x (f '_ [ x ])).
  { assert (I1 : NotEmpty \{ λ y', derivative_neg f x y' \}).
    { exists y'. apply AxiomII. assumption. }
    apply AxiomcR in I1. applyAxiomII I1.
    assumption. } 
  eapply derivativeUnique''; eauto.
Qed.

Theorem Theorem5_4_2' : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative_pos \{\ λ x y, y = u[x] - v[x] \}\
    x0 (u '+ [x0] - v '+ [x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1]. 
  assert (H2 :∃y, derivative_pos u x0 y).
  { red in H0. 
    destruct H0 as [H4 [H5 H6]]. destruct H5 as [δ' [H5 H5']].
    exists y1. 
    split; auto. split. exists δ'. split; auto. red. intros z H7.
    red in H5'. pose proof (H5' z).
    assert (z ∈ Neighbor x0 δ').
    { apply AxiomII. applyAxiomII H7. destruct H7. rewrite Abs_ge; lra. }
    apply H in H0. auto.
    red. red in H6. destruct H6 as [H6 H7].
    destruct H7 as [δ'' [H7 [H8 H9]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((u [z] - u [x0]) / (z - x0)).
      apply AxiomII'. auto.
    - intros. apply H9 in H. destruct H as [δ'''[H H10]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - x0] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
      apply H10 in H2. auto. }
  destruct H2 as [y1' H2]. apply derEqual' in H2 as H2'.
  assert (H3: ∃y, derivative_pos v x0 y).
  { red in H1. 
    destruct H1 as [H4 [H5 H6]]. destruct H5 as [δ' [H5 H5']].
    exists y2. 
    split; auto. split. exists δ'. split; auto. red. intros z H7.
    red in H5'. pose proof (H5' z).
    assert (z ∈ Neighbor x0 δ').
    { apply AxiomII. applyAxiomII H7. destruct H7. rewrite Abs_ge; lra. }
    apply H in H1. auto.
    red. red in H6. destruct H6 as [H6 H7].
    destruct H7 as [δ'' [H7 [H8 H9]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((v [z] - v [x0]) / (z - x0)).
      apply AxiomII'. auto.
    - intros. apply H9 in H. destruct H as [δ'''[H H10]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - x0] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
      apply H10 in H3. auto. }
  destruct H3 as [y2' H3]. apply derEqual' in H3 as H3'.
  
  rewrite H2'; rewrite H3'.
  clear H2' H3'.
  assert (H4 : Function \{\ λ x y, y = u[x] - v[x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H2 as [H2 [[δ1' [H5 H6]] H7]].
  destruct H3 as [H3 [[δ2' [H8 H9]] H10]].
  generalize (Lemma1 δ1' δ2' H5 H8);
  intros [δ' [H11 [H12 H13]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] - v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H14 : Function \{\ λ x y, y =
      (\{\ λ x1 y0, y0 = u[x1] - v[x1] \}\[x]
      - \{\ λ x1 y0, y0 = u[x1] - v[x1] \}\[x0])
      / (x - x0) \}\).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists ((\{\ λ x y, y = u[x] - v[x] \}\[x]
      - \{\ λ x y, y = u[x] - v[x] \}\[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H15.
      destruct H7 as [H7 [δ3' [H16 [H17 H18]]]].
      destruct H10 as [H10 [δ4' [H19 [H20 H21]]]].
      assert (H22 : ε/2 > 0). lra.
      apply H21 in H22 as H23.
      destruct H23 as [δ2 [[H23 H27] H24]].
      apply H18 in H22 as [δ1 [[H25 H28] H26]].
      generalize (Lemma1' δ' δ1 δ2 H11 H25 H23).
      intros [δ [H29 [H30 [H31 H32]]]].
      exists δ. split; try lra. intros x H33.
      assert (H34 : \{\ λ x y, y =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0) \}\[x] =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H34. clear H34.
      assert (H34 : ∀ x1, \{\ λ x y,
        y = u[x] - v[x] \}\ [x1] = u[x1] - v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H34; auto.
      rewrite H34; auto.  
      assert (H39 : x0 < x < x0 + δ1). lra.
      apply H26 in H39.
      assert (H40 : x0 < x < x0 + δ2). lra.
      apply H24 in H40.
      assert (H41 : \{\ λ x y, y =
        (u[x] - u[x0]) / (x - x0) \}\ [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H41 in H39. clear H41.
      assert (H41 : \{\ λ x y, y =
        (v[x] - v[x0]) / (x - x0) \}\ [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H41 in H40. clear H41.
      assert (H41 : (u[x] - v[x] -
        (u[x0] - v[x0])) / (x - x0)
        - (y1' - y2') = ((u[x] - u[x0]) / (x - x0) - y1')
        - ((v[x] - v[x0]) / (x - x0) - y2')).
      { field. lra. }
      rewrite H41.
      generalize (Abs_minus_le ((u[x] - u[x0])
        / (x - x0) - y1') ((v[x] - v[x0])
        / (x - x0) - y2')). intro H42. lra.
Qed.

Theorem Theorem5_4_2'' : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative_neg \{\ λ x y, y = u[x] - v[x] \}\
    x0 (u '_ [x0] - v '_ [x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1]. 
  assert (H2 :∃y, derivative_neg u x0 y).
  { red in H0. 
    destruct H0 as [H4 [H5 H6]]. destruct H5 as [δ' [H5 H5']].
    exists y1. 
    split; auto. split. exists δ'. split; auto. red. intros z H7.
    red in H5'. pose proof (H5' z).
    assert (z ∈ Neighbor x0 δ').
    { apply AxiomII. applyAxiomII H7. destruct H7. rewrite Abs_R; lra. }
    apply H in H0. auto.
    red. red in H6. destruct H6 as [H6 H7].
    destruct H7 as [δ'' [H7 [H8 H9]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((u [z] - u [x0]) / (z - x0)).
      apply AxiomII'. auto.
    - intros. apply H9 in H. destruct H as [δ'''[H H10]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - x0] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_R; lra. }
      apply H10 in H2. auto. }
  destruct H2 as [y1' H2]. apply derEqual'' in H2 as H2'.
  assert (H3: ∃y, derivative_neg v x0 y).
  { red in H1. 
    destruct H1 as [H4 [H5 H6]]. destruct H5 as [δ' [H5 H5']].
    exists y2. 
    split; auto. split. exists δ'. split; auto. red. intros z H7.
    red in H5'. pose proof (H5' z).
    assert (z ∈ Neighbor x0 δ').
    { apply AxiomII. applyAxiomII H7. destruct H7. rewrite Abs_R; lra. }
    apply H in H1. auto.
    red. red in H6. destruct H6 as [H6 H7].
    destruct H7 as [δ'' [H7 [H8 H9]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((v [z] - v [x0]) / (z - x0)).
      apply AxiomII'. auto.
    - intros. apply H9 in H. destruct H as [δ'''[H H10]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - x0] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_R; lra. }
      apply H10 in H3. auto. }
  destruct H3 as [y2' H3]. apply derEqual'' in H3 as H3'.
    rewrite H2'; rewrite H3'.
  clear H2' H3'.
  assert (H4 : Function \{\ λ x y, y = u[x] - v[x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H2 as [H2 [[δ1' [H5 H6]] H7]].
  destruct H3 as [H3 [[δ2' [H8 H9]] H10]].
  generalize (Lemma1 δ1' δ2' H5 H8);
  intros [δ' [H11 [H12 H13]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] - v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H14 : Function \{\ λ x y, y =
      (\{\ λ x1 y0, y0 = u[x1] - v[x1] \}\[x]
      - \{\ λ x1 y0, y0 = u[x1] - v[x1] \}\[x0])
      / (x - x0) \}\).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists ((\{\ λ x y, y = u[x] - v[x] \}\[x]
      - \{\ λ x y, y = u[x] - v[x] \}\[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H15.
      destruct H7 as [H7 [δ3' [H16 [H17 H18]]]].
      destruct H10 as [H10 [δ4' [H19 [H20 H21]]]].
      assert (H22 : ε/2 > 0). lra.
      apply H21 in H22 as H23.
      destruct H23 as [δ2 [[H23 H27] H24]].
      apply H18 in H22 as [δ1 [[H25 H28] H26]].
      generalize (Lemma1' δ' δ1 δ2 H11 H25 H23).
      intros [δ [H29 [H30 [H31 H32]]]].
      exists δ. split; try lra. intros x H33.
      assert (H34 : \{\ λ x y, y =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0) \}\[x] =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H34. clear H34.
      assert (H34 : ∀ x1, \{\ λ x y,
        y = u[x] - v[x] \}\ [x1] = u[x1] - v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H34; auto.
      rewrite H34; auto.   
      assert (H39 : x0 - δ1 < x < x0). lra.
      apply H26 in H39.
      assert (H40 : x0 - δ2 < x < x0). lra.
      apply H24 in H40.
      assert (H41 : \{\ λ x y, y =
        (u[x] - u[x0]) / (x - x0) \}\ [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H41 in H39. clear H41.
      assert (H41 : \{\ λ x y, y =
        (v[x] - v[x0]) / (x - x0) \}\ [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H41 in H40. clear H41.
      assert (H41 : (u[x] - v[x] -
        (u[x0] - v[x0])) / (x - x0)
        - (y1' - y2') = ((u[x] - u[x0]) / (x - x0) - y1')
        - ((v[x] - v[x0]) / (x - x0) - y2')).
      { field. lra. }
      rewrite H41.
      generalize (Abs_minus_le ((u[x] - u[x0])
        / (x - x0) - y1') ((v[x] - v[x0])
        / (x - x0) - y2')). intro H42. lra.
Qed.
  


Theorem Theorem3_4_1' : ∀ (f : Fun) (x0 A : R), limit_pos f x0 A -> A > 0 -> (∀ r, 0 < r < A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (rightNeighbor0 x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4_1'' : ∀ (f : Fun) (x0 A : R), limit_neg f x0 A -> A < 0 -> (∀ r, 0 < r < (- A) -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (leftNeighbor0 x0 δ) -> f[x] < - r < 0))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : - A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Lemma Lemma_5_8 : ∀ (f :Fun) (x0 : R), 
  (derivative_pos f x0 (f '+ [x0]) /\ f '+ [x0] > 0)
  -> (∃ δ, δ > 0 /\ (∀x , x ∈ \(x0, x0 + δ\) -> f [x0] < f [x])).
Proof.   
  intros. destruct H.  
  red in H. destruct H as [H [H3 H4]]. 
  assert (∃g, g = \{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\).
  { exists \{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\. auto. }
  destruct H1 as [g H1].
  rewrite <- H1 in H4.
  assert ((∀ r, 0 < r < (f '+ [x0]) -> (∃ δ, δ > 0 /\
         (∀ x, x ∈ (rightNeighbor0 x0 δ) -> 0 < r < g[x])))).
  { apply Theorem3_4_1'; auto. }
  pose proof (H2 ((f '+ [x0])/2)).   
  assert (0 < f '+ [x0] / 2 < f '+ [x0]). lra. apply H5 in H6.
  destruct H6 as [δ [H6 H7]]. exists δ. split; auto. intros. pose proof H8 as H8'.
  apply H7 in H8. 
  assert (0 < g [x]). lra. rewrite H1 in H9.
  assert (\{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\ [x] = 
              ((f [x] - f [x0]) / (x - x0))).
  { apply f_x. red. intros. applyAxiomII' H10. applyAxiomII' H11.
    rewrite H10. auto. 
    apply AxiomII'. auto. }
  rewrite H10 in H9. 
  assert ((x - x0) > 0). 
  { applyAxiomII H8'. lra. } 
  apply (Rmult_lt_0_compat (x - x0) ((f [x] - f [x0]) / (x - x0))) in H11 as H12.
  unfold Rdiv in H12. rewrite <- Rmult_assoc in H12.
  rewrite Rinv_r_simpl_m in H12. lra. lra. lra.
Qed.


Lemma Lemma_5_8_1 : ∀ (f :Fun) (a b x0: R), a < b /\ (a ∈ \[ a, b \)) /\
    (derivative_pos f a (f '+ [a]) /\ f '+ [a] > 0)
  -> (∃ δ, δ > 0 /\ δ < b -a /\ (∀x , x ∈ \(a, a + δ\) -> f [a] < f [x])).
Proof.  
  intros. destruct H as [I1 [I2 [H H0]]].
  red in H. destruct H as [H [H3 H4]]. 
  assert (∃g, g = \{\ λ x y, y = (f [x] - f [a]) / (x - a) \}\).
  { exists \{\ λ x y, y = (f [x] - f [a]) / (x - a) \}\. auto. }
  destruct H1 as [g H1].
  rewrite <- H1 in H4.
  assert ((∀ r, 0 < r < (f '+ [a]) -> (∃ δ, δ > 0 /\
         (∀ x, x ∈ (rightNeighbor0 a δ) -> 0 < r < g[x])))).
  { apply Theorem3_4_1'; auto. } 
  pose proof (H2 ((f '+ [a])/2)).  
  assert (0 < f '+ [a] / 2 < f '+ [a]). lra. apply H5 in H6.
  destruct H6 as [δ [H6 H7]]. 
  
  assert (I3: ∃δ', δ > δ' /\ δ' > 0 /\ δ' < b-a).
  { exists (Rbasic_fun.Rmin (δ/2) (b - a)/2). split.
    unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra.
    split. unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra.
    unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra. }
  destruct I3 as [δ' I3]. exists δ'. destruct I3 as [I3 [I3' I3'']].
  split; auto. split. lra. intros.
  assert(x ∈ rightNeighbor0 a δ ).
  apply AxiomII. applyAxiomII H8. lra.
  apply H7 in H9. 
  assert (0 < g [x]). lra. rewrite H1 in H10.
  assert (\{\ λ x y, y = (f [x] - f [a]) / (x - a) \}\ [x] = 
              ((f [x] - f [a]) / (x - a))).
  { apply f_x. red. intros. applyAxiomII' H11. applyAxiomII' H12.
    rewrite H11. auto. 
    apply AxiomII'. auto. }
  rewrite H11 in H10. 
  assert ((x - a) > 0). 
  { applyAxiomII H8. lra. } 
  apply (Rmult_lt_0_compat (x - a) ((f [x] - f [a]) / (x - a))) in H12 as H13.
  unfold Rdiv in H13. rewrite <- Rmult_assoc in H13.
  rewrite Rinv_r_simpl_m in H13. lra. lra. lra. 
Qed.

Lemma Lemma_5_8_2 : ∀ (f :Fun) (a b : R),  a < b /\ (b ∈ \( a, b \]) /\
  (derivative_neg f b (f '_ [b]) /\ f '_ [b] < 0)
  -> (∃ δ, δ > 0 /\  δ < b -a /\ (∀x , x ∈ \(b - δ, b\) -> f [b] < f [x])).
Proof. 
  intros. destruct H as [I1 [I2 [H H0]]]. 
  red in H. destruct H as [H [H3 H4]]. 
  assert (∃g, g = \{\ λ x y, y = (f [x] - f [b]) / (x - b) \}\).
  { exists \{\ λ x y, y = (f [x] - f [b]) / (x - b) \}\. auto. }
  destruct H1 as [g H1].
  rewrite <- H1 in H4.
  assert ((∀ r, 0 < r < - (f '_ [b]) -> (∃ δ, δ > 0 /\
         (∀ x, x ∈ (leftNeighbor0 b δ) ->  g[x] < - r < 0)))).     
  { apply Theorem3_4_1''; auto. } 
  pose proof (H2 (-(f '_ [b])/2)).  
  assert (0 < - f '_ [b] / 2 < - f '_ [b]). lra. apply H5 in H6.
  destruct H6 as [δ [H6 H7]]. 
  assert (I3: ∃δ', δ > δ' /\ δ' > 0 /\ δ' < b-a).
  { exists (Rbasic_fun.Rmin (δ/2) (b - a)/2). split.
    unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra.
    split. unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra.
    unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. lra. }
  destruct I3 as [δ' I3]. exists δ'. destruct I3 as [I3 [I3' I3'']].
  split; auto. split. lra. intros.
  assert(x ∈ leftNeighbor0 b δ ).
  apply AxiomII. applyAxiomII H8. lra.
  apply H7 in H9. 
  assert (g [x] < 0). lra. rewrite H1 in H10.
  assert (\{\ λ x y, y = (f [x] - f [b]) / (x - b) \}\ [x] = 
              ((f [x] - f [b]) / (x - b))).
  { apply f_x. red. intros. applyAxiomII' H11. applyAxiomII' H12.
    rewrite H11. auto. apply AxiomII'. auto. }
  rewrite H11 in H10. 
  assert ((x - b) < 0). 
  { applyAxiomII H8. lra. }
  assert (x - b < 0 /\ (f [x] - f [b]) / (x - b) < 0). lra.
  apply (Rmult_le_le (x - b) ((f [x] - f [b]) / (x - b))) in H13.
  unfold Rdiv in H13. rewrite <- Rmult_assoc in H13.
  rewrite Rinv_r_simpl_m in H13. lra. lra. 
Qed.


Theorem Theorem6_5 : ∀ (f : Fun) (a b : R), a < b /\ (∀x, x ∈ \[a, b\] -> derivable f x) -> derivative_pos f a (f '+ [a]) <> derivative_neg f b (f '_ [b]) -> (∀k, k ∈ \(f '_ [b], f '+ [a]\) -> ∃ ξ, a < ξ < b /\ derivative f ξ k).
Proof.   
  intros.  
  assert (∃g: Fun, g = \{\ λ x y, y = k*x \}\ ).
  { exists \{\ λ x0 y, y = k * x0 \}\. auto. } 
  destruct H2 as [g H2].  
  assert (∃F: Fun, F = \{\ λ x y, y = f[x] - g[x] \}\).
  { exists \{\ λ x y, y = f [x] - g[x] \}\. auto. }
  destruct H3 as [F H3]. destruct H as [H' H].
  assert (∀x, g[x] = k * x). 
  { rewrite H2. intros.
    assert (\{\ λ x0 y, y = k * x0 \}\ [x] = k * x).
    { apply f_x. red. intros. applyAxiomII' H4. applyAxiomII' H5.
      rewrite H4. auto. apply AxiomII'. auto. }
    rewrite H4. auto. }
  assert ((∀x, x ∈ \[a, b\] -> derivable F x)).
  { intros. red. apply H in H5 as H6. red in H6. destruct H6 as [y0' H6].
    assert (derivable g x).
    { red. exists k. pose proof (Lemma5_5 0 k x 1).
      assert (\{\ λ x y, y = k * (x - 0) ^^ 1 \}\ = \{\ λ x0 y, y = k * x0 \}\).
      simpl. apply AxiomI. split; intros. applyAxiomII H8. 
      destruct H8 as [x3[y3[H8 H8']]]. apply AxiomII. exists x3,y3. split; auto.
      rewrite Rminus_0_r in H8'. rewrite Rmult_1_r in H8'. auto.
      applyAxiomII H8. destruct H8 as [x3[y3[H8 H8']]]. apply AxiomII.
      exists x3, y3. split; auto. rewrite Rminus_0_r. rewrite Rmult_1_r.
      auto. rewrite H8 in H7. clear H8.
      rewrite Rminus_0_r in H7. 
      assert ( (k * INR 1 * x ^^ (1 - 1)) = k).
      { simpl. lra. }
      rewrite H8 in H7. rewrite H2. auto. }
      pose proof H7 as H7'.
      red in H7. destruct H7 as [y0'' H7].
      apply derEqual in H6. apply derEqual in H7.
      exists (y0' - y0'').
      rewrite <- H6. rewrite <- H7. rewrite H3.
      apply (Theorem5_4_2 f g x); auto. } 
  assert (∃y, derivative_pos f a y).
  { pose proof (H a).
    assert (a ∈ \[ a, b \]).
    { apply AxiomII. split. right. auto. left. auto. }
    apply H6 in H7. red in H7. destruct H7 as [y0' H7]. red in H7.
    destruct H7 as [H7 [H8 H9]]. destruct H8 as [δ' [H8 H8']].
    exists y0'. 
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H8'. pose proof (H8' z).
    assert (z ∈ Neighbor a δ').
    { apply AxiomII. applyAxiomII H10. destruct H10. rewrite Abs_ge; lra. }
    apply H11 in H12. auto.
    red. red in H9. destruct H9 as [H9 H10].
    destruct H10 as [δ'' [H10 [H11 H12]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((f [z] - f [a]) / (z - a)).
      apply AxiomII'. auto.
    - intros. apply H12 in H13. destruct H13 as [δ'''[H13 H14]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - a] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
      apply H14 in H16. auto. }
  destruct H6 as [y H6]. apply derEqual' in H6 as H6'.
  
  assert (∃y, derivative_neg f b y).
  { pose proof (H b).
    assert (b ∈ \[ a, b \]).
    { apply AxiomII. split. left. auto. right. auto. }
    apply H7 in H8. red in H8. destruct H8 as [y0' H8]. red in H8.
    destruct H8 as [H8 [H9 H10]]. destruct H9 as [δ' [H9 H9']].
    exists y0'.
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H9'. pose proof (H9' z).
    assert (z ∈ Neighbor b δ').
    { apply AxiomII. applyAxiomII H11. destruct H11. destruct H13.
      - rewrite Abs_lt; lra.
      - rewrite H13. apply Abs_R; lra. }
    apply H12 in H13. auto.
    red. red in H10. destruct H10 as [H10 H11].
    destruct H11 as [δ'' [H11 [H12 H13]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((f [z] - f [b]) / (z - b)).
      apply AxiomII'. auto.
    - intros. apply H13 in H14. destruct H14 as [δ'''[H14 H15]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - b] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_lt; lra. }
      apply H15 in H17. auto. }
  destruct H7 as [y' H7]. apply derEqual'' in H7 as H7'.
  
  assert (∃y, derivative_pos F a y).
  { pose proof (H5 a).
    assert (a ∈ \[ a, b \]).
    { apply AxiomII. split. right. auto. left. auto. }
    apply H8 in H9. red in H9. destruct H9 as [y0' H9]. red in H9.
    destruct H9 as [H9 [H10 H11]]. destruct H10 as [δ' [H10 H10']].
    exists y0'. red. 
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H10'. pose proof (H10' z).
    assert (z ∈ Neighbor a δ').
    { apply AxiomII. applyAxiomII H12. destruct H12. rewrite Abs_ge; lra. }
    apply H13 in H14. auto.
    red. red in H11. destruct H11 as [H11 H12].
    destruct H12 as [δ'' [H12 [H13 H14]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((F [z] - F [a]) / (z - a)).
      apply AxiomII'. auto.
    - intros. apply H14 in H15. destruct H15 as [δ'''[H15 H16]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - a] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
      apply H16 in H18. auto. }
  destruct H8 as [y1 H8]. apply derEqual' in H8 as H8'.
  
  assert (∃y, derivative_neg F b y).
  { pose proof (H5 b).
    assert (b ∈ \[ a, b \]).
    { apply AxiomII. split. left. auto. right. auto. }
    apply H9 in H10. red in H10. destruct H10 as [y0' H10]. red in H10.
    destruct H10 as [H10 [H11 H12]]. destruct H11 as [δ' [H11 H11']].
    exists y0'.
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H11'. pose proof (H11' z).
    assert (z ∈ Neighbor b δ').
    { apply AxiomII. applyAxiomII H13. destruct H13. destruct H15.
      - rewrite Abs_lt; lra.
      - rewrite H15. apply Abs_R; lra. }
    apply H14 in H15. auto.
    red. red in H12. destruct H12 as [H12 H13].
    destruct H13 as [δ'' [H13 [H14 H15]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((F [z] - F [b]) / (z - b)).
      apply AxiomII'. auto.
    - intros. apply H15 in H16. destruct H16 as [δ'''[H16 H17]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - b] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_lt; lra. }
      apply H17 in H19. auto. }
  destruct H9 as [y1' H9]. apply derEqual'' in H9 as H9'.  
  
  assert (∀x : R,x ∈ \[ a, b \] -> derivative g x k).
  { intros. pose proof (Lemma5_5 0 k x 1).
    assert (\{\ λ x y, y = k * (x - 0) ^^ 1 \}\ = \{\ λ x0 y, y = k * x0 \}\).
    simpl. apply AxiomI. split; intros. applyAxiomII H12. 
    destruct H12 as [x3[y3[H12 H12']]]. apply AxiomII. exists x3,y3. split; auto.
    rewrite Rminus_0_r in H12'. rewrite Rmult_1_r in H12'. auto.
    applyAxiomII H12. destruct H12 as [x3[y3[H12 H12']]]. apply AxiomII.
    exists x3, y3. split; auto. rewrite Rminus_0_r. rewrite Rmult_1_r.
    auto. rewrite H12 in H11. clear H12.
    rewrite Rminus_0_r in H11. 
    assert ( (k * INR 1 * x ^^ (1 - 1)) = k).
    { simpl. lra. }
    rewrite H12 in H11. rewrite H2. auto. }
  assert (∀x : R,x ∈ \[ a, b \] -> derivable g x). 
  { intros. red. exists k. apply H10 in H11; auto. } 
   
  assert ( derivative_pos g a k).
  { pose proof (H10 a).
    assert (a ∈ \[ a, b \]).
    { apply AxiomII. split. right. auto. left. auto. }
    apply H12 in H13.
    red in H13. destruct H13 as [H13 [H14 H15]]. destruct H14 as [δ' [H14 H14']].
    red. 
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H14'. pose proof (H14' z).
    assert (z ∈ Neighbor a δ').
    { apply AxiomII. applyAxiomII H16. destruct H16. rewrite Abs_ge; lra. }
    apply H17 in H18. auto.
    red. red in H15. destruct H15 as [H15 H16].
    destruct H16 as [δ'' [H16 [H17 H18]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((g [z] - g [a]) / (z - a)).
      apply AxiomII'. auto.
    - intros. apply H18 in H19. destruct H19 as [δ'''[H19 H20]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - a] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_gt; lra. }
      apply H20 in H22. auto. }
  apply derEqual' in H12 as H12'.
  assert (derivative_neg g b k).
  { pose proof (H10 b).
    assert (b ∈ \[ a, b \]).
    { apply AxiomII. split. left. auto. right. auto. }
    apply H13 in H14.
    red in H14. destruct H14 as [H14 [H15 H16]]. destruct H15 as [δ' [H15 H15']].
    red. 
    split; auto. split. exists δ'. split; auto. red. intros.
    red in H15'. pose proof (H15' z).
    assert (z ∈ Neighbor b δ').
    { apply AxiomII. applyAxiomII H17. destruct H17. destruct H19.
      - rewrite Abs_lt; lra.
      - rewrite H19. apply Abs_R; lra. }
    apply H18 in H19. auto.
    red. red in H16. destruct H16 as [H16 H17].
    destruct H17 as [δ'' [H17 [H18 H19]]]. split; auto.
    exists δ''. split; auto. split.
    - red. intros. apply AxiomII. exists ((g [z] - g [b]) / (z - b)).
      apply AxiomII'. auto.
    - intros. apply H19 in H20. destruct H20 as [δ'''[H20 H21]].
      exists δ'''. split; auto. intros. 
      assert (0 < Abs [x - b] < δ''').
      { split. apply Abs_not_eq_0. lra. rewrite Abs_lt; lra. }
      apply H21 in H23. auto. }
  apply derEqual'' in H13 as H13'. 
  
  assert (a ∈ \[ a, b \]).
  { apply AxiomII. split. right. auto. left. auto. }
  apply H in H14 as H15. apply H10 in H14 as H15'. 
  assert ( derivative_pos \{\ λ x y, y = f[x] - g[x] \}\ a (f '+ [a] - g '+ [a]) ).
  { apply Theorem5_4_2'; auto. }
  rewrite <- H3 in H16. apply derEqual' in H16.
  assert (b ∈ \[ a, b \]).
  { apply AxiomII. split. left. auto. right. auto. }
  apply H in H17 as H18. apply H10 in H17 as H18'.
  assert ( derivative_neg \{\ λ x y, y = f[x] - g[x] \}\ b (f '_ [b] - g '_ [b]) ).
  { apply Theorem5_4_2''; auto. }
  rewrite <- H3 in H19. apply derEqual'' in H19.
  rewrite H12' in H16. rewrite H13' in H19.
  
  assert (F '+ [a] > 0 /\ F '_ [b] < 0).
  { applyAxiomII H1. destruct H1 as [H1 H1']. split.
    - rewrite H16. lra.
    - rewrite H19. lra. }
  assert (F '+ [a] * F '_ [b] < 0). 
  { assert ( F '_ [b] < 0 /\ F '+ [a] > 0). lra.
    apply Rmult_le_gr in H21; auto. lra. } 
  
  assert ( a < b /\ (a ∈ \[ a, b \)) /\derivative_pos F a (F '+ [a]) /\ F '+ [a] > 0).
  { rewrite <- H8' in H8. split; auto. split. apply AxiomII. split.
    right. auto. auto. split; tauto. } 
  apply (Lemma_5_8_1 F a b a) in H22.
  assert (a < b /\ (b ∈ \( a, b \]) /\derivative_neg F b (F '_ [b]) /\ F '_ [b] < 0).
  { rewrite <- H9' in H9. split; auto. split. apply AxiomII.
    split; auto. right; auto. split; tauto. }
  apply Lemma_5_8_2 in H23; auto.
  destruct H22 as [δ1 [H22' [H22'' H22]]]. 
  destruct H23 as [δ2 [H23' [H23'' H23]]]. 
  assert (∃x1, x1 ∈ \( a, a + δ1 \)). exists (a+δ1/2). apply AxiomII. lra.
  destruct H24 as [x1 H24]. pose proof H24 as H24'. apply H22 in H24.
  assert (∃x2, x2 ∈ \( b - δ2, b \)). exists (b - δ2/2). apply AxiomII. lra.
  destruct H25 as [x2 H25]. pose proof H25 as H25'. apply H23 in H25.
  
  assert (∀x : R,x ∈ \[ a, b \] -> Continuous F x).
  { intros. apply H5 in H26. apply Theorem5_1 in H26. auto. }
  assert (ContinuousClose F a b).
  { red. split. 
    - red. intros. apply H26. apply AxiomII. split; left; lra.  
    - assert (Continuous F a /\ Continuous F b).
      { split.
        - apply H26. apply AxiomII. split. right. lra. left. lra.
        - apply H26. apply AxiomII. split. left. lra. right. lra. }
      destruct H27 as [H27 H27'].
      apply Theorem4_1 in H27. apply Theorem4_1 in H27'. tauto.
   }
   eapply (Theorem4_6 F a b) in H' as H28; auto. destruct H28 as [H28 H28'].
   destruct H28 as [F' H28]. red in H28. destruct H28 as [H28 [H29 H30]].
   destruct H30 as [ξ [H30 H30']]. exists ξ.
   applyAxiomII H30. destruct H30. 
   destruct H30, H31.
   - split; auto. 
     assert (extremum F ξ).
     { red. left. red. split.
       - rewrite H3. red. intros. applyAxiomII' H32. applyAxiomII' H33.
         rewrite H32. auto. 
       - exists (Rbasic_fun.Rmin (b - ξ) (ξ - a)).
         split. unfold Rbasic_fun.Rmin; destruct Rle_dec; lra.
         split.
         + red. intros. apply H28. 
           apply AxiomII. applyAxiomII H32. pose proof (Rgt_or_ge (z - ξ) 0).
           destruct H33.
           * unfold Rbasic_fun.Rmin in H32. destruct Rle_dec in H32;
             rewrite Abs_gt in H32; auto; split; left; lra; left; lra.
           * unfold Rbasic_fun.Rmin in H32. destruct Rle_dec in H32. 
             -- destruct H33.
                ++ rewrite Abs_lt in H32; auto. split; left; lra; left; lra.
                ++ symmetry in H33; apply Rminus_diag_uniq in H33; rewrite H33;
                   split; left; lra.
             -- destruct H33.
                ++ rewrite Abs_lt in H32; auto. split; left; lra; left; lra.
                ++ symmetry in H33; apply Rminus_diag_uniq in H33; rewrite H33;
                   split; left; lra.
         + intros. rewrite H30'. apply H29. applyAxiomII H32. apply AxiomII.
           pose proof (Rgt_or_ge (x - ξ) 0).
           destruct H33.
           * unfold Rbasic_fun.Rmin in H32. destruct Rle_dec in H32;
             rewrite Abs_gt in H32; auto; split; left; lra; left; lra.
           * unfold Rbasic_fun.Rmin in H32. destruct Rle_dec in H32. 
             -- destruct H33.
                ++ rewrite Abs_lt in H32; auto. split; left; lra; left; lra.
                ++ symmetry in H33; apply Rminus_diag_uniq in H33; rewrite H33;
                   split; left; lra.
             -- destruct H33.
                ++ rewrite Abs_lt in H32; auto. split; left; lra; left; lra.
                ++ symmetry in H33; apply Rminus_diag_uniq in H33; rewrite H33;
                   split; left; lra. }
     assert (ξ ∈ \[ a, b \]).
     { apply AxiomII. split. left. lra. left. lra. } pose proof H33 as H33'.
     apply H5 in H33. apply Theorem5_3 in H33; auto.
     apply derEqual in H33 as H34. 
     assert (derivative g ξ k).
     { apply H10 in H33'. auto. }
     assert (∀x : R,x ∈ \[ a, b \] -> derivative F x (f '[x] - g '[x])).
     { intros. apply H5 in H36 as H37. apply H11 in H36 as H38.
       rewrite H3. apply Theorem5_4_2; auto. }
     apply H36 in H33' as H37.
     apply derEqual in H37. apply derEqual in H35.
     rewrite H34 in H37. rewrite H35 in H37. 
     apply H in H33'. red in H33'. destruct H33'.
     apply derEqual in H38 as H39. rewrite <- H39 in H38.
     symmetry in H37. apply Rminus_diag_uniq in H37.
     rewrite <- H37. auto.
  - rewrite <- H31 in H25. rewrite H30' in H25.
    assert (x2 ∈ \[ a, b \]). apply AxiomII. applyAxiomII H25'.
    destruct H25'. lra. apply H29 in H32. lra.
  - rewrite <- H30 in H24. rewrite H30' in H24.
    assert (x1 ∈ \[ a, b \]). apply AxiomII. applyAxiomII H24'.
    destruct H24'. lra. apply H29 in H32. lra.
  - rewrite H30 in H31. lra.
Qed.



End A6_1.

Export A6_1.
