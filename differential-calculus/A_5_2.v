Require Export A_5_1.

Module A5_2.

(* 5.2 求导法则 *)

(* 5.2.1 导数的四则运算 *)
Fixpoint pow (r:R) (n:nat) : R :=
  match n with
    | O => 1
    | S n => Rmult r (pow r n)
  end.
Notation "r ^^ n" :=(pow r n) (at level 20).

Ltac QED_function := red; intros x21' y21' z21' Pq1 Pq2; applyAxiomII' Pq1;
  applyAxiomII' Pq2; rewrite Pq2; auto. 

Ltac Function_ass := apply f_x; [QED_function|apply AxiomII'; auto].


Lemma Lemma_pow1 : ∀ (x0 : R) (n k : nat), 
      x0 ^^ (n+k) = (x0 ^^ n) * (x0 ^^ k).
Proof.
  intros. generalize dependent n. induction k.
  - simpl. intros. rewrite Nat.add_0_r.
    rewrite Rmult_1_r. auto.
  - induction n. simpl. rewrite Rmult_1_l.
    auto. simpl. rewrite IHn. rewrite <- Rmult_assoc.
    simpl. auto.
Qed.


Lemma Lemma_pow2 : ∀ (x0 : R) (k : nat), x0 ^^ (2*k) = (x0 ^^ 2) ^^ k.
Proof.
  intros. induction k.
  - simpl. auto.
  - simpl. 
    rewrite Rmult_1_r. 
    simpl in IHk. rewrite Rmult_1_r in IHk.
    rewrite <- IHk. rewrite Nat.add_0_r.
    rewrite <- Nat.add_1_r.
    rewrite <- plus_assoc_reverse.
    assert(x0 ^^ (k + k + 1) = x0 ^^ (k + k) * x0 ^^ 1).
    { apply Lemma_pow1. }
    rewrite H. simpl. rewrite Rmult_1_r.
    rewrite <- Rmult_assoc. 
    rewrite <- Rmult_comm. 
    rewrite <- Rmult_assoc. auto.
Qed. 
    
Lemma Lemma_pow3: ∀ (x0 : R) (k : nat), x0 > 0 -> x0 ^^ k > 0.  
Proof.
  intros. induction k. simpl. lra.
  simpl. apply Rmult_gt_0_compat; auto.
Qed.

Lemma Lemma_pow4 : ∀ (x0 y0: R) (n : nat), 
      (x0 ^^ n) * (y0 ^^ n) = (x0 * y0) ^^ n.
Proof.
  intros. generalize dependent n. induction n.
  - simpl. lra. 
  - simpl. rewrite <- IHn. field. 
Qed.



(* 加法 *)
Theorem Theorem5_4_1 : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative \{\ λ x y, y = u[x] + v[x] \}\
    x0 (u '[x0] + v '[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1].
  apply derEqual in H0 as H2.
  apply derEqual in H1 as H3.
  rewrite H2; rewrite H3.
  clear H2 H3.
  assert (H3 : Function \{\ λ x y, y = u[x] + v[x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H0 as [H0 [[δ1' [H4 H5]] H6]].
  destruct H1 as [H1 [[δ2' [H7 H8]] H9]].
  generalize (Lemma1 δ1' δ2' H4 H7);
  intros [δ' [H10 [H11 H12]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] + v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H13 : Function \{\ λ x y, y =
      (\{\ λ x y, y = u[x] + v[x] \}\[x]
      - \{\ λ x y, y = u[x] + v[x] \}\[x0])
      / (x - x0) \}\).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists ((\{\ λ x y, y = u[x] + v[x] \}\[x]
      - \{\ λ x y, y = u[x] + v[x] \}\[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H14.
      destruct H6 as [H6 [δ3' [H15 [H16 H17]]]].
      destruct H9 as [H9 [δ4' [H18 [H19 H20]]]].
      assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22.
      destruct H22 as [δ2 [[H22 H26] H23]].
      apply H17 in H21 as [δ1 [[H24 H27] H25]].
      generalize (Lemma1' δ' δ1 δ2 H10 H24 H22).
      intros [δ [H28 [H29 [H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y =
        (\{\ λ x y, y = u[x] + v[x] \}\[x]
        - \{\ λ x y, y = u[x] + v[x] \}\[x0])
        / (x - x0) \}\[x] =
        (\{\ λ x y, y = u[x] + v[x] \}\[x]
        - \{\ λ x y, y = u[x] + v[x] \}\[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, \{\ λ x y,
        y = u[x] + v[x] \}\ [x1] = u[x1] + v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H33; auto.
      rewrite H33; auto.
      assert (H38 : 0 < Abs [x - x0] < δ1). lra.
      apply H25 in H38.
      assert (H39 : 0 < Abs [x - x0] < δ2). lra.
      apply H23 in H39.
      assert (H40 : \{\ λ x y, y =
        (u[x] - u[x0]) / (x - x0) \}\ [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : \{\ λ x y, y =
        (v[x] - v[x0]) / (x - x0) \}\ [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] + v[x] -
        (u[x0] + v[x0])) / (x - x0)
        - (y1 + y2) = ((u[x] - u[x0]) / (x - x0) - y1)
        + ((v[x] - v[x0]) / (x - x0) - y2)).
      { field. apply Lemma2 in H32.
        apply H32. }
      rewrite H40.
      generalize (Abs_plus_le ((u[x] - u[x0])
        / (x - x0) - y1) ((v[x] - v[x0])
        / (x - x0) - y2)). intro H41. lra.
Qed.

(*  减法  *)
Theorem Theorem5_4_2 : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative \{\ λ x y, y = u[x] - v[x] \}\
    x0 (u '[x0] - v '[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1].
  apply derEqual in H0 as H2.
  apply derEqual in H1 as H3.
  rewrite H2; rewrite H3.
  clear H2 H3.
  assert (H3 : Function \{\ λ x y, y = u[x] - v[x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H0 as [H0 [[δ1' [H4 H5]] H6]].
  destruct H1 as [H1 [[δ2' [H7 H8]] H9]].
  generalize (Lemma1 δ1' δ2' H4 H7);
  intros [δ' [H10 [H11 H12]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] - v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H13 : Function \{\ λ x y, y =
      (\{\ λ x y, y = u[x] - v[x] \}\[x]
      - \{\ λ x y, y = u[x] - v[x] \}\[x0])
      / (x - x0) \}\).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists ((\{\ λ x y, y = u[x] - v[x] \}\[x]
      - \{\ λ x y, y = u[x] - v[x] \}\[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H14.
      destruct H6 as [H6 [δ3' [H15 [H16 H17]]]].
      destruct H9 as [H9 [δ4' [H18 [H19 H20]]]].
      assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22.
      destruct H22 as [δ2 [[H22 H26] H23]].
      apply H17 in H21 as [δ1 [[H24 H27] H25]].
      generalize (Lemma1' δ' δ1 δ2 H10 H24 H22).
      intros [δ [H28 [H29 [H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : \{\ λ x y, y =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0) \}\[x] =
        (\{\ λ x y, y = u[x] - v[x] \}\[x]
        - \{\ λ x y, y = u[x] - v[x] \}\[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, \{\ λ x y,
        y = u[x] - v[x] \}\ [x1] = u[x1] - v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H33; auto.
      rewrite H33; auto.
      assert (H38 : 0 < Abs [x - x0] < δ1). lra.
      apply H25 in H38.
      assert (H39 : 0 < Abs [x - x0] < δ2). lra.
      apply H23 in H39.
      assert (H40 : \{\ λ x y, y =
        (u[x] - u[x0]) / (x - x0) \}\ [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : \{\ λ x y, y =
        (v[x] - v[x0]) / (x - x0) \}\ [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] - v[x] -
        (u[x0] - v[x0])) / (x - x0)
        - (y1 - y2) = ((u[x] - u[x0]) / (x - x0) - y1)
        - ((v[x] - v[x0]) / (x - x0) - y2)).
      { field. apply Lemma2 in H32.
        apply H32. }
      rewrite H40.
      generalize (Abs_minus_le ((u[x] - u[x0])
        / (x - x0) - y1) ((v[x] - v[x0])
        / (x - x0) - y2)). intro H41. lra.
Qed.


(* 导数的乘法 *)
Lemma Lemma_limit_0' : forall (v: Fun) (x0 :R), 
  derivable' v x0 ->
  derivable' \{\ λ h y,y = (v [x0 + h] ) \}\ 0. 
Proof.
  intros. unfold derivable' in H. destruct H as [y H]. unfold derivative' in H.
  destruct H as [H H1]. destruct H1 as [H1 H2].
  unfold derivable'. exists y. unfold derivative'. split.
  - unfold Function. intros. applyAxiomII H0. destruct H0 as [x1[y1[H4 H5]]].
    applyAxiomII H3. destruct H3 as [x2[y2[H3 H6]]].
    apply ProdEqual in H4. apply ProdEqual in H3.
    destruct H4 as [J1 J2]. destruct H3 as [J3 J4].
    rewrite <- J1 in H5. rewrite <- J3 in H6.
    rewrite <- J2 in H5. rewrite <- J4 in H6.
    rewrite H6, H5. auto.
  - split. exists 1. split. lra.
    intros x I1. apply AxiomII. exists (v [x0 + x]). apply AxiomII'. auto.
    assert (\{\ λ h0 y0, y0 = (\{\ λ h1 y1, y1 = v [x0 + h1] \}\ [0 + h0] - 
            \{\ λ h1 y1,y1 = v [x0 + h1] \}\ [0]) / h0 \}\
           = \{\ λ h0 y0, y0 = (v [x0 + h0] -v [x0])/ h0 \}\).
    { apply AxiomI. split; intros.
      - applyAxiomII H0. destruct H0 as [x'[y'[H0 H3]]].
        apply AxiomII. exists x',y'. split; auto. 
        assert (J1: \{\ λ h1 y1, y1 = v [x0 + h1] \}\ [0 + x']
                = v [x0 + x']).
        { apply f_x. unfold Function. intros. applyAxiomII H4. 
          destruct H4 as [x1[y1[H4 H6]]].
          applyAxiomII H5. destruct H5 as [x2[y2[H5 H7]]].
          apply ProdEqual in H4. apply ProdEqual in H5.
          destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7.
          rewrite <- J2 in H6. rewrite <- J4 in H7.
          rewrite H6, H7. auto. apply AxiomII'. 
          rewrite <- Rplus_assoc. rewrite Rplus_0_r. auto.
        }
        rewrite J1 in H3. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = v [x0 + h1] \}\ [0]
                = v [x0]).
        { apply f_x. unfold Function. intros. applyAxiomII H4. 
          destruct H4 as [x1[y1[H4 H6]]].
          applyAxiomII H5. destruct H5 as [x2[y2[H5 H7]]].
          apply ProdEqual in H4. apply ProdEqual in H5.
          destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7.
          rewrite <- J2 in H6. rewrite <- J4 in H7.
          rewrite H6, H7. auto. apply AxiomII'.
          rewrite Rplus_0_r. auto.
        }
        rewrite J1 in H3. clear J1.
        apply H3.
      - applyAxiomII H0. destruct H0 as [x'[y'[H0 H3]]].
        apply AxiomII. exists x', y'. split; auto.
        assert (J1: \{\ λ h1 y1, y1 = v [x0 + h1] \}\ [0 + x']
                = v [x0 + x']).
        { apply f_x. unfold Function. intros. applyAxiomII H4. 
          destruct H4 as [x1[y1[H4 H6]]].
          applyAxiomII H5. destruct H5 as [x2[y2[H5 H7]]].
          apply ProdEqual in H4. apply ProdEqual in H5.
          destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7.
          rewrite <- J2 in H6. rewrite <- J4 in H7.
          rewrite H6, H7. auto. apply AxiomII'. 
          rewrite <- Rplus_assoc. rewrite Rplus_0_r. auto.
        }
        rewrite J1. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = v [x0 + h1] \}\ [0]
                = v [x0]).
        { apply f_x. unfold Function. intros. applyAxiomII H4. 
          destruct H4 as [x1[y1[H4 H6]]].
          applyAxiomII H5. destruct H5 as [x2[y2[H5 H7]]].
          apply ProdEqual in H4. apply ProdEqual in H5.
          destruct H4 as [J1 J2]. destruct H5 as [J3 J4].
          rewrite <- J1 in H6. rewrite <- J3 in H7.
          rewrite <- J2 in H6. rewrite <- J4 in H7.
          rewrite H6, H7. auto. apply AxiomII'. 
          rewrite Rplus_0_r. auto.
        }
        rewrite J1. clear J1.
        apply H3.
    }
    rewrite H0. apply H2.
Qed.

Lemma Lemma_limit_0 : forall (v: Fun) (y x0 :R), 
  derivable' \{\ λ h y,y = (v [x0 + h] ) \}\ 0 -> 
  limit \{\ λ h y,y = (v [x0 + h] ) \}\ 0 (v [x0]).
Proof. 
  intros.
  assert (H0: derivable \{\ λ h y,y = (v [x0 + h] ) \}\ 0).
  { pose proof H as H'.
    unfold derivable' in H'. destruct H' as [y0 H'].
    unfold derivable. exists y0. rewrite <- Equaderivative in H'. apply H'. }
  apply Theorem5_1 in H0. unfold Continuous in H0.
  destruct H0 as [H0 H1].
  assert (H2:\{\ λ h y, y = v [x0 + h] \}\ [0]
             = v [x0]).
  { apply f_x.
    - unfold Function. intros. applyAxiomII H2. destruct H2 as [x1[y1[H2 H4]]].
      applyAxiomII H3. destruct H3 as [x2[y2[H3 H5]]].
      apply ProdEqual in H2. apply ProdEqual in H3.
      destruct H2 as [J1 J2]. destruct H3 as [J3 J4].
      rewrite <- J1 in H4. rewrite <- J3 in H5.
      rewrite <- J2 in H4. rewrite <- J4 in H5.
      rewrite H4, H5. auto.
    - apply AxiomII'. rewrite Rplus_0_r. auto.
   }
   rewrite H2 in H1. apply H1.
Qed. 

Theorem Theorem5_5 : ∀ (u v : Fun) (x0: R),
  derivable' u x0 -> derivable' v x0 ->
  derivative' \{\ λ x y, y = u[x] * v[x] \}\
    x0 (u '[x0] * v[x0] + v '[x0] * u[x0]).
Proof. 
  intros u v x0. intros [y1 H0]. intros [y2 H1]. pose proof H1 as M'. 
  apply derEqual' in H0 as H2.
  apply derEqual' in H1 as H3. 
  assert (H4 : Function \{\ λ x y, y = u[x] * v[x] \}\).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto.
  destruct H0 as [H0 [[δ1' [H5 H6]] H7]].
  destruct H1 as [H1 [[δ2' [H8 H9]] H10]].
  generalize (Lemma1 δ1' δ2' H5 H8);
  intros [δ' [H11 [H12 H13]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] * v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H14: forall x0 h0, \{\ λ x y0 ,y0 = u [x] * v [x] \}\ [x0 + h0]
            = u [x0 + h0] * v [x0 + h0] ).
    { intros. apply f_x; auto. apply AxiomII'. auto. }
    assert (H15: forall x0,\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]
            = u [x0] * v [x0] ).
    { intros. apply f_x; auto. apply AxiomII'. auto. }
    pose proof (H14 x0) as H14'. pose proof (H15 x0) as H15'. 
    assert (H16: ∃f, f = 
                 (\{\ λ h0 y,y =(\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0 + h0] -
                 \{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]) / h0 \}\ )).
    exists (\{\ λ h0 y,y =(\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0 + h0] -
                 \{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]) / h0 \}\ ). auto.
    destruct H16 as [f H16].
    assert (H17:∀h, f [h] =
            \{\ λ h0 y , y = (\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0 + h0] -
                 \{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]) / h0 \}\ [h]). 
    { rewrite H16; auto. }
    assert (H18: Function f).
    { unfold Function. rewrite H16. intros x y z H18 H19.
      applyAxiomII H18. applyAxiomII H19.
      destruct H18 as [x1 [y0[H18 H20]]].
      destruct H19 as [x2 [y0'[H19 H21]]].
      apply ProdEqual in H18. apply ProdEqual in H19.
      destruct H18 as [J1 J2]. destruct H19 as [J3 J4].
      rewrite <- J1 in H20. rewrite <- J3 in H21.
      rewrite <- J2 in H20. rewrite <- J4 in H21.
      rewrite H20, H21. auto. }
    assert (H19:∀h, [h, (
                (\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0 + h] -
                 \{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]) / h)] ∈ f).
    { intros. rewrite H16. apply AxiomII'. auto. }  
    
    rewrite <- H16.
    assert (H20: limit \{\ λ h y,y = (v [x0 + h] ) \}\ 0 (v [x0])).
    { assert (derivable' v x0).
      { unfold derivable'. exists y2. apply M'. } apply Lemma_limit_0' in H.
        apply Lemma_limit_0 in H; auto. } 
    assert (H21: \{\ λ h0 y,y = (\{\ λ x y0,y0 = u [x] * v [x] \}\ [x0 + h0] -
             \{\ λ x y0,y0 = u [x] * v [x] \}\ [x0]) / h0 \}\
            = \{\  λ h0 y,y = ( u [x0 + h0] * v [x0 + h0] - (u [x0] * v [x0])) / h0 \}\).
    { apply AxiomI. split; intros.
      - apply AxiomII. applyAxiomII H. destruct H as [h' [y [H H21]]].
        exists h', y. split;auto. rewrite H21. 
        pose proof (H14 x0 h'). pose proof (H15 x0). rewrite H22. rewrite H23.
        auto.
      - apply AxiomII. applyAxiomII H. destruct H as [h' [y [H H21]]].
        exists h', y. split;auto. rewrite H21. 
        pose proof (H14 x0 h'). pose proof (H15 x0). rewrite H22. rewrite H23.
        auto. }
    assert (K1: limit (\{\ λ h y,y = (u [x0 + h] - u [x0]) / h \}\ **
                      \{\ λ h y,y = v [x0 + h] \}\ ) 0 (y1 * v [x0]) ).
    { apply Theorem3_7_3; auto. }
    assert (H20': limit \{\ λ h y, y = u [x0] \}\ 0 u [x0]).
    { unfold limit. split.
      - QED_function.
      - exists 1. split. lra. split.
        + intros x I1. apply AxiomII. exists (u [x0]). apply AxiomII'. auto.
        + intros. exists (1/2). split. lra. intros.
          assert (\{\ λ h y ,y = u [x0] \}\ [x] = u [x0] ).
          { apply f_x. unfold Function. intros. applyAxiomII' H24.
          applyAxiomII' H23. 
          rewrite H24,H23. auto. apply AxiomII'. auto. }
          rewrite H23. 
          assert ((u [x0] - u [x0]) = 0). lra. rewrite H24. 
          rewrite Abs_ge; lra. }
    assert (K2: limit (\{\ λ h y,y = (v [x0 + h] - v [x0]) / h \}\ ** 
                       \{\ λ h y,y = u [x0] \}\) 0 (y2 * u [x0])).
    { apply Theorem3_7_3; auto. }
    rewrite H2. rewrite H3.
    assert (L1: ∃g, g = \{\ λ h y,y = (u [x0 + h] - u [x0]) / h \}\).
    { exists (\{\ λ h y,y = (u [x0 + h] - u [x0]) / h \}\). auto. }
    destruct L1 as [g L1].
    assert (L1': Function g).
    {  rewrite L1. QED_function. }
    assert (L2: ∃h, h = \{\ λ h y,y = v [x0 + h] \}\).
    { exists (\{\ λ h y,y = v [x0 + h] \}\). auto. }
    destruct L2 as [g' L2].
    assert (L2': Function g').
    { rewrite L2. QED_function.  }
    rewrite <- L1 in K1. rewrite <- L2 in K1.
    assert (L3: ∃l, l = \{\ λ h y,y = (v [x0 + h] - v [x0]) / h \}\).
    { exists (\{\ λ h y,y = (v [x0 + h] - v [x0]) / h \}\). auto. }
    destruct L3 as [l L3].
    assert (L3': Function l).
    { rewrite L3. QED_function. }
    assert (L4: ∃l, l = \{\ λ h y : R,y = u [x0] \}\).
    { exists (\{\ λ h y : R,y = u [x0] \}\). auto. }
    destruct L4 as [l' L4].
    assert (L4': Function l').
    { rewrite L4. QED_function. }
    rewrite <- L3 in K2. rewrite <- L4 in K2.   
    assert (K3: limit (g ** g' \+ l ** l') 0 (y1 * v [x0] + y2 * u [x0])).
    { apply Theorem3_7_1; auto. }
    assert (f = (g ** g' \+ l ** l')). 
    { unfold plus_fun.
      assert (K4: ∃G, G = \{\ λ h y,y = (u [x0 + h] - u [x0]) / h *
                                          v [x0 + h]\}\).
      { exists (\{\ λ h y,y = (u [x0 + h] - u [x0]) / h * v [x0 + h] \}\).
        auto. }
      destruct K4 as [G K4].
      assert (K4': Function G).
      { rewrite K4. QED_function. }
      assert (K5: ∃L, L = \{\ λ h y,y = (v [x0 + h] - v [x0]) / h * u [x0] \}\).
      { exists (\{\ λ h y,y = (v [x0 + h] - v [x0]) / h * u [x0] \}\). auto. }
      destruct K5 as [L K5].
      assert (K5': Function L).
      { rewrite K5. QED_function. }
      assert (LK1: G = g ** g').
      { rewrite K4,L1,L2. unfold mult_fun. apply AxiomI. split;intros.
        - apply AxiomII. apply -> AxiomII in H. destruct H as [x [y [H H']]].
          exists x, y. split; auto. split.
          + apply AxiomII. exists ((u [x0 + x] - u [x0]) / x ). apply AxiomII'.
            auto.
          + split. apply AxiomII. exists (v [x0 + x]). apply AxiomII'. auto.
            assert (Z1: \{\ λ h0 y0,y0 = (u [x0 + h0] - u [x0]) / h0 \}\ [x]
                        = (u [x0 + x] - u [x0]) / x).
            { Function_ass. }
            assert (Z2: \{\ λ h0 y0,y0 = v [x0 + h0] \}\ [x] = (v [x0 + x])).
            { Function_ass. }
            rewrite Z1, Z2. apply H'.
        - apply -> AxiomII in H. destruct H as [x [y [H H']]].
          destruct H' as [H' [H'' H''']]. 
          assert (Z1: \{\ λ h0 y0,y0 = (u [x0 + h0] - u [x0]) / h0 \}\ [x]
                        = (u [x0 + x] - u [x0]) / x).
            { Function_ass. }
            
            assert (Z2: \{\ λ h0 y0,y0 = v [x0 + h0] \}\ [x] = (v [x0 + x])).
            { Function_ass. }
          rewrite Z1 in H'''. rewrite Z2 in H'''. apply AxiomII.
          exists x, y. split; auto. }
      assert (LK2: L = l ** l').
      { rewrite K5,L3,L4. unfold mult_fun. apply AxiomI. split;intros.
        - apply AxiomII. apply -> AxiomII in H. destruct H as [x [y [H H']]].
          exists x, y. split; auto. split.
          + apply AxiomII. exists ((v [x0 + x] - v [x0]) / x ). apply AxiomII'.
            auto.
          + split. apply AxiomII. exists (u [x0]). apply AxiomII'. auto.
            assert (Z1: \{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 \}\ [x]
                        = (v [x0 + x] - v [x0]) / x).
            { Function_ass. }
            
            assert (Z2: \{\ λ h0 y0,y0 = u [x0] \}\ [x] = (u [x0])).
            { Function_ass. }
            rewrite Z1, Z2. apply H'.
        - apply -> AxiomII in H. destruct H as [x [y [H H']]].
          destruct H' as [H' [H'' H''']]. 
          assert (Z1: \{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 \}\ [x]
                        = (v [x0 + x] - v [x0]) / x).
            { Function_ass. }
            assert (Z2: \{\ λ h0 y0,y0 = u [x0] \}\ [x] = (u [x0])).
            { Function_ass. }
          rewrite Z1 in H'''. rewrite Z2 in H'''. apply AxiomII.
          exists x, y. split; auto. }
        rewrite <- LK1. rewrite <- LK2.
        rewrite H16.    
    apply AxiomI. split; intros.
    - apply AxiomII. apply -> AxiomII in H. destruct H as [x [y [H H']]].
      exists x, y. split; auto. split.
      + rewrite K4. apply AxiomII. exists ( (u [x0 + x] - u [x0]) / x * v [x0 + x]).
        apply AxiomII'. auto.
      + split. rewrite K5. apply AxiomII. exists ((v [x0 + x] - v [x0]) / x * u [x0]).
        apply AxiomII'. auto.
        rewrite K4, K5.
        assert (\{\ λ h0 y0,y0 = (u [x0 + h0] - u [x0]) / h0 * v [x0 + h0] \}\ [x]
               = (u [x0 + x] - u [x0]) / x * v [x0 + x]).
        { Function_ass. }
        assert (\{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 * u [x0] \}\ [x]
               = (v [x0 + x] - v [x0]) / x * u [x0]).
        { Function_ass. }
        rewrite H23, H22.
        rewrite H'. rewrite H14'. rewrite H15. lra.
    - apply -> AxiomII in H. destruct H as [x [y [H H']]]. 
      destruct H' as [H' [H'' H''']].
      apply AxiomII. exists x, y. split; auto. rewrite K4, K5 in H'''.
      assert (\{\ λ h0 y0,y0 = (u [x0 + h0] - u [x0]) / h0 * v [x0 + h0] \}\ [x]
               = (u [x0 + x] - u [x0]) / x * v [x0 + x]). 
        { apply f_x. rewrite <- K4. apply K4'.
          apply AxiomII'. auto. } 
        assert (\{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 * u [x0] \}\ [x]
               = (v [x0 + x] - v [x0]) / x * u [x0]).
        { apply f_x. rewrite <- K5. apply K5'.
          apply AxiomII'. auto. } 
      rewrite H23 in H'''. rewrite H'''.
      assert(\{\ λ h y0,y0 = (u [x0 + h] - u [x0]) / h * v [x0 + h] \}\ [x] = (u [x0 + x] - u [x0]) / x * v [x0 + x]).
      { Function_ass. } rewrite H24. rewrite H14'.
      rewrite H15. lra. }
    rewrite H. apply K3.
Qed.

Theorem Theorem5_5'' : ∀ (u v : Fun) (x0: R),
  derivable u x0 -> derivable v x0 ->
  derivative \{\ λ x y, y = u[x] * v[x] \}\
    x0 (u '[x0] * v[x0] + v '[x0] * u[x0]).
Proof.
  intros.
  unfold derivable in *.
  destruct H as [y'].
  destruct H0 as [y0'].
  apply Equaderivative in H.
  apply Equaderivative in H0. 
  apply Equaderivative. 
  apply Theorem5_5;
  red; [exists y'|exists y0']; auto.
Qed.

Lemma Lemma5_1 : ∀ (u : Fun) (c : R),
  Function \{\ λ x y, y = c * u[x] \}\.
Proof.
  intros. QED_function.
Qed.

Lemma Lemma5_2 : ∀ (u : Fun) (c x0 : R),
  \{\ λ x y, y = c * u[x] \}\[x0] = c * u[x0].
Proof.
  intros. Function_ass.
Qed.

Lemma Lemma5_3 : ∀ (u : Fun) (c x0 : R),
  derivable u x0 -> derivative \{\ λ x y, y = c * u[x] \}\
    x0 (c * u '[x0]).
Proof.
  intros u c x0 [y H0]. apply derEqual in H0 as H1.
  rewrite H1. clear H1.
  split; try apply Lemma5_1. unfold derivative in H0.
  destruct H0 as [H0 [[δ' [H1 H2]] H3]]. split.
  - exists δ'. split; auto. intros x I1.
    apply AxiomII. exists (c*u[x]).
    apply AxiomII'. reflexivity.
  - assert (H4 : Function \{\ λ x y0, y0 =
            (\{\ λ x1 y1, y1 = c * u[x1] \}\[x] -
             \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])
             / (x - x0) \}\ ).
    { intros x1 y1 z1 I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; assumption. }
    split; auto. exists δ'.
    split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists ((\{\ λ x1 y1, y1 = c * u[x1] \}\[x] -
            \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])
             / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H5. unfold limit in H3.
      destruct H3 as [H3 [δ1' [H6 [H7 H8]]]].
      assert (H16 : ∀ x, \{\ λ x y0, y0 =
        (\{\ λ x1 y1, y1 = c * u[x1] \}\[x] -
         \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])
         / (x - x0) \}\[x] =
         (\{\ λ x1 y1, y1 = c * u[x1] \}\[x] -
         \{\ λ x1 y1, y1 = c * u[x1] \}\ [x0])
         / (x - x0)).
      { intros x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      destruct classic with (P := c = 0) as [J0 | J0].
      * exists (δ'/2). split; [lra | intros x H9].
        rewrite H16. rewrite Lemma5_2. rewrite Lemma5_2.
        rewrite J0 in *.
        apply Lemma2 in H9. apply Abs_R.
        assert (I1 : (0 * u [x] - 0 * u [x0])
          / (x - x0) - 0 * y = 0).
        { field. apply H9. }
        rewrite I1. lra.
      * assert (J1 : Abs[c] > 0).
        { apply Abs_not_eq_0. assumption. }
        assert (J2 : ε/Abs[c] > 0).
        { apply Rdiv_lt_0_compat; assumption. }
        apply H8 in J2 as H9.
        destruct H9 as [δ1 [[H9 H10] H11]].
        generalize (Lemma1 δ' δ1 H1 H9).
        intros [δ [H12 [H13 H14]]].
        exists δ. split; [lra | intros x H15].
        rewrite H16. clear H16.
        rewrite Lemma5_2. rewrite Lemma5_2.
        assert (H16 : 0 < Abs [x - x0] < δ1). lra.
        apply H11 in H16.
        assert (H17 : \{\ λ x y, y = (u[x] - u[x0])
          / (x - x0) \}\ [x] = (u[x] - u[x0])
          / (x - x0)).
        { apply f_x; auto. apply AxiomII'.
          reflexivity. }
        rewrite H17 in H16.
        apply Lemma2 in H15.
        assert (H18 : (c * u[x] - c * u[x0]) / (x - x0)
          - c * y = c * ((u [x] - u [x0]) / (x - x0) - y)).
        { field. apply H15. }
        rewrite H18. rewrite Abs_mult.
        apply Rmult_lt_compat_l with (r := Abs[c]) in H16;
        auto. assert (H19 : Abs [c] * (ε / Abs [c]) = ε).
        { field. lra. }
        rewrite H19 in H16. assumption.
Qed.


Lemma Lemma5_6_1 : forall (v: Fun) (x0 :R),
derivable' v x0 -> derivable' \{\ λ h y,y = (v [x0 + h] * v[x0] ) \}\ 0. 
Proof.  
  intros. unfold derivable' in H. destruct H as [y H]. unfold derivative' in H.
  destruct H as [H H1]. destruct H1 as [H1 H2].
  unfold derivable'. exists (y * v [x0]). unfold derivative'. split.
  - unfold Function. intros. applyAxiomII H0. destruct H0 as [x1[y1[H4 H5]]].
    applyAxiomII H3. destruct H3 as [x2[y2[H3 H6]]].
    apply ProdEqual in H4. apply ProdEqual in H3.
    destruct H4 as [J1 J2]. destruct H3 as [J3 J4].
    rewrite <- J1 in H5. rewrite <- J3 in H6.
    rewrite <- J2 in H5. rewrite <- J4 in H6.
    rewrite H6, H5. auto.
  - split. exists 1. split. lra.
    intros x I1. apply AxiomII. exists (v [x0 + x] * v [x0]). apply AxiomII'. auto.
    assert (\{\ λ h0 y0, y0 = (\{\ λ h1 y1, y1 = v [x0 + h1] * v [x0] \}\ 
    [0 + h0] -  \{\ λ h1 y1,y1 = v [x0 + h1] * v [x0] \}\ [0]) / h0 \}\
    = \{\ λ h0 y0, y0 = (v [x0 + h0] * v [x0] -v [x0] * v [x0])/ h0 \}\).
    { apply AxiomI. split; intros.
      - applyAxiomII H0. destruct H0 as [x'[y'[H0 H3]]].
        apply AxiomII. exists x',y'. split; auto. 
        assert (J1: \{\ λ h1 y1, y1 = v [x0 + h1] * v [x0] \}\ [0 + x']
                = v [x0 + x'] * v [x0]).
        { Function_ass. replace (0 + x') with x'; auto. lra. }
        rewrite J1 in H3. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = v [x0 + h1] * v [x0]\}\ [0]
                = v [x0] * v [x0]).
        { Function_ass. replace (x0 + 0) with x0; auto. lra. }
        rewrite J1 in H3. clear J1.
        apply H3.
      - applyAxiomII H0. destruct H0 as [x'[y'[H0 H3]]].
        apply AxiomII. exists x', y'. split; auto.
        assert (J1: \{\ λ h1 y1, y1 = v [x0 + h1] * v [x0] \}\ [0 + x']
                = v [x0 + x'] * v [x0]).
        { Function_ass. replace (0 + x') with x'; auto. lra. }
        rewrite J1. clear J1.
        assert (J1: \{\ λ h1 y1,y1 = v [x0 + h1] * v [x0]\}\ [0]
                = v [x0] * v [x0]).
        { Function_ass. replace (x0 + 0) with x0; auto. lra. }
        rewrite J1. clear J1.
        apply H3. }
    rewrite H0.  
    assert (\{\ λ h0 y0, y0 = (v [x0 + h0] * v [x0] - v [x0] * v [x0]) / h0 \}\
            = \{\ λ h0 y0, y0 = (v [x0 + h0] - v [x0] ) / h0 \}\ ** 
              \{\ λ h0 y0, y0 = v [x0]  \}\).
    { apply AxiomI. split; intros.
      - applyAxiomII H3. destruct H3 as [x' [y' [H3 H4]]].
        apply AxiomII. exists x',y'. split; auto. split. apply AxiomII.
        exists ((v [x0 + x'] - v [x0]) / x'). apply AxiomII'. auto.
        split. apply AxiomII. exists (v [x0]). apply AxiomII'. auto.
        assert (\{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 \}\ [x']
                = ((v [x0 + x'] - v [x0]) / x')).
        { Function_ass. }
        rewrite H5. clear H5.
        assert (\{\ λ h0 y0, y0 = v [x0] \}\ [x'] = v [x0]).
        { Function_ass. } 
        rewrite H5. clear H5.  rewrite Rmult_comm. 
        assert (((v [x0 + x'] - v [x0]) / x') = ((v [x0 + x'] - v [x0]) * / x')).
        lra. rewrite H5.  rewrite <- Rmult_assoc.
        assert (v [x0] * (v [x0 + x'] - v [x0]) = 
        v [x0] * v [x0 + x'] - v [x0] * v [x0] ).
        rewrite Rmult_minus_distr_l. auto.
        rewrite H6. rewrite H4. lra.
      - applyAxiomII H3. destruct H3 as [x'[y'[H3 [H4 [H5 H6]]]]].
        apply AxiomII. exists x', y'. split; auto. 
        assert (\{\ λ h0 y0,y0 = (v [x0 + h0] - v [x0]) / h0 \}\ [x']
                = ((v [x0 + x'] - v [x0]) / x')).
        { Function_ass. }  
        rewrite H7 in H6. clear H7.
        assert (\{\ λ h0 y0, y0 = v [x0] \}\ [x'] = v [x0]).
        { Function_ass. }
        rewrite H7 in H6. clear H7. rewrite Rmult_comm in H6. 
        assert (((v [x0 + x'] - v [x0]) / x') = ((v [x0 + x'] - v [x0]) * / x')).
        lra. rewrite H7 in H6. rewrite <- Rmult_assoc in H6.
        assert (v [x0] * (v [x0 + x'] - v [x0]) = 
        v [x0] * v [x0 + x'] - v [x0] * v [x0] ).
        rewrite Rmult_minus_distr_l. auto.
        rewrite H8 in H6. rewrite H6. lra. }
    rewrite H3.
    apply Theorem3_7_3; auto.
    unfold limit. split.
    unfold Function. intros. applyAxiomII H4. 
    destruct H4 as [x1[y1[H4 H6]]].
    applyAxiomII H5. destruct H5 as [x2[y2[H5 H7]]].
    apply ProdEqual in H4. apply ProdEqual in H5.
    destruct H4 as [J1 J2]. destruct H5 as [J3 J4]. 
    rewrite <- J2 in H6. rewrite <- J4 in H7.
    rewrite H6, H7. auto.
    exists 1. split. lra. split.
    intros x I1. apply AxiomII. exists (v [x0]). apply AxiomII'. auto.
    intros. exists (1/2). split. lra. intros.
    assert (\{\ λ h0 y0, y0 = v [x0] \}\ [x] = v [x0]).
    { Function_ass. } 
    rewrite H6.  
    rewrite Rminus_diag_eq. rewrite Abs_ge;
    auto; lra. auto.
Qed.


Lemma Lemma5_6'' : forall (v: Fun) (x0 :R),
derivable' \{\ λ h y,y = (v [x0 + h] * v[x0] ) \}\ 0 -> v[x0] <> 0 -> 
limit \{\ λ h y, y = v[x0 + h] * v[x0]\}\ 0 (v[x0] * v[x0]).
Proof.
  intros v x0 H K. 
  assert (H0: derivable \{\ λ h y,y = (v [x0 + h] * v[x0] ) \}\ 0).
  { pose proof H as H'.
    unfold derivable' in H'. destruct H' as [y0 H'].
    unfold derivable. exists y0.
    rewrite <- Equaderivative in H'. apply H'. }
  apply Theorem5_1 in H0. unfold Continuous in H0.
  destruct H0 as [H0 H1].
  assert (H2: \{\ λ h y, y = v [x0 + h] * v [x0] \}\ [0]
             = v [x0] * v [x0] ).
  { Function_ass. replace (x0 + 0) with x0; auto. lra. }
   rewrite H2 in H1. apply H1.
Qed.


Lemma Lemma5_6': forall (f : Fun) (x0:R),
    Continuous f x0 -> f [x0] <> 0 ->
    ∃ ε, ε > 0 /\ (forall h:R, Abs [h] < ε -> f [x0 + h] <> 0).
Proof.
  intros. unfold Continuous in H.
  destruct H. apply Rdichotomy in H0 as I1.
  destruct I1 as [I1 | I1].
  - generalize (Theorem3_4_2 f x0 f[x0] H1 I1).
    intro I2. assert (I3 : 0 < -f[x0]/2 < -f[x0]). lra.
    apply I2 in I3 as I4. 
    destruct I4 as [δ [I4 I5]].
    exists δ. split; auto. intros x I6.
    pose proof (Abs_Rge0 x). destruct H2.
    assert ((x0 + x) ∈ Neighbor0 x0 δ).
    { apply AxiomII. replace (x0 + x - x0) with x. 
       split; auto. lra. }
    apply I5 in H3. lra. 
    assert ( x = 0).
    { destruct (tf (x = 0)). auto.  
      apply Abs_not_eq_0 in n. exfalso.
      rewrite H2 in n. apply Rgt_irrefl in n; auto. }
    rewrite H3. rewrite Rplus_0_r. auto.
  - generalize (Theorem3_4_1 f x0 f[x0] H1 I1).
    intro I2. assert (I3 : 0 < f[x0]/2 < f[x0]). lra.
    apply I2 in I3 as I4. 
    destruct I4 as [δ [I4 I5]].
    exists δ. split; auto. intros x I6.
    pose proof (Abs_Rge0 x). destruct H2.
    assert ((x0 + x) ∈ Neighbor0 x0 δ).
    { apply AxiomII. replace (x0 + x - x0) with x. 
       split; auto. lra. }
    apply I5 in H3. lra. 
    assert ( x = 0).
    { destruct (tf (x = 0)). auto.  
      apply Abs_not_eq_0 in n. exfalso.
      rewrite H2 in n. apply Rgt_irrefl in n; auto. }
    rewrite H3. rewrite Rplus_0_r. auto.
Qed.

(* 导数的除法 *)
Lemma Lemma5_6 : ∀ (u : Fun) (x0 : R), u [x0] <> 0 -> derivable u x0 ->
derivative \{\ λ x y, y = 1 / u[x] \}\ x0 (- (u '[x0] / (u [x0] * u [x0]))).
Proof.
  intros u x0 H [y' H0].
  apply (Equaderivative u x0 y') in H0 as J1.
  assert ( J2: derivable' u x0).
  { unfold derivable'. exists y'; auto. }
  apply Lemma5_6_1 in J2.
  apply Lemma5_6'' in J2 as J2; auto. clear J1.
  apply derEqual in H0 as H1.
  assert (K3 : derivable u x0).
  { unfold derivable. exists y'; auto. }
  apply Theorem5_1 in K3 as K4.
  apply Lemma5_6' in K4; auto.
  apply Equaderivative.
  assert (J1: ∃ f, f = \{\ λ h y,y = u [x0 + h] * u [x0] \}\).
  { exists \{\ λ h y,y = u [x0 + h] * u [x0] \}\; auto. }
  destruct J1 as [f J1]. rewrite <- J1 in J2.
  apply (Theorem3_7_4' f 0 (u [x0] * u [x0])) in J2.
  apply (Equaderivative u x0 y') in H0.
  unfold derivative'. 
  unfold derivative' in H0. 
  assert (K1: Function \{\ λ x y,y = 1 / u [x] \}\) .
  { QED_function. }
  destruct H0 as [H0[H4 H5]]. 
  destruct H4 as [δ'' [H4 H7]].
  split; auto. split. 
  - exists δ''. split; auto. intros z H8. 
    apply H7 in H8. apply AxiomII. exists (1 / u[z]). 
    apply AxiomII'; auto. 
  - assert (K2: forall z, \{\ λ x y,y = 1 / u [x] \}\ [z] = 1 / u[z]).
    { intros. Function_ass. }
    rewrite K2. 
    assert (K5 :\{\ λ h y,y = (\{\ λ x y0,y0 = 1 / u [x] \}\ [x0 + h] - 1 / u [x0]) / h \}\ = \{\ λ h y,y = ( 1 / u [x0 + h] - 1 / u [x0]) / h \}\ ).
  { apply AxiomI. split; intros; try (apply AxiomII; applyAxiomII H2;
      destruct H2 as [x[y [H6 H8]]] ).
    - rewrite K2 in H8. exists x, y. split; auto.
    - exists x, y. split; auto. rewrite K2. auto. }
    rewrite K5. clear K5.
    assert (K7 : Function \{\ λ h y,y = (1 / u [x0 + h] - 1 / u [x0]) / h \}\).
  { QED_function. } split; auto.
   unfold limit in J2. unfold limit in H5.
   destruct H5. destruct J2.
   destruct H3 as [δ1'[H10 [H8 H9]]].
   destruct H6 as [δ2'[H11 [H12 H13]]].
   assert (H14 : (∃ δ3', δ3' >0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (Neighbor0 0 δ3') -> Abs[(1 /// f) [x]] <= M)))).
   { apply Theorem3_3'. exists (/ (u [x0] * u [x0])). split; auto. exists δ2'.
    repeat split; auto. } 
    destruct H14 as [δ3'[K5 K6]].
    assert (K8 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2' /\ δ' <= δ3').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1].
    - destruct (Rlt_or_le δ1' δ3') as [I2 | I2];
        [exists (δ1'/2) | exists (δ3'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2' δ3') as [I2 | I2];
        [exists (δ2'/2) | exists (δ3'/2)]; repeat split; lra. }
  destruct K8 as [δ' [K8 [K9 [K10 K11]]]].
  exists δ'. split; auto. split.
  + intros z H15. apply AxiomII. exists ((1 / u [x0 + z] - 1 / u [x0]) / z).
    apply AxiomII'; auto.
  + destruct K6 as [M [K6 K12]].
    generalize (Abs_Rge0 y'). intro H14.
    intros ε H15.
    assert (H16: ε / (M+Abs[y']) > 0).
  { apply  Rmult_gt_0_compat; auto.
    apply Rinv_0_lt_compat. lra. }
    apply H13 in H16 as H17. apply H9 in H16 as H18.
    destruct H17 as [δ1 [H19 H20]].
    destruct H18 as [δ2 [H21 H22]].
    destruct K4 as [δ3 [K4 K13]].
    assert (H23 : ∃ δ, δ > 0 /\ δ <= δ1 /\ δ <= δ2 /\ δ < δ' /\ δ < δ3 ).
    { destruct (Rlt_or_le δ1 δ2). 
      - destruct (Rlt_or_le δ1 δ').
        + destruct (Rlt_or_le δ1 δ3);
          [ exists (δ1 / 2) | exists (δ3 / 2)]; repeat split; lra.
        + destruct (Rlt_or_le δ' δ3);
          [ exists (δ' / 2)| exists (δ3 / 2)]; repeat split; lra.
      - destruct (Rlt_or_le δ2 δ') as [L1 | L1].
        + destruct (Rlt_or_le δ3 δ2) as [L2|L2];
          [ exists (δ3 / 2) | exists (δ2 / 2)]; repeat split; lra.
        + destruct (Rlt_or_le δ' δ3) as [L2|L2];
          [ exists (δ' / 2) | exists (δ3 / 2)]; repeat split; lra. }
   destruct H23 as [δ [H23 [H24 [H25 [H26 H27]]]]].
   exists δ. split; auto. intros x H28. 
   rewrite Rminus_0_r in H28. destruct H28. 
   assert (Abs [x] < δ3). lra. apply K13 in H17.
   assert (0 < Abs [x - 0] < δ1). rewrite Rminus_0_r. lra.
   assert (0 < Abs [x - 0] < δ2). rewrite Rminus_0_r. lra.
   assert (\{\ λ h y,y = (1 / u [x0 + h] - 1 / u [x0]) / h \}\ [x] = 
      (1 / u [x0 + x] - 1 / u [x0]) / x ).
   { apply f_x; auto. apply AxiomII'; auto. }
   assert (J2 : f [x] = u [x0 + x] * u [x0]).
   { rewrite J1. Function_ass. }
   assert ((1 /// f) [x] = / (u [x0 + x] * u [x0])).
   { apply f_x; auto.  apply AxiomII'. repeat split.
     - apply AxiomII. exists (u [x0 + x] * u [x0]).
       rewrite J1. apply AxiomII'. auto.
     - rewrite J2. 
       apply Rmult_integral_contrapositive; split; auto.
     - rewrite J2; lra. }
    assert (\{\ λ h y,y = (1 / u [x0 + h] - 1 / u [x0]) / h \}\ [x] = 
     (1 / u [x0 + x] - 1 / u [x0]) / x ).
     { apply f_x; auto. apply AxiomII'; auto. }
    rewrite H31. 
   assert (J3 : (1 / u [x0 + x] - 1 / u [x0]) / x = (- (u[x0 + x] - u[x0]) / x ) / (u [x0 + x] * u [x0])).
  { intros. unfold Rdiv. 
    rewrite Rmult_assoc. rewrite (Rmult_comm (/ x)).
    rewrite <- Rmult_assoc. 
    apply Rmult_eq_compat_r. 
    apply (Rmult_eq_reg_r u [x0]); auto.
    rewrite (Rinv_mult_distr u [x0 + x]); auto.
    rewrite Rmult_assoc. 
    replace (/ u [x0 + x] * / u [x0] * u [x0]) with (/ u [x0 + x]).
    unfold Rminus.  rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l. rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rmult_plus_distr_r. 
    assert (- u [x0 + x] * / u [x0 + x] = -1).
    { rewrite Ropp_mult_distr_l_reverse.
      rewrite Rinv_r; auto.  }
    rewrite H32. 
    assert (- (1 * / u [x0]) * u [x0] = -1).
    { rewrite Ropp_mult_distr_l_reverse. rewrite Rmult_1_l.
      rewrite Rinv_l; auto. }
    rewrite H33. lra. rewrite Rmult_assoc. 
    rewrite Rinv_l; auto. lra. }
  rewrite J3. clear H13. clear H9.
  assert (J4 : ∃ u' , u' = \{\ λ h y,y = (u [x0 + h] - u [x0]) / h \}\).
  { exists \{\ λ h y,y = (u [x0 + h] - u [x0]) / h \}\; auto. }
  destruct J4 as [u']. rewrite <- H9 in H2.
  assert (J4 : u' [x] = (u [x0 + x] - u [x0]) / x).
  { apply f_x; auto. rewrite H9. apply AxiomII'; auto. }
  assert (J5 : - (u [x0 + x] - u [x0]) / x / (u[x0 + x] * u [x0]) = - u'[x] * ((1 /// f) [x])).
  { rewrite H30. rewrite J4. unfold Rdiv. lra. }
  rewrite J5. 
  assert (- u' [x] * (1 /// f) [x] - - (u '[ x0] / (u [x0] * u [x0])) = 
  - (u' [x] * (1 /// f) [x] - (u '[ x0] / (u [x0] * u [x0])))).
  { lra. }
  rewrite H13. rewrite <- Abs_eq_neg. clear H13.
  clear H31. rewrite H1. 
  apply H22 in H28 as H13. apply H20 in H18 as H31.
  clear H22. clear H20.
  rewrite <- H9 in H13.
  assert (∃ B, B = / (u [x0] * u [x0])).
  { exists (/ (u [x0] * u [x0])); auto.  }
  destruct H20 as [B]. rewrite <- H20 in H31.
  unfold Rdiv. rewrite <- H20.
  assert (u' [x] * (1 /// f) [x] - y' * B =
    (u' [x]-y') * (1 /// f) [x] + y' *((1 /// f) [x]-B )). field.
  rewrite H22. 
  generalize (Abs_plus_le ((u'[x]-y')*(1 /// f) [x]) (y' *((1 /// f) [x]-B))).
  intro H36. generalize (Abs_mult (u'[x] - y') ((1 /// f) [x])).
  intro H37. generalize (Abs_mult (y') ((1 /// f) [x]- B)).
  intro H38. rewrite H37 in H36. rewrite H38 in H36.
  apply Rle_lt_trans with (r2 := Abs[u' [x]- y']*Abs[(1 /// f) [x]] +
    Abs[y']*Abs[(1 /// f) [x]-B]); auto.
  assert (H39 : Abs[(1 /// f) [x]] <= M).
  { apply K12. apply AxiomII. rewrite Rminus_0_r;  lra. }
  assert (H40 : ε = (ε/(M + Abs[y'])) * M + Abs[y']*(ε/(M + Abs[y']))).
  field; lra. rewrite H40. apply Rplus_lt_le_compat.
  * destruct H39 as [H39 | H39].
   ** apply Rmult_le_0_lt_compat; auto;
      apply Rge_le; apply Abs_Rge0.
   ** rewrite H39. apply Rmult_lt_compat_r; auto.
   * apply Rmult_le_compat_l; lra.
 - apply Rmult_integral_contrapositive; auto.
Qed.
   

(* 导数的除法  *)
Theorem Theorem5_6 : ∀ (u v : Fun) (x0: R),
derivable u x0 -> derivable v x0 -> v[x0] <> 0 ->
derivative \{\ λ x y, y = u[x] / v[x] \}\
    x0 ((u '[x0] * v[x0] - u[x0] * v '[x0]) / (v [x0] * v [x0]) ).
Proof.
  intros u v x0 H H0 H2. apply Lemma5_6 in H0 as H1; auto.
  pose proof H as [u' J2].
  apply (Equaderivative u x0 u') in J2 as J1.
  pose proof H0 as [v' J3].
  apply (Equaderivative v x0 v') in J3 as J4.
  unfold Rdiv.
  assert (∃ g, g = \{\ λ x y,y = 1 / v [x] \}\).
  { exists \{\ λ x y,y = 1 / v [x] \}\; auto.  }
  destruct H3 as [g]. rewrite <- H3 in H1.
  apply Equaderivative.
  assert (Function g).
  { rewrite H3. QED_function. }
  assert (forall x, g [x] = / v [x]).
  { intros. apply f_x; auto. rewrite H3.
    apply AxiomII'; auto. lra. }
  assert (\{\ λ x y,y = u [x] * / v [x] \}\ = \{\ λ x y,y = u [x] * g[x] \}\).
  { apply AxiomI. split; intros.
    - applyAxiomII H6. apply AxiomII.
      destruct H6 as [x[y [H6 H7]]]. 
      exists x, y. split; auto. rewrite H5; auto.
    - applyAxiomII H6. apply AxiomII.
      destruct H6 as [x[y [H6 H7]]].
      exists x, y. split; auto. rewrite H5 in H7; auto.  }
   rewrite H6. apply derEqual in H1 as H7.
   apply derEqual in J2 as H8.
   assert (u '[x0] * g [x0] + u[x0] * g '[x0] = (u '[ x0] * v [x0] - u [x0] * v '[ x0]) * / (v [x0] * v [x0])).
   { unfold Rminus.
    rewrite Rmult_plus_distr_r.   
    rewrite Rmult_assoc. 
    replace (v [x0] * / (v [x0] * v [x0])) with (/ v [x0]).
    rewrite H5. 
    apply Rplus_eq_compat_l. rewrite H7. lra.
    replace (/ (v [x0] * v [x0])) with (/ v[x0] * / v[x0]).
    rewrite <- Rmult_assoc. rewrite Rinv_r; auto; lra.
    rewrite Rinv_mult_distr; auto;lra. }
    rewrite <- H9. assert (u[x0] * g '[x0] = g '[x0] * u [x0]).
    lra. rewrite H10.
    apply (Theorem5_5 u g); unfold derivable'.
    exists u';auto. exists (- (v '[ x0] / (v [x0] * v [x0]))).
    apply Equaderivative; auto.
Qed.
 




Theorem Lemma5_7' : ∀ (f g: Fun) (x0 δ : R), Inverse_Function f g ->  δ > 0 ->
 (Neighbor x0 δ ⊂ dom[f])
-> ContinuousOpen  f (x0 - δ) (x0 + δ)
-> IntervalStrictlyMonotonicFun f (Neighbor x0 δ) -> 
∃ a b, a = Rbasic_fun.Rmin f[x0 - δ/2] f[x0 + δ/2] /\ b = Rbasic_fun.Rmax f [x0 - δ/2] f[x0 + δ/2] /\ \(a, b\) ⊂ dom[f ﹣¹] /\ (∀ y, y ∈ \(a, b\) -> Continuous f ﹣¹ y /\ IntervalStrictlyMonotonicFun f ﹣¹ \(a, b\)).
Proof. (* 需要用到4-2的定理, f逆在 [y0 - δ/2, y0 + δ/2] 严格单调且连续*)  
  intros. red in H1. pose proof H as H'.
  red in H. destruct H. pose proof H2 as H2'. red in H2.
  pose proof H3 as H3'. red in H3.  
  assert (x0 - δ / 2 ∈ Neighbor x0 δ).
  { apply AxiomII. assert ((x0 - δ / 2 - x0) = (x0 - x0 - δ / 2)). lra.
    rewrite H5. rewrite Abs_lt. lra. lra. }
  assert (x0 + δ / 2 ∈ Neighbor x0 δ).
  { apply AxiomII. assert ((x0 + δ / 2 - x0) = (x0 - x0 + δ / 2)). lra.
    rewrite H6. rewrite Abs_gt. lra. lra. }  
  assert (ContinuousClose f (x0 - δ/2) (x0 + δ/2)). 
  { red in H. destruct H. red. split. red. intros. apply H2. lra.
    assert (Continuous f (x0 - δ / 2)).
    { apply H2. lra. }
    assert (Continuous f (x0 + δ / 2)).
    { apply H2. lra. }
    apply Theorem4_1 in H8. destruct H8.
    apply Theorem4_1 in H9. destruct H9.
    split; auto. }
  destruct H3; pose proof H3 as I3;  
  red in H3; destruct H3 as [H3 [H8 H9]].  
  - exists (f [x0 - δ / 2]), (f [x0 + δ / 2]).
    apply (H9 (x0 - δ / 2)(x0 + δ / 2)) in H5 as H5'; auto.
    split. unfold Rbasic_fun.Rmin. destruct Rle_dec. auto. lra.
    split. unfold Rbasic_fun.Rmax. destruct Rle_dec. auto. lra. 
    split. red. intros y H10.            
    pose proof (Lemma_inver f). destruct H11. applyAxiomII H10. 
    rewrite H11.    
    apply (Theorem4_7 f  (x0 - δ / 2) (x0 + δ / 2) y) in H7 as H13; auto. 
    destruct H13 as [x [H14 H14']].
    rewrite <- H14'. 
    assert (x ∈ dom[ f ]).
    { apply H1. apply AxiomII. apply Abs_R. lra. }
    red in H. destruct H.  
    apply fx_ran; auto. lra.  
    + intros. 
      assert (ContinuousClose (f ﹣¹) f [x0 - δ / 2] f [x0 + δ / 2]).
      { apply (Theorem4_8 f (f ﹣¹) (x0 - δ / 2) (x0 + δ / 2)); auto.  
        rewrite <- H4. auto. lra.
        red. red in I3. destruct I3 as [I1 [I2 I3]].
        split; auto. split. 
        - intros x' I4. 
          apply AxiomII. exists f[x']. apply x_fx; auto. apply H1. apply AxiomII.
          apply Abs_R. applyAxiomII I4. lra. 
        - intros. apply I3; auto. apply AxiomII. apply Abs_R. applyAxiomII H11.
          lra. apply AxiomII. apply Abs_R. applyAxiomII H12. lra. }
      red in H11. destruct H11 as [H11 [H12 H13]]. 
      red in H11. applyAxiomII H10. apply H11 in H10; auto.
      split; auto. red. left.
      assert (IntervalStrictlyIncreaseFun (f﹣¹) (\[ f [x0 - δ / 2], f [x0 + δ / 2]  \])).  
      { apply (Lemma_4_8 f g (x0 - δ / 2) (x0 + δ / 2)); auto.
        lra. red in I3. destruct I3 as [I1 [I2 I3]].
        red. split; auto. split. intros x' I4. 
        apply AxiomII. exists f[x']. apply x_fx; auto. apply H1. apply AxiomII.
        apply Abs_R. applyAxiomII I4. lra.
        intros.
        apply I3. apply AxiomII. applyAxiomII H14. apply Abs_R. lra.
        apply AxiomII. applyAxiomII H15. apply Abs_R. lra. auto. }
      red in H14. destruct H14 as [H14 [H15 H16]].
      red. split; auto. split.
      * intros y0 H17. applyAxiomII H17.
        apply (Theorem4_7 f (x0 - δ / 2) (x0 + δ / 2) y0) in H7 as H18; auto.
        destruct H18 as [x' [H18 H18']]. 
        apply AxiomII. exists x'. 
        apply AxiomII'. rewrite <- H18'.
        apply x_fx; auto. apply H1. apply AxiomII. apply Abs_R. lra. lra.
      * intros. apply H16; auto.  
        apply AxiomII. applyAxiomII H17. destruct H17.
        split. left; auto. left; auto.
        apply AxiomII. applyAxiomII H18. destruct H18.
        split. left; auto. left; auto.
    + lra. 
  - exists (f [x0 + δ / 2]), (f [x0 - δ / 2]).
    apply (H9 (x0 - δ / 2)(x0 + δ / 2)) in H5 as H5'; auto.
    split. unfold Rbasic_fun.Rmin. destruct Rle_dec. lra. auto.
    split. unfold Rbasic_fun.Rmax. destruct Rle_dec. auto. lra. auto. 
    split. red. intros y H10.            
    pose proof (Lemma_inver f). destruct H11. applyAxiomII H10. 
    rewrite H11.    

    apply (Theorem4_7 f  (x0 - δ / 2) (x0 + δ / 2) y) in H7 as H13; auto. 
    destruct H13 as [x [H14 H14']].
    rewrite <- H14'. 
    assert (x ∈ dom[ f ]).
    { apply H1. apply AxiomII. apply Abs_R. lra. }
    red in H. destruct H.  
    apply fx_ran; auto. lra.  
    + intros. 
      assert (ContinuousClose (f ﹣¹) f [x0 + δ / 2] f [x0 - δ / 2]).
      { apply (Theorem4_8' f (f ﹣¹) (x0 - δ / 2) (x0 + δ / 2)); auto.  
        rewrite <- H4. auto. lra.
        red. red in I3. destruct I3 as [I1 [I2 I3]].
        split; auto. split. 
        - intros x' I4. 
          apply AxiomII. exists f[x']. apply x_fx; auto. apply H1. apply AxiomII.
          apply Abs_R. applyAxiomII I4. lra. 
        - intros. apply I3; auto. apply AxiomII. apply Abs_R. applyAxiomII H11.
          lra. apply AxiomII. apply Abs_R. applyAxiomII H12. lra. }
      red in H11. destruct H11 as [H11 [H12 H13]]. 
      red in H11. applyAxiomII H10. apply H11 in H10; auto.
      split; auto. red. right.
      assert (IntervalStrictlyDecreaseFun (f﹣¹) (\[ f [x0 + δ / 2], f [x0 - δ / 2]  \])).  
      { apply (Lemma_4_8' f g (x0 - δ / 2) (x0 + δ / 2)); auto.
        lra. red in I3. destruct I3 as [I1 [I2 I3]].
        red. split; auto. split. intros x' I4. 
        apply AxiomII. exists f[x']. apply x_fx; auto. apply H1. apply AxiomII.
        apply Abs_R. applyAxiomII I4. lra.
        intros.
        apply I3. apply AxiomII. applyAxiomII H14. apply Abs_R. lra.
        apply AxiomII. applyAxiomII H15. apply Abs_R. lra. auto. }
      red in H14. destruct H14 as [H14 [H15 H16]].
      red. split; auto. split. 
      * intros y0 H17. applyAxiomII H17.
        apply (Theorem4_7 f (x0 - δ / 2) (x0 + δ / 2) y0) in H7 as H18; auto.
        destruct H18 as [x' [H18 H18']]. 
        apply AxiomII. exists x'. 
        apply AxiomII'. rewrite <- H18'.
        apply x_fx; auto. apply H1. apply AxiomII. apply Abs_R. lra. lra. 
      * intros. apply H16; auto.  
        apply AxiomII. applyAxiomII H17. destruct H17.
        split. left; auto. left; auto.
        apply AxiomII. applyAxiomII H18. destruct H18.
        split. left; auto. left; auto.
    + lra.
Qed.



(* 连续的第二个定义 *)
Definition Continuous' (f : Fun) (x0: R) := 
 x0 ∈ dom[f] /\ limit \{\ λ δx δy, δy = f[x0 + δx] - f[x0]\}\ 0 0.
Theorem EquaContinuous : ∀ (f : Fun) (x0: R),  
   Continuous f x0 -> Continuous' f x0. 
Proof. 
  intros. red. intros. red in H.
  destruct H as [H' H]. split; auto.
  unfold limit in *.
  destruct H as [H [δ [H2 [H3 H4]]]].
  split.
  - red. intros. applyAxiomII' H1. applyAxiomII' H0. rewrite H1. auto.
  - exists δ. split; auto. split.
    + red. intros. apply AxiomII. exists (f [x0 + z] - f [x0]). apply AxiomII'.
      auto.
    + intros. apply H4 in H0. destruct H0 as [δ' [H5 H6]].
      exists δ'. split; auto.
      intros.
      assert (\{\ λ δx δy,δy = f [x0 + δx] - f [x0] \}\ [x]
              = f [x0 + x] - f [x0]).
      { apply f_x. 
        - red. intros. applyAxiomII' H1. applyAxiomII' H7. rewrite H7. auto.
        - apply AxiomII'. auto. }
      rewrite H1. 
      pose proof (H6 (x0+x)).
      assert (x0+x-x0=x). lra. rewrite H8 in H7. 
      rewrite Rminus_0_r in H0. 
      apply H7 in H0. rewrite Rminus_0_r. auto. 
Qed.


(* 反函数的导数 *)
Theorem Theorem5_7' : ∀f g x0 y0,Inverse_Function f g -> [x0 ,y0] ∈ f
-> (∃ δ:R, δ > 0 /\ (Neighbor x0 δ ⊂ dom[f]) /\
(ContinuousOpen  f (x0 - δ) (x0 + δ) /\
IntervalStrictlyMonotonicFun f (Neighbor x0 δ))) -> derivative f x0 (f '[x0]) -> f '[x0] <> 0 -> derivative f ﹣¹ y0  (1 / f '[x0]).
Proof. 
  intros f g x0 y0 H1 H2' H3 H4 H5.
  destruct H3 as [δ [H3 [H7 [H8 H8']]]].
  apply (Lemma5_7' f g x0 δ) in H1 as H1'; auto. 
  destruct H1' as [a[b[L1 [L2[L3 L4]]]]]. 
  red in H1. pose proof H1 as h1.
  destruct H1 as [[H1 H1']_]. 
  assert (J1 : x0 - δ < x0 < x0 + δ). lra.
  assert (J1' :x0 ∈ Neighbor x0 δ).
  { apply AxiomII. rewrite Abs_ge; lra.  }
  assert (K2 : y0 ∈ \( a, b \)).
  { apply AxiomII. red in H8. 
    apply H8 in J1 as H. 
    destruct H as [K1 K2]. red in K2.
    assert (Q1 :(x0 - δ / 2)∈ Neighbor x0 δ).
    { apply AxiomII.  replace (x0 - δ / 2 - x0) with (- (δ / 2)).
      rewrite <- Abs_eq_neg. rewrite Abs_gt; lra. lra. }
    assert (Q2: (x0 + δ / 2)∈ Neighbor x0 δ).
    { apply AxiomII.  replace (x0 + δ / 2 - x0) with (δ / 2).
      rewrite Abs_gt; lra. lra. }
    assert (H2: f[ x0 ] = y0).
    { apply f_x; auto. }
    assert ([y0, x0] ∈ f ﹣¹).
    { apply AxiomII. exists y0,x0. split; auto. }
    apply f_x in H; auto. red in H8'.
    destruct H8'.  
    - red in H0. destruct H0 as [H14 [K2' K3]].
      apply (K3 (x0 - δ / 2) x0) in Q1 as H0'; auto.
      apply (K3 x0 (x0 + δ / 2)) in Q2 as H'; auto. 
      unfold Rbasic_fun.Rmin in L1. 
      destruct Rle_dec in L1. rewrite L1.
      rewrite <- H2. split; auto.
      unfold Rbasic_fun.Rmax in L2; 
      destruct Rle_dec in L2; rewrite L2; auto;
      lra. unfold Rbasic_fun.Rmax in L2; 
      destruct Rle_dec in L2; rewrite L2; auto;
      lra. lra. lra.
    - red in H0. destruct H0 as [H14 [K2' K3]].
      apply (K3 (x0 - δ / 2) x0) in Q1 as H0'; auto.
      apply (K3 x0 (x0 + δ / 2)) in Q2 as H'; auto.
      unfold Rbasic_fun.Rmin in L1. 
      destruct Rle_dec in L1. rewrite L1.
      rewrite <- H2.  split; auto. lra.
      unfold Rbasic_fun.Rmax in L2; 
      destruct Rle_dec in L2; rewrite L2; auto;
      lra. unfold Rbasic_fun.Rmax in L2; 
      destruct Rle_dec in L2; rewrite L2; auto;
      lra. lra. lra. }
  apply L4 in K2 as H.
  destruct H as [H' H''].  
  apply (EquaContinuous f ﹣¹ y0) in H'.
  red in H'. destruct H' as [H0' H].   
  red in H8. apply H8 in J1 as H3'.
  apply (EquaContinuous f x0) in H3'.
  red in H3'. destruct H3' as [H3' H'].
  apply (Equaderivative (f﹣¹) y0 ((1 / f '[ x0]))); auto.
  apply (Equaderivative f x0 (f '[ x0])) in H4. 
  red in H4. destruct H4 as [_[H4 H9]].
  assert (K1 : ∀x: R, \{\ λ h y,y = (f[x0 + h] - f[x0]) / h \}\ [x] = (f[x0 + x] - f[x0]) / x). 
  { intros. Function_ass. } 
  assert (H9':limit \{\ λ h y,y = h / (f [x0 + h] - f[x0]) \}\ 0 (1 / f '[ x0])). 
  { apply (Theorem3_7_4' \{\ λ h y,y = (f[x0 + h] - f[x0]) / h \}\ 0  (f '[ x0])) in H9; auto. 
    unfold limit. unfold limit in H9.
    destruct H9 as [I1[δ'[I2[I3 I4]]]]. 
    assert (L7:Function \{\ λ h y,y = h / (f [x0 + h] - f[x0]) \}\). 
    { QED_function. } 
      split; auto. exists δ'. split; auto. 
      split. intros z H6. apply AxiomII. 
      exists (z / (f [x0 + z] - f[x0])). 
      apply AxiomII'; auto. intros. 
      apply I4 in H0 as H2. clear I4.
      destruct H2 as [δ''[[J0' J1'']J2]].
      pose proof (Lemma1' δ' δ δ''). 
      apply H2 in I2 as I2'; auto. clear H2.
      destruct I2' as [δ0[J3 [J4 [J5 J6]]]].
      exists δ0. split; auto. intros.
      assert (0 < Abs [x - 0] < δ''). lra.
      apply J2 in H6. clear J2. 
      assert ((1 /// \{\ λ h y,y = (f [x0 + h] - f [x0]) / h \}\) [x] = 1/((f[x0 + x] - f [x0]) / x)).
      { apply f_x; auto. apply AxiomII'; auto.
        split. apply AxiomII. 
        exists ((f[x0 + x] - f[x0]) / x).
        apply AxiomII'; auto.
        assert (\{\ λ h y,y = (f[x0 + h] - f [x0]) / h \}\ [x]=(f [x0 + x] - f [x0]) / x).
        { Function_ass. } split.  
        - rewrite H9.
          assert (0 < Abs [x - 0] < δ). lra.
          assert ((x0 + x) ∈ (Neighbor x0 δ)).
          { apply AxiomII. replace (x0 + x - x0) with x.
            rewrite Rminus_0_r in H10.
            lra. lra. } red in H8'.
          destruct H8'. 
          + red in H12. 
            destruct H12 as [_ [_ H12]].
            rewrite Rminus_0_r in H2.
            destruct H2. apply Abs_not_eq_0 in H2. 
            unfold Rdiv. apply Rmult_integral_contrapositive.
            split.
            * pose proof (Rge_lt x 0).
              destruct H14.
              -- destruct H14. apply (H12 x0 (x0 + x)) in J1'; auto.
                 lra. lra.
                 rewrite H14 in H2. lra.
              -- apply (H12 (x0 + x) x0) in H11; auto. lra. lra.
            * apply Rinv_neq_0_compat; auto.
          + red in H12.  
            destruct H12 as [_ [_ H16]].
            rewrite Rminus_0_r in H2.
            destruct H2. apply Abs_not_eq_0 in H2. 
            unfold Rdiv. apply Rmult_integral_contrapositive.
            split.
            * pose proof (Rge_lt x 0).
              destruct H13.
              -- destruct H13. apply (H16 x0 (x0 + x)) in J1'; auto.
                 lra. lra.
                 rewrite H13 in H6. lra.
              -- apply (H16 (x0 + x) x0) in H11; auto. lra. lra.
            * apply Rinv_neq_0_compat; auto. 
        - rewrite H9. lra. }
      rewrite H9 in H6. 
      assert (\{\ λ h y,y = h / (f[x0 + h] - f[x0]) \}\ [x]
             =  (x / (f [x0 + x] - f[x0]))).
      { Function_ass. } rewrite H10.
      assert ((1 / (((f [x0 + x] - (f[x0])) / x)) = 
              x / (f [x0 + x] - f [x0]))).
      { unfold Rdiv. rewrite Rmult_1_l.
        rewrite (Rinv_mult_distr (f[x0 + x] - f [x0]) ( / x)).
        rewrite (Rinv_involutive x). 
        apply Rmult_comm.
        rewrite Rminus_0_r in H2.
        destruct H2. apply Abs_not_eq_0 in H2. lra.
        assert (0 < Abs [x - 0] < δ). lra.
        assert ((x0 + x) ∈ (Neighbor x0 δ)).
        { apply AxiomII. replace (x0 + x - x0) with x.
          rewrite Rminus_0_r in H11.
          lra. lra. } red in H8'.
        destruct H8'. 
        + red in H13. 
          destruct H13 as [_ [_ H17]].
          rewrite Rminus_0_r in H11.
          destruct H11. apply Abs_not_eq_0 in H11. 
          pose proof (Rge_lt x 0).
          destruct H14.
          -- destruct H14. apply (H17 x0 (x0 + x)) in J1'; auto. lra. lra.
            rewrite H14 in H13. lra.
          -- apply (H17 (x0 + x) x0) in H12; auto. lra. lra.
        + red in H13.  
          destruct H13 as [_ [_ H17]].
          rewrite Rminus_0_r in H11.
          destruct H11. apply Abs_not_eq_0 in H11. 
          pose proof (Rge_lt x 0).
          destruct H14.
          -- destruct H14. apply (H17 x0 (x0 + x)) in J1'; auto. lra. lra.
             rewrite H14 in H13. lra.
          -- apply (H17 (x0 + x) x0) in H12; auto. lra. lra.
        + apply Rinv_neq_0_compat.
          rewrite Rminus_0_r in H2.
          destruct H2. apply Abs_not_eq_0 in H2. lra. }
       rewrite H11 in H6. 
       replace (/ f '[ x0]) with (1 / f '[ x0]) in H6.
       auto. lra. }
   red. unfold limit in H9'.
   split; auto.
   assert (K3: ∃δ': R, δ' > 0 /\ Neighbor y0 δ' ⊂\( a, b \)).
   { exists (Rbasic_fun.Rmin Abs[y0 - a] Abs[b -y0]).
     unfold Rbasic_fun.Rmin. destruct Rle_dec. 
     pose proof (Abs_Rge0 (y0 - a)). split.
     destruct H0; auto.
     apply <- Abs_eq_0 in H0.
     apply Rminus_diag_uniq in H0. rewrite H0 in K2.
     applyAxiomII K2. destruct K2. lra.
     intros z H6'. applyAxiomII H6'. 
     apply AxiomII. split.
     - applyAxiomII K2. destruct K2 as [K2 K2'].
       assert (H13 : Abs [y0 - a] = y0 -a).
       { rewrite Abs_ge; lra. }
       rewrite H13 in H6'. clear H13.
       pose proof (Rge_lt (z - y0) 0).
       destruct H2. 
       + apply (Rminus_ge z y0) in H2.
         apply (Rge_gt_trans (z) (y0) (a)); auto.
       + assert (Abs [z - y0] = y0 -z).  rewrite Abs_lt; lra.
         rewrite H6 in H6'. lra.
     - applyAxiomII K2. destruct K2 as [K2 K2'].
       assert (Abs [z - y0] < Abs [b - y0]). lra.
       assert (Abs [b - y0] = b - y0). apply Abs_ge; lra.
       rewrite H6 in H2. 
       pose proof (Rge_lt (z - y0) 0).
       destruct H10.
       + assert (Abs [z - y0] = z - y0). rewrite Abs_ge; lra.
         rewrite H11 in H2. lra.
       + apply (Rminus_lt z y0) in H10.
         apply (Rlt_trans (z) (y0) (b)); auto.
    - apply Rnot_le_lt in n. split. 
      pose proof (Abs_Rge0 (b - y0)).
      destruct H0; auto.
      apply <- Abs_eq_0 in H0.
      apply Rminus_diag_uniq in H0. rewrite H0 in K2.
      applyAxiomII K2. destruct K2. lra.
      intros z H6'. applyAxiomII H6'. 
      apply AxiomII. split.
      applyAxiomII K2. destruct K2 as [K2 K2'].
       assert (Abs [b - y0] = b -y0).
       { rewrite Abs_ge; lra. }
       rewrite H0 in H6'. 
       pose proof (Rge_lt (z - y0) 0).
       destruct H2. 
       + apply (Rminus_ge z y0) in H2.
         apply (Rge_gt_trans (z) (y0) (a)); auto.
       + assert (Abs [z - y0] = y0 -z).  rewrite Abs_lt; lra.
         assert (y0 > a). lra. assert(Abs [y0 - a] = y0 -a). 
         apply Abs_ge; lra. assert (Abs [z - y0] < Abs [y0 - a]).
         lra. rewrite H11 in H12. rewrite H6 in H12. lra.
       + applyAxiomII K2. destruct K2 as [K2 K2'].
         assert (Abs [b - y0] = b - y0). apply Abs_ge; lra.
         rewrite H0 in H6'. pose proof (Rge_lt (z - y0) 0).
         destruct H2. assert (Abs [z - y0] = z - y0). 
         rewrite Abs_ge; lra. rewrite H6 in H6'. lra.
         apply (Rminus_lt z y0) in H2.
         apply (Rlt_trans (z) (y0) (b)); auto. }
     destruct K3 as [δ'[K3 K4]]. split.
     exists δ'. split; auto. unfold Contain in *.
     intros. apply L3. apply K4; auto.
     unfold limit in H. unfold limit in H'.
     red. split. unfold Function. intros. 
     applyAxiomII' H0. applyAxiomII' H2; rewrite H2; auto. 
     destruct H9' as [K5 [δ1 [K6 [K7 K8]]]].
     exists δ1. split; auto. split. 
     - intros z K9. apply AxiomII. 
       exists (((f ﹣¹) [y0 + z] - (f ﹣¹) [y0]) / z).
       apply AxiomII'; auto.
     - intros. apply K8 in H0 as K8'.
       destruct K8' as [δ1'[K9 K10]].
       destruct K9 as [K9 K9']. 
       destruct H as [H Q4]. destruct Q4 as [δ2[Q4[Q5 Q6]]].
       destruct H' as [J0' [δ3[J2 [J3 J4]]]].
       apply Q6 in K9 as Q6'.
       apply J4 in K6 as J4'. destruct J4' as [δ3'[[J5 J7] J6]].
       apply Q6 in J5 as J5'. 
       destruct Q6' as [δ2' [[Q7' Q6'] Q7]].
       destruct J5' as [δ2''[[J7' J6'] J8]].
       pose proof (Lemma1'' δ1' δ' δ2' δ2'') as H13.
       pose proof K9 as H13'.
       apply H13 in H13'; auto. clear H13.
       destruct H13' as [δ0[H13[H14[H15 [H16 H17]]]]].
       exists δ0. split; auto.
       split; auto. lra. intros y1 H13'.
       assert (0 < Abs [y1 - 0] < δ2'). lra.
       assert (L5:0 < Abs [y1 - 0] < δ2''). lra.
       apply Q7 in H2 as Q7''. 
       apply J8 in L5 as L5'.   
       assert (K11 : ∀y1: R, \{\ λ δx δy,δy = (f ﹣¹) [y0 + δx] - (f ﹣¹) [y0] \}\ [y1] = (f ﹣¹) [y0 + y1] - (f ﹣¹)  [y0]). 
       { intros. apply f_x; auto. apply AxiomII'; auto. }
       rewrite K11 in Q7''. rewrite K11 in L5'. 
       rewrite Rminus_0_r in Q7''. rewrite Rminus_0_r in L5'.
       assert (H19 : ∃δx: R, δx = (f ﹣¹) [y0 + y1] - (f ﹣¹) [y0]).
       { exists ((f ﹣¹) [y0 + y1] - (f ﹣¹) [y0]); auto.  }
       destruct H19 as [δx].   
       assert (H20:δx <> 0).
       { assert (0 < Abs [y1 - 0] < δ'). lra.
         red in H1'. assert ((y0 + y1) ∈ Neighbor y0 δ'). 
         apply AxiomII. replace (y0 + y1 - y0) with (y1 - 0); lra.
         assert ((y0 + y1) ∈ \( a, b \)). 
         { apply K4; auto.  } red in H''.
         destruct H'' as [H''|H''];
         red in H''; destruct H'' as [_[_ H'']]; 
           destruct H10; clear Q6 J4 K8 K10; 
           rewrite Rminus_0_r in H18; apply Abs_not_eq_0 in H10;
           apply Rdichotomy in H10; destruct H10.
           + apply (H''(y0 + y1) y0) in H12; auto; lra.
           + apply (H'' y0 (y0 + y1)) in K2; auto; lra.
           + apply (H''(y0 + y1) y0) in H12; auto; lra.
           + apply (H'' y0 (y0 + y1)) in K2; auto; lra. }
       rewrite <- H6 in Q7''.
       rewrite <- H6 in L5'.
       assert (H21 : 0 < Abs [δx - 0] < δ1').
       { rewrite Rminus_0_r. split; auto. apply Abs_not_eq_0; auto. }
       apply K10 in H21.
       assert (H21' : 0 < Abs [δx - 0] < δ3').
       { rewrite Rminus_0_r. split; auto. apply Abs_not_eq_0; auto. }
       apply J6 in H21'. clear K10. clear J6.
       assert (H22:∀δx,\{\ λ h y,y = h / (f[x0 + h] - f[x0]) \}\ [δx] = δx / (f[x0 + δx] - f[x0])). 
       { intros. apply f_x; auto. apply AxiomII'; auto.  }
       rewrite H22 in H21. 
       assert (H23:\{\ λ h y,y = ((f ﹣¹)[y0 + h] - (f ﹣¹)[y0]) / h \}\ [y1] = ((f ﹣¹)[y0 + y1] - (f ﹣¹)[y0]) / y1).
       { Function_ass.  } 
       rewrite H23. 
       assert (H24:∀δx: R, \{\ λ δx δy,δy = f[x0 + δx] - f[x0] \}\ [δx] = f[x0 + δx] - f[x0]).
       { intros. apply f_x; auto. apply AxiomII'; auto. } 
       rewrite H24 in H21'. clear H23 H24 H22.
       rewrite <- H6.
       assert (H22:∃δy:R,δy = f[x0 + δx] - f[x0]).
   { exists (f[x0 + δx] - f[x0]); auto.  }
   destruct H22 as [δy]. 
       assert (H23: δy = y1).
      { rewrite H10. rewrite H6.
        assert((f ﹣¹) [y0] = x0).
        { apply f_x; auto. apply AxiomII'; auto. }
        rewrite H11. rewrite Rplus_comm.   
       replace ((f ﹣¹) [y0 + y1] - x0 + x0) with (f ﹣¹) [y0 + y1]. 
       assert (f [(f ﹣¹) [y0 + y1]] = y0 + y1). 
       { assert (y0 + y1 ∈ dom[ f ﹣¹]). apply L3. apply K4.
         apply AxiomII; replace (y0 + y1 - y0) with y1; 
         destruct H13'; rewrite Rminus_0_r in H18; lra.
         apply (Lemma_Inverse' f g); auto. }
         rewrite H12. assert(f[x0] = y0).
        { apply f_x; auto. } rewrite H18. lra. lra. }
       rewrite <- H10 in H21. rewrite <- H23; auto.
Qed.



 
(* 复合函数的导数引理 书本93页 *)
Lemma Lemma5_81 : ∀ (f : Fun) (x0 : R), derivable f x0  -> Function f /\ 
(∃ δ:R, δ > 0 /\ Neighbor x0 δ ⊂ dom[ f] /\ (∃ h: Fun, Continuous h x0 /\  
∀x: R, x ∈ Neighbor x0 δ -> f[x] - f[x0] = h [x] * (x - x0) /\ 
h[x0] = f '[x0])).
Proof.
  intros. split; intros. 
  - unfold derivable in H. destruct H as [y0'].
    apply derEqual in H as H7.
    unfold derivative in H. destruct H as [H[H1 H2]]. auto. 
  - red in H. destruct H as [y0'].
    apply derEqual in H as H7.
    unfold derivative in H. destruct H as [H[H1 H2]].
    destruct H1 as [δ [H1 J3]].
    unfold limit in H2. destruct H2 as [H2[δ' [H3 [H4 H5]]]].
    exists δ. split; auto. split; auto.
    assert (∃h :Fun, h = \{\ λ x y, x = x0 /\ y = y0' \/ 
    x ∈ Neighbor0 x0 δ /\ y = (f [x] - f [x0]) / (x - x0) \}\).
    { exists \{\ λ x y, x = x0 /\ y = y0' \/ x ∈ Neighbor0 x0 δ 
    /\ y = (f [x] - f [x0]) / (x - x0) \}\. auto. }
    destruct H0 as [h]. exists h. 
    assert (K1 :[x0, y0'] ∈ h).
    { rewrite H0. apply AxiomII'. left. split; auto. }
    assert (Function h). 
    { rewrite H0. unfold Function. intros. applyAxiomII' H6.
      applyAxiomII' H8. destruct H6 as [[H6 H12]|[H6 H12]]; 
      destruct H8 as [[H8 H13]|[H8 H13]]. rewrite H13; auto.
      applyAxiomII H8. rewrite H6 in H8. 
      destruct H8. rewrite Rminus_diag_eq in H8.
      rewrite Abs_ge in H8. lra. right; auto. auto.
      applyAxiomII H6. rewrite H8 in H6. 
      destruct H6. rewrite Rminus_diag_eq in H6.
      rewrite Abs_ge in H6. lra. right; auto. auto.
      rewrite H13. auto. }
    assert (h[x0] = y0'). 
    { apply f_x. auto. rewrite H0. apply AxiomII'. left.
      split; auto.  }
    repeat split; auto.
    + apply AxiomII. exists y0'. auto.
    + exists δ. split; auto. split. intros z H11.
      apply AxiomII. exists ((f[z] - f[x0])/(z - x0)).
      rewrite H0. apply AxiomII'.
      right. repeat split; auto. intros.
      apply H5 in H9. destruct H9 as [δ2 [H9 H12]].
      pose proof (Lemma1 δ2 δ); auto. destruct H9 as [H9 K2].
      apply H10 in H9; auto. clear H10.
      destruct H9 as [δ3 [K3 [K4 K5]]].
      exists δ3. split; auto. intros. 
      assert (0 < Abs [x - x0] < δ2). lra.
      apply H12 in H10 as H14. 
      assert (\{\ λ x1 y,y = (f [x1] - f [x0]) / (x1 - x0) \}\ [x] = 
      (f [x] - f [x0]) / (x - x0) ).
      { apply f_x; auto. apply AxiomII'; auto. }
      rewrite H11 in H14.  
      assert (h [x] = (f [x] - f [x0]) / (x - x0)).
      { apply f_x; auto. rewrite H0. apply AxiomII'.
        right. repeat split; auto. apply AxiomII; auto. lra. }
      rewrite H13. rewrite H8. auto.
    + applyAxiomII H9. assert (H11: Abs [x - x0] >= 0).
      { apply Abs_Rge0. } destruct H11.
      * apply Abs_not_eq_0 in H10 as J2;
        apply Rinv_neq_0_compat in J2 as H12.  
        apply (Rmult_eq_reg_r (/(x - x0))); auto.
        rewrite Rmult_assoc.
        rewrite (Rinv_r (x - x0)); auto.
        rewrite Rmult_1_r.   
        assert (h [x] = (f [x] - f [x0]) / (x - x0)).
        { apply f_x; auto. rewrite H0. apply AxiomII'.
          right. repeat split; auto. apply AxiomII; auto. }
          rewrite H11; auto.
        * destruct (classic (x = x0)). rewrite H11. lra.
          apply Rminus_eq_contra in H11.
          apply Abs_not_eq_0 in H11. lra.
     + rewrite H7; auto.
Qed.


Lemma Lemma5_81' : ∀ (f h : Fun) (x0 : R), Function f /\ 
(∃ δ:R, δ > 0 /\ Neighbor x0 δ ⊂ dom[ f] /\ ( Continuous h x0 /\  
∀x: R, x ∈ Neighbor x0 δ -> f[x] - f[x0] = h [x] * (x - x0) )) ->  
derivative f x0 h[x0].
Proof. 
  intros. destruct H as [H1 H2]. destruct H2 as [δ [H2 [H3 [H4 H5]]]]. 
  unfold derivative. split; auto.  
  assert (H9: Function \{\ λ x y,y = (f [x] - f [x0]) / (x - x0) \}\).
  { unfold Function. intros. applyAxiomII' H0. applyAxiomII' H. 
    rewrite H; auto. }
  unfold Continuous in H4. destruct H4 as [H4 H6].
  split.
  + exists δ; split; auto.
  + red in H6. red.
    destruct H6 as [H6 [δ'[H7[H8 H10]]]].
    split; auto. exists δ'. split; auto. split.
    * intros x I1. apply AxiomII. exists ( (f [x] - f [x0]) / (x - x0)).
      apply AxiomII'. auto.
    * intros. pose proof H as H'. apply H10 in H'.
      destruct H' as [δ1 [H' H'']]. destruct H' as [H' H0].
      pose proof (Lemma1' δ δ' δ1). pose proof H2 as H2'. 
      apply H11 in H2'; auto. destruct H2' as [δ2 [H12 [H13 [H14 H15]]]].
      exists δ2. 
      split. auto. intros.
      assert ( 0 < Abs [x - x0] < δ1).
      { split. lra. destruct H16. 
        apply (Rlt_trans (Abs [x - x0]) δ2 δ1); auto. }
      apply H'' in H17. 
      assert (\{\ λ x1 y, y = (f [x1] - f [x0]) / (x1 - x0) \}\ [x]
                 = (f [x] - f [x0]) / (x - x0) ).
      { apply f_x; auto. apply AxiomII'. auto. }
      rewrite H18. clear H18.
      assert (x ∈ Neighbor x0 δ).
      { apply AxiomII. destruct H16. 
        apply (Rlt_trans (Abs [x - x0]) δ2 δ); auto. }
      apply H5 in H18. 
      apply (Rmult_eq_compat_r (/(x - x0)) (f [x] - f [x0]) ( h [x] * (x - x0)))
      in H18.
      assert ((f [x] - f [x0]) * / (x - x0) = (f [x] - f [x0]) / (x - x0)).
      lra. rewrite H19 in H18. 
      assert (h [x] * (x - x0) * / (x - x0) = h[x]).
      apply (Rinv_r_simpl_l (x - x0) (h [x])). destruct H16.
      apply Abs_not_eq_0 in H16. auto.
      rewrite H20 in H18. rewrite H18. apply H17.
Qed. 

Lemma Lemma_budeng : ∀x y z, x-z < y <-> x<y+z.
Proof.
  intros. split; intros.
  -  apply (Rplus_lt_compat_r (z) (x-z) y) in H. 
     simpl in H. lra.
  -  apply (Rplus_lt_compat_r (-z) _ _) in H.
    lra. 
Qed.


(* 引理 复合函数及乘法的连续性 *)
Lemma Lemma_comp_con : ∀ (F Φ H φ: Fun) (x0 u0: R), Continuous Φ x0 -> (∀ u x: R, φ[x] = u) -> Continuous F u0 -> H = \{\ λ x y,y = F [φ [x]] * Φ [x] \}\ -> Continuous H x0.
Proof.  
  intros. assert (K1 : Function H).
  { unfold Function. rewrite H3. intros. applyAxiomII' H4.
    applyAxiomII' H5. rewrite H5; auto. } 
    unfold Continuous in *. split. 
    - apply AxiomII.  
      exists (F [φ [x0]] * Φ [x0]). rewrite H3.
      apply AxiomII'; auto.
    - destruct H0 as [H9 I1].
      destruct H2 as [H5 I3]. unfold limit in *.
      split; auto. destruct I1 as [I1[δ1[I4[I5 I6]]]].
      destruct I3 as [I3[δ2[I7[I8 I9]]]]. 
      pose proof(Lemma1 δ1 δ2). apply H0 in I4; auto.
      destruct I4 as [δ3[J1[J2 J3]]]. exists δ3.
      split;auto. split.
      + clear H0. intros z H11.
        apply AxiomII. exists (F [φ [z]] * Φ [z]).
        rewrite H3. apply AxiomII'; auto. 
      + intros.  
        assert (∃A : R, A = 1 /(1 + (Abs[F [u0]]) +  (Abs[Φ [x0]]))).
        { exists (1 /(1 + (Abs[F [u0]]) +  (Abs[Φ [x0]]))); auto. }
        destruct H4 as [A H4]. assert (A > 0).
        { rewrite H4. apply Rmult_gt_0_compat. lra. 
        apply Rinv_0_lt_compat. rewrite Rplus_assoc. 
        rewrite Rplus_comm.   
        apply Rle_lt_0_plus_1. apply Rplus_le_le_0_compat.
        pose proof (Abs_Rge0  F [u0]). lra. 
        pose proof (Abs_Rge0  Φ [x0]). lra.  }
        assert (ε * A > 0). { apply Rmult_lt_0_compat; auto. }
        assert (Rbasic_fun.Rmin 1 (ε * A) > 0). 
        { unfold Rbasic_fun.Rmin. destruct (Rle_dec 1 (ε * A)); auto. lra. }
        apply I6 in H7 as K2. apply I9 in H8 as K3.
        destruct K2 as [δ5[K4 K5]]. destruct K3 as [δ4[K6 K7]].
        destruct K6. destruct K4. pose proof (Lemma1' δ3 δ4 δ5).
        apply H14 in J1; auto. destruct J1 as [δ[K2 [K3 [K4 K6]]]].
        exists δ. split; auto. intros. pose proof (H1 u0 x0). 
        assert (∃u, 0 < Abs [u - u0] < δ4). 
        { exists (u0 + δ4/2 ). unfold Rminus. 
          rewrite Rplus_assoc. rewrite Rplus_comm.  
          rewrite Rplus_assoc. rewrite Rplus_opp_l.  
          rewrite Rplus_0_r. split. rewrite Abs_ge; lra. 
          rewrite Abs_ge; lra.   } 
        destruct H17 as [u].
        assert (∀x : R, H [x] = F [φ [x]] * Φ [x]).
        { intros. apply f_x; auto. rewrite H3. apply AxiomII'; auto. }
        rewrite (H18 x). rewrite (H18 x0). 
        replace (F [φ [x]] * Φ [x] - F [φ [x0]] * Φ [x0]) with
        (F [φ [x]] *(Φ [x] - Φ [x0]) + Φ [x0] * (F [φ [x]] - F [φ [x0]])).
        pose proof (Abs_plus_le (F [φ [x]] * (Φ [x] - Φ [x0])) (Φ [x0] * (F [φ [x]] - F [φ [x0]])) ).
        apply (Rle_lt_trans _ _ ε) in H19; auto. 
        rewrite (Abs_mult (F [φ [x]]) ((Φ [x] - Φ [x0]))); rewrite (Abs_mult (Φ [x0]) (F [φ [x]] - F [φ [x0]])). 
        assert (0 < Abs [x - x0] < δ5). lra. apply K5 in H20.
        clear H19. clear H14. 
        apply K7 in H17.
        assert (1 > Abs [F [u] - F [u0]] /\ (ε * A) > Abs [F [u] - F [u0]]).
        { apply Rbasic_fun.Rmin_Rgt; auto. } 
        rewrite <- H16 in H17. 
        pose proof (H1 u x). rewrite <- H19 in H17. 
        assert (Abs [F [φ [x]]] * Abs [Φ [x] - Φ [x0]] + Abs [Φ [x0]] * 
                Abs [F [φ [x]] - F [φ [x0]]] <
                (1 + Abs[F [φ [x0]]]) * (ε * A) + Abs [Φ [x0]] * (ε * A)).
        { destruct H14. apply Rplus_lt_le_compat.  
          - apply Rmult_ge_0_gt_0_lt_compat. apply Abs_Rge0.
            rewrite Rplus_comm. apply Rplus_le_lt_0_compat. 
            pose proof (Abs_Rge0 F [φ [x0]]); lra. lra.
            apply (Lemma_budeng (Abs [F [φ [x]]]) 1 (Abs [F[φ[x0]]])).
            pose proof (Abs_abs_minus' (F [φ [x]]) (F [φ [x0]])).
            apply (Rle_lt_trans (Abs [F [φ [x]]] - Abs [F [φ [x0]]]) (Abs [F [u] - F [u0]]) 1);auto.
            rewrite <- H19. rewrite <- H16. apply H22. apply H20.
          - apply (Rmult_le_compat_l (Abs [Φ [x0]]) ( Abs [F [φ [x]] - F [φ [x0]]] ) ((ε * A))); auto. apply Rge_le.
            apply Abs_Rge0. red. left. rewrite H16. rewrite H19.
            apply Rgt_lt. apply H21.
         } 
         assert ((1 + Abs [F [φ [x0]]]) * (ε * A) + Abs [Φ [x0]] * (ε * A) <= ε).
         { red. right. 
           rewrite <- ( Rmult_plus_distr_r ((1 + Abs [F [φ [x0]]])) (Abs [Φ [x0]]) (ε * A)). 
           rewrite <- Rmult_assoc. 
           rewrite H4. unfold Rdiv. rewrite Rmult_1_l. 
           rewrite <- H16. apply Rinv_r_simpl_m.
           
           red. intros. 
           assert ((Abs [F [u0]] + Abs [Φ [x0]]) >= 0).
           { assert (Abs [F [u0] + Φ [x0]] <= Abs [F [u0]] + Abs [Φ [x0]]).
             apply Abs_plus_le.
             assert (0 <= Abs [F [u0] + Φ [x0]] ). apply Rge_le. 
             apply Abs_Rge0. apply Rle_ge.
             apply (Rle_trans (0) (Abs [F [u0] + Φ [x0]]) 
             (Abs [F [u0]] + Abs [Φ [x0]])); auto.
           }
           assert ((1+ Abs [F [u0]] + Abs [Φ [x0]]) > 0).
           lra. rewrite <- H16 in H24. rewrite H22 in H24. lra.    
         }
         apply (Rlt_le_trans (Abs [F [φ [x]]] * Abs [Φ [x] - Φ [x0]] + 
         Abs [Φ [x0]] * Abs [F [φ [x]] - F [φ [x0]]]) ((1 + Abs [F [φ [x0]]]) 
         * (ε * A) + Abs [Φ [x0]] * (ε * A)) (ε)); auto.
         rewrite Rmult_minus_distr_l.
         rewrite Rmult_minus_distr_l. lra.
Qed.

Theorem Theorem5_8:∀ (f φ : Fun) (x0 u0 : R), derivable φ x0 
 ->  φ[x0] = u0 -> derivable f u0 -> Comp f φ -> 
 derivative (f ◦ φ) x0 (f '[u0] * φ '[x0]).
Proof.  
  intros. pose proof H as H'. apply Lemma5_81 in H.  
  destruct H as [H3 [δ [H4 [H5 [Φ [H6 H7]]]]]].
  pose proof H1 as H1'. apply Lemma5_81 in H1. 
  destruct H1 as [H8 [δ'[H9 [H10 [F [H11 H12]]]]]].
  unfold Comp in H2.    
  assert (I1: ∃ x, x ∈ Neighbor x0 δ).
  exists x0. apply AxiomII. 
   rewrite Rminus_diag_eq; auto.
  rewrite Abs_ge. auto. lra. 
  assert (I1': ∃ u, u ∈ Neighbor u0 δ').
  { exists u0. apply AxiomII. rewrite Rminus_diag_eq; auto.
  rewrite Abs_ge. auto. lra. } 
  assert (∃ H, H = \{\ λ x y,y = F [φ [x]] * Φ [x] \}\).
  { exists (\{\ λ x1 y, y = F [φ [x1]] * Φ [x1] \}\). auto. }
  destruct H as [H I2].
  assert (Continuous H x0).
  { apply (Lemma_comp_con F Φ H φ x0 u0); auto. 
    intros. pose proof (H2 f φ x u).
    destruct H1 as [K1 [K2 [K3 [K4 [K5 K6]]]]]. symmetry. apply K3. }
  assert (Function (f ◦ φ) /\ 
           ∃δ:R, δ > 0 /\ Neighbor x0 δ ⊂ dom[ (f ◦ φ)] /\ ( Continuous H x0 /\  
           ∀x: R, x ∈ Neighbor x0 δ -> (f ◦ φ)[x] - (f ◦ φ)[x0] = H [x] * (x - x0) )).
  { split.
    - red. intros. applyAxiomII' H13. destruct H13 as [y0 [H13 H13']].
      applyAxiomII' H14. destruct H14 as [y1 [H14 H14']].
      apply f_x in H13; auto. apply f_x in H14; auto. rewrite H13 in H14. 
      rewrite H14 in H13'. apply f_x in H13'; auto. apply f_x in H14'; auto.
      rewrite H13' in H14'. apply H14'.
    - exists δ. split; auto. split.
      + intros x K1. destruct I1' as [u I1'].
        pose proof (H2 f φ x u). destruct H13 as [H13[H14 [H15 [H16 [H17 H18]]]]].
        rewrite H17. apply AxiomII. split. apply AxiomII; auto. auto.
      + split;auto.   
        intros. pose proof H13 as H13'. apply H7 in H13. destruct H13.
        destruct I1' as [u I1']. apply H12 in I1'.
        destruct I1' as [H15 H16].
        pose proof (H2 f φ x u) as I3.
        destruct I3 as [I3 [I4 [I5 [I6 [I7 I8]]]]].
        rewrite I5 in H15. rewrite <- H0 in H15. rewrite H13 in H15.
        rewrite I6. pose proof (H2 f φ x0 u0). 
        destruct H17 as [H17 [H18 [H19 [H20 [H21 H22]]]]]. rewrite H20.
        rewrite I2.
        assert (\{\ λ x1 y, y = F [φ [x1]] * Φ [x1] \}\ [x]
                 =  F [φ [x]] * Φ [x]).
        { Function_ass. }
        rewrite H23.
        rewrite <- I5 in H15. rewrite <- H19 in H15. rewrite <- I5.
        rewrite Rmult_assoc. apply H15. }
  apply (Lemma5_81' (f ◦ φ) H x0) in H13.
  rewrite I2 in H13. 
  assert (\{\ λ x y, y = F [φ [x]] * Φ [x] \}\ [x0]
           = F [φ [x0]] * Φ [x0]).
  { Function_ass. }
  rewrite H14 in H13.
  assert ( Function f /\ (∃ δ:R, δ > 0 /\ Neighbor u0 δ ⊂ dom[ f] /\ 
           ( Continuous F u0 /\ ∀u: R, u ∈ Neighbor u0 δ -> 
           f[u] - f[u0] = F [u] * (u - u0) ))).
  { split; auto. exists δ'. split; auto. split; auto. split; auto. intros.
    apply H12 in H15. destruct H15. auto. }
  apply (Lemma5_81' f F u0) in H15.
  assert ( Function φ /\ (∃ δ:R, δ > 0 /\ Neighbor x0 δ ⊂ dom[ φ] /\ 
           ( Continuous Φ x0 /\ ∀x: R, x ∈ Neighbor x0 δ -> 
           φ[x] - φ[x0] = Φ [x] * (x - x0) ))).
  { split; auto. exists δ. split; auto. split; auto. split; auto. intros.
    apply H7 in H16. destruct H16. auto. }
  apply (Lemma5_81' φ Φ x0) in H16.
  apply derEqual in H15. apply derEqual in H16. 
  rewrite H15. rewrite H16. rewrite <- H0. apply H13.
Qed.



(* 基本初等函数导数公式 *)
Lemma Lemma3 : ∀ a n, Function \{\ λ x y,
  y = (x - a)^^n \}\.
Proof.
  intros a n x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma3' : ∀ a c n, Function \{\ λ x y,
  y = c * (x - a)^^n \}\.
Proof.
  intros a c n x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma4 : ∀ a x n, \{\ λ x y,
  y = (x - a)^^n \}\ [x] = (x - a)^^n.
Proof.
  intros a x n. apply f_x; try apply Lemma3.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma4' : ∀ a c x n, \{\ λ x y,
  y = c * (x - a)^^n \}\ [x] = c * (x - a)^^n.
Proof.
  intros a c x n. apply f_x; try apply Lemma3'.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma5 : ∀ a, Function \{\ λ x y : R, y = x - a \}\.
Proof.
  intros a x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma6 : ∀ a x, \{\ λ x y, y = x - a \}\ [x] = x - a.
Proof.
  intros a x. apply f_x; try apply Lemma5.
  apply AxiomII'. reflexivity.
Qed.

(* 幂函数连续 *)
Lemma Lemma7 : ∀ a x0 n, limit
  \{\ λ x y, y = (x - a)^^n \}\ x0 ((x0 - a)^^n).
Proof.
  intros a x0 n. generalize dependent x0.
  induction n as [|n IHn].
  - intro x0. split; try apply Lemma3. exists 2.
    split; try lra. split.
    + intros x H0. simpl. apply AxiomII. exists 1.
      apply AxiomII'. reflexivity.
    + intros ε H0. exists 1. split; try lra.
      intros x H1. rewrite Lemma4.
      simpl. apply Abs_R. lra.
  - intros x0. simpl.
    assert (H0 : \{\ λ x y, y = (x - a) * (x - a)^^n \}\ =
      \{\ λ x y, y = x - a \}\ **
      \{\ λ x y, y = (x - a)^^n \}\).
    { apply AxiomI. intros [x y]. split; intros I1;
      applyAxiomII' I1; apply AxiomII'.
      - repeat split.
        + apply AxiomII. exists (x - a).
          apply AxiomII'. reflexivity.
        + apply AxiomII. exists ((x - a)^^n).
          apply AxiomII'. reflexivity.
        + rewrite Lemma6. rewrite Lemma4.
          assumption.
      - destruct I1 as [I1 [I2 I3]].
        rewrite I3. rewrite Lemma6. rewrite Lemma4.
        reflexivity. }
    rewrite H0. apply Theorem3_7_3; auto.
    split; try apply Lemma5. exists 1.
    split; [lra | split].
    + intros x I1. apply AxiomII.
      exists (x - a). apply AxiomII'. reflexivity.
    + intros ε I1. assert (I2 : 1 > 0). lra.
      generalize (Lemma1 ε 1 I1 I2).
      intros [δ [I3 [I4 I5]]]. exists δ.
      split; [lra | intros x I6].
      rewrite Lemma6.
      assert (I7 : x - a - (x0 - a) = x - x0).
      field. rewrite I7. lra.
Qed.

(* 幂函数导数 *)
Lemma Lemma5_4 : ∀ a x0 n, derivative
  \{\ λ x y, y = (x - a)^^n \}\ x0
  (INR n * ((x0 - a) ^^ (n - 1))).
Proof.
  intros a x0 n.
  split; try apply Lemma3. split.
  - exists 1. split; try lra.
    intros x I1. apply AxiomII.
    exists ((x - a)^^n). apply AxiomII'.
    reflexivity.
  - rewrite Lemma4.
    assert (H1 : \{\ λ x y,
      y = (\{\ λ x1 y0, y0 = (x1 - a) ^^ n \}\ [x]
      - (x0 - a) ^^ n) / (x - x0) \}\
      = \{\ λ x y, y = ((x - a) ^^ n
        - (x0 - a) ^^ n) / (x - x0) \}\).
    { apply AxiomI. intros [x y].
      split; intros I1; apply AxiomII'; applyAxiomII' I1.
      - rewrite Lemma4 in I1. assumption.
      - rewrite Lemma4. assumption. }
    rewrite H1. clear H1.
    assert (H0 : ∀ x0 n, Function
      \{\ λ x y, y = ((x - a)^^n
        - (x0 - a)^^n) / (x - x0) \}\).
    { intros x1 n0. intros x2 y2 z2 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption. }
    induction n as [|n IHn].
    + split; auto. exists 1. split; try lra; split.
      * intros x I1. simpl. apply AxiomII.
        exists ((1 - 1) / (x - x0)).
        apply AxiomII'. reflexivity.
      * intros ε I1. exists (1/2).
        split; try lra. intros x [I2 I3].
        apply Abs_not_eq_0 in I2.
        assert (I4 : \{\ λ x1 y,
          y = ((x1 - a)^^0 - (x0 - a)^^0)
            / (x1 - x0) \}\ [x] = 0).
        { apply f_x; auto. apply AxiomII'.
          simpl. field. assumption. }
        rewrite I4. simpl. apply Abs_R. lra.
    + assert (H1 : ∀ x, ((x - a)^^S n -
        (x0 - a)^^S n) / (x - x0)
        = (x - a)^^n * (x - x0) / (x - x0)
          + (x0 - a) * ((x - a)^^n -
          (x0 - a)^^n) / (x - x0)).
      { intros x. simpl.
        assert (I1 : (x - a) * (x - a)^^n
          - (x0 - a) * (x0 - a)^^n
          = (x - a)^^n * (x - x0) +
          (x0 - a) * ((x - a)^^n - (x0 - a)^^n)).
        field. rewrite I1. rewrite Rdiv_plus_distr.
        reflexivity. }
      assert (H2 : (INR (S n) * (x0 - a)^^(S n - 1))
        = (x0 - a)^^n + INR n * (x0 - a)^^n).
      { rewrite S_INR.
        assert (I1 : (S n - 1 = n)%nat).
        { simpl. rewrite minus_n_O.
          reflexivity. }
        rewrite I1. field. }
      rewrite H2. clear H2.
      assert (H2 : Function \{\ λ x y, y =
        (x - a) ^^ n * (x - x0) / (x - x0) \}\).
      { intros x y z I1 I2. applyAxiomII' I1;
        applyAxiomII' I2. rewrite I2; assumption. }
      assert (H3 : Function \{\ λ x y, y =
          (x0 - a) * ((x - a)^^n
            - (x0 - a)^^n) / (x - x0) \}\).
      { intros x y z I1 I2. applyAxiomII' I1;
        applyAxiomII' I2. rewrite I2; assumption. }
      assert (H4: ∀ x, \{\ λ x1 y0,
        y0 = (x1 - a)^^n * (x1 - x0)
         / (x1 - x0) \}\ [x]
        = (x - a)^^n * (x - x0) / (x - x0)).
      { intro x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      assert (H5 : ∀ x, \{\ λ x1 y0,
        y0 = (x0 - a) * ((x1 - a)^^n - (x0 - a)^^n)
        / (x1 - x0) \}\ [x] = (x0 - a) *
          ((x - a)^^n - (x0 - a)^^n) / (x - x0)).
      { intro x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      assert (H6 : \{\ λ x y, y =
        ((x - a)^^S n - (x0 - a)^^S n) / (x - x0) \}\
        = \{\ λ x y, y = (x - a) ^^ n * (x - x0)
          / (x - x0) \}\ \+ \{\ λ x y, y =
          (x0 - a) * ((x - a)^^n -
          (x0 - a)^^n) / (x - x0) \}\).
      { apply AxiomI. intros [x y]; split; intro I1;
        applyAxiomII' I1; apply AxiomII'.
        - repeat split.
          + apply AxiomII.
            exists ((x - a)^^n * (x - x0) / (x - x0)).
            apply AxiomII'. reflexivity.
          + apply AxiomII.
            exists ((x0 - a) * ((x - a)^^n
              - (x0 - a)^^n) / (x - x0)).
            apply AxiomII'. reflexivity.
          + rewrite H4; rewrite H5.
            rewrite I1. apply H1.
        - destruct I1 as [I1 [I4 I5]].
          rewrite H4 in I5.
          rewrite H5 in I5.
          rewrite I5. symmetry.
          apply H1. }
      rewrite H6. clear H6.
      apply Theorem3_7_1.
      * generalize (Lemma7 a x0 n). unfold limit.
        intros [I2 [δ' [I3 [I4 I5]]]].
        split; auto. exists δ'.
        split; [assumption | split].
        -- intros x I1. apply AxiomII.
          exists ((x - a)^^n * (x - x0) / (x - x0)).
          apply AxiomII'. reflexivity.
        -- intros ε I1. apply I5 in I1 as I6.
          destruct I6 as [δ [I6 I7]].
          exists δ; split; [assumption | intros x I8].
          apply I7 in I8 as I9.
          rewrite Lemma4 in I9.
          apply Lemma2 in I8 as [I8 I10].
          rewrite H4.
          assert (I11 : (x - a)^^n * (x - x0) / (x - x0)
            = (x - a)^^n). field; auto.
          rewrite I11. assumption.
      * assert (I1 : INR n * (x0 - a) ^^ n =
          (x0 - a) * (INR n * (x0 - a) ^^ (n - 1))).
        { destruct n.
          - simpl. field.
          - rewrite <- Rmult_assoc.
            rewrite (Rmult_comm (x0 - a) (INR (S n))).
            rewrite Rmult_assoc.
            simpl. rewrite <- minus_n_O.
            reflexivity. }
        rewrite I1. clear I1.
        assert (I1 : Function \{\ λ x y : R,
          y = x0 - a \}\).
        { intros x1 y1 z1 I1 I2.
          applyAxiomII' I1; applyAxiomII' I2.
          rewrite I2. assumption. }
        assert (I2 : ∀ x, \{\ λ x y : R,
          y = x0 - a \}\[x] = x0 - a).
        { intros x. apply f_x; auto.
          apply AxiomII'. reflexivity. }
        assert (I3 : Function \{\ λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) \}\).
        { intros x1 y1 z1 J1 J2.
          applyAxiomII' J1; applyAxiomII' J2.
          rewrite J2. assumption. }
        assert (I4 : ∀ x, \{\ λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) \}\[x]
          = ((x - a)^^n - (x0 - a)^^n) / (x - x0)).
        { intros x. apply f_x; auto.
          apply AxiomII'. reflexivity. }
        assert (I5 : \{\ λ x y, y = (x0 - a) *
          ((x - a)^^n - (x0 - a)^^n) / (x - x0) \}\
          = \{\ λ x y, y = x0 - a \}\ ** \{\ λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) \}\).
        { apply AxiomI. intros [x y]; split; intro J1;
          applyAxiomII' J1; apply AxiomII'.
          - rewrite I4. rewrite I2.
            repeat split.
            + apply AxiomII. exists (x0 - a).
              apply AxiomII'. reflexivity.
            + apply AxiomII.
              exists (((x - a)^^n -
                (x0 - a)^^n) / (x - x0)).
              apply AxiomII'. reflexivity.
            + lra.
          - destruct J1 as [J1 [J2 J3]].
            rewrite I4 in J3. rewrite I2 in J3.
            lra. }
        rewrite I5. clear I5.
        apply Theorem3_7_3; auto.
        split; auto. exists 2. split; [lra | split].
        -- intros x J1. apply AxiomII.
          exists (x0 - a). apply AxiomII'.
          reflexivity.
        -- intros ε J1. exists 1.
          split; [lra | intros x J2].
          rewrite I2. apply Abs_R. lra.
Qed.

Lemma Lemma5_5 : ∀ a c x0 n, derivative \{\ λ x y,
  y = c * (x - a)^^n \}\ x0
  (c * INR n  * (x0 - a)^^(n - 1)).
Proof.
  intros a c x0 n.
  assert (H0 : ∃ u, u = \{\ λ x y, y = (x - a)^^n \}\).
  { exists \{\ λ x y, y = (x - a)^^n \}\.
    reflexivity. }
  destruct H0 as [u H0].
  assert (H1 : \{\ λ x y, y = c * (x - a)^^n \}\ =
    \{\ λ x y, y = c * u[x] \}\).
  { rewrite H0. apply AxiomI. intros [x y]; split;
    intros I1; applyAxiomII' I1; apply AxiomII'.
    - rewrite Lemma4. assumption.
    - rewrite Lemma4 in I1. assumption. }
  rewrite H1.
  generalize (Lemma5_4 a x0 n). intro H2.
  rewrite <- H0 in H2.
  assert (H3 : c * INR n * (x0 - a)^^(n - 1) =
    c * u '[x0]).
  { apply derEqual in H2 as H3.
    rewrite H3. field. }
  rewrite H3. apply Lemma5_3.
  exists (INR n * (x0 - a) ^^ (n - 1)).
  assumption.
Qed.

Lemma Lemma5_9 : ∀ f g x0 y0, Function g ->
  (∃ δ, 0 < δ /\ (∀ x, x ∈ Neighbor x0 δ ->
    x ∈ dom[g] /\ f[x] = g[x]))
  -> derivative f x0 y0 -> derivative g x0 y0.
Proof.
  intros f g x0 y0 H0 [δ [H1 H2]] H3.
  split; [auto | split].
  - exists δ. split; auto.
    intros x I1. apply H2. assumption.
  - unfold limit. unfold derivative in H3.
    destruct H3 as [H3 [[δ' [I1 I2]] I3]].
    unfold limit in I3.
    destruct I3 as [I3 [δ1' [I4 [I5 I6]]]].
    split.
    + intros x y z J1 J2. applyAxiomII' J1;
      applyAxiomII' J2. rewrite J2; assumption.
    + exists δ1'. split; [auto | split].
      * intros x J1. apply AxiomII.
        exists ((g [x] - g [x0]) / (x - x0)).
        apply AxiomII'. reflexivity.
      * intros ε J1. apply I6 in J1 as J2.
        destruct J2 as [δ1 [[J2 J3] J4]].
        generalize (Lemma1 δ δ1 H1 J2).
        intros [δ2 [J5 [J6 J7]]].
        exists δ2. split; try lra.
        intros x J8.
        assert (J9 : 0 < Abs [x - x0] < δ1). lra.
        apply J4 in J9.
        assert (J10 : \{\ λ x y, y =
          (f [x] - f [x0]) / (x - x0) \}\ [x]
          = (f [x] - f [x0]) / (x - x0)).
        { apply f_x; auto. apply AxiomII'.
          reflexivity. }
        rewrite J10 in J9.
        clear J10.
        assert (J10 : \{\ λ x y, y =
          (g [x] - g [x0]) / (x - x0) \}\ [x]
          = (g [x] - g [x0]) / (x - x0)).
        { apply f_x.
          - intros x1 y1 z1 K1 K2.
            applyAxiomII' K1;
            applyAxiomII' K2.
            rewrite K2; assumption.
          - apply AxiomII'. reflexivity. }
        rewrite J10. assert (J11 : x ∈ Neighbor x0 δ).
        { apply AxiomII. lra. }
        apply H2 in J11 as [J11 J12].
        rewrite <- J12.
        assert (J13 : x0 ∈ Neighbor x0 δ).
        { apply AxiomII. apply Abs_R. lra. }
        apply H2 in J13 as [J14 J15].
        rewrite <- J15. assumption.
Qed.

(* 常数函数导数 *)
Lemma Lemma5_10 : ∀ c, Function \{\ λ x y : R, y = c \}\.
Proof.
  intros c x y z I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2; assumption.
Qed.

Lemma Lemma5_11 : ∀ c x, \{\ λ x y : R, y = c \}\[x] = c.
Proof.
  intros c x. apply f_x;
  try apply Lemma5_10.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma5_12 : ∀ c x0, derivative
  \{\ λ x y, y = c \}\ x0 0.
Proof.
  intros c x.
  split; [apply Lemma5_10 | split].
  - exists 1. split; [lra | intros x0 I1].
    apply AxiomII. exists c.
    apply AxiomII'. reflexivity.
  - unfold limit. split.
    + intros x1 y1 z1 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption.
    + exists 2. split; [lra | split].
      * intros x0 I1. apply AxiomII.
        exists ((\{\ λ _ y1 : R, y1 = c \}\ [x0]
          - \{\ λ _ y1 : R, y1 = c \}\ [x]) /
          (x0 - x)).
        apply AxiomII'. reflexivity.
      * intros ε I1. exists 1.
        split; [lra | intros x0 I2].
        -- assert (I3 : \{\ λ x1 y, y =
           (\{\ λ _ y0 : R, y0 = c \}\ [x1]
           - \{\ λ _ y0 : R,y0 = c \}\ [x]) /
           (x1 - x) \}\ [x0] = 0).
          { apply f_x.
            - intros x1 y1 z1 J1 J2.
              applyAxiomII' J1; applyAxiomII' J2.
              rewrite J2; assumption.
            - apply AxiomII'.
              rewrite Lemma5_11. rewrite Lemma5_11.
              apply Lemma2 in I2.
              field. apply I2. }
          rewrite I3. apply Abs_R. lra.
Qed.

Lemma Lemma5_19 : ∀ c x0, limit \{\ λ _ y : R, y = c\}\ x0 c.
Proof.
  intros c x0. split.
  - apply Lemma5_10.
  - exists 2. split; [lra | split].
    + intros x H0. apply AxiomII.
      exists c. apply AxiomII'.
      reflexivity.
    + intros ε H0. exists 1.
      split; [lra | intros x H1].
      rewrite Lemma5_11. apply Abs_R.
      lra.
Qed.

Lemma Lemma7' : ∀ a c x0 n, limit
  \{\ λ x y, y = c * (x - a)^^n \}\ x0 (c * (x0 - a)^^n).
Proof.
  intros a c x0 n.
  assert (H0 : \{\ λ x y, y = c * (x - a)^^n \}\ =
    \{\ λ x y, y = c \}\ ** \{\ λ x y, y = (x - a)^^n \}\).
  { apply AxiomI. intros [x y];
    split; intro I1;
    applyAxiomII' I1; apply AxiomII'.
    - repeat split.
      + apply AxiomII. exists c.
        apply AxiomII'. reflexivity.
      + apply AxiomII. exists ((x - a) ^^ n).
        apply AxiomII'. reflexivity.
      + rewrite Lemma5_11. rewrite Lemma4.
        assumption.
    - destruct I1 as [I1 [I2 I3]].
      rewrite I3. rewrite Lemma5_11.
      rewrite Lemma4. reflexivity. }
  rewrite H0. apply Theorem3_7_3.
  - apply Lemma5_19.
  - apply Lemma7.
Qed.          
          


End A5_2.

Export A5_2.

