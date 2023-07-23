Require Export A_4_2.

Module A5_1.

(* 5.1 导数的概念 *)

(* 定义：导数 *)
Definition derivative (f : Fun) (x0 y0' : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f]) /\
  (limit \{\ λ x y, y = (f[x] - f[x0]) / (x - x0) \}\ x0 y0').

Definition derivative' (f : Fun) (x0 y0': R) :=
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f]) /\
  (limit \{\ λ h y, y = (f[x0 + h] - f[x0]) / h \}\ 0 y0').


(* 两个导数定义等价 *) 
Theorem Equaderivative : ∀ (f : Fun) (x0 y0': R),  
   derivative f x0 y0' <-> derivative' f x0 y0'. 
Proof.
  intros. split; intros.
  - unfold derivative in H. destruct H as [H[]].
    unfold derivative'. split; auto. 
    split; auto.  
    unfold limit in *.
    destruct H1 as [H1 [δ[H8[H9 H10]]]].
    unfold Contain in H9.    
    split; auto.
    + unfold Function. intros. applyAxiomII' H2. 
      applyAxiomII' H3. rewrite H2; auto.
    + exists δ. split; auto. split. 
      unfold Contain. intros. apply AxiomII.
      exists ((f [x0 + z] - f [x0]) / z).
      apply AxiomII'; auto.
      intros. apply H10 in H2. destruct H2 as[δ0].
      exists δ0. destruct H2.  split; auto.
      intros. replace (x - 0) with x in H4.
      assert (0 < Abs [x0 + x - x0]< δ0).  
      { assert ((x0 + x - x0) = x).
        rewrite Rplus_comm. lra.
        rewrite H5. auto. }
        pose proof (H3 (x0 + x)). apply H6 in H5.
      assert (Function \{\ λ h0 y ,y = (f [x0 + h0] - f [x0]) / h0 \}\).
      { unfold Function. intros. applyAxiomII' H7. 
        applyAxiomII' H11. rewrite H11. auto. }
      assert (\{\ λ h0 y ,y = (f [x0 + h0] - f [x0]) / h0 \}\ [x] = (f [x0 + x] - f [x0]) / x). 
      { apply f_x; auto. apply AxiomII'; simpl; auto.  }
      rewrite H11. 
      assert (\{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\ [x0 + x] = 
      (f [x0 + x] - f [x0]) / (x0 + x -x0)).
      { apply f_x; auto. apply AxiomII'; simpl; auto. }
      rewrite H12 in H5.
      assert (x0 + x - x0 = x). { lra. }
      rewrite H13 in H5. auto. lra.
   - unfold derivative. unfold derivative' in H.
     destruct H as [H [H1 H2]]. 
     unfold limit in H2. destruct H2.
     assert (Function \{\ λ x y ,y = (f [x] - f [x0]) / (x - x0) \}\).
     { unfold Function. intros. applyAxiomII' H3.
       applyAxiomII' H4. rewrite H4. auto. }
     repeat split; auto.
     destruct H2 as[δ' [H4 [H5]]].
     exists δ'. split; auto. split.
     + unfold Contain. intros. apply AxiomII. 
       exists ((f[z] - f[x0]) /(z - x0)).
       apply AxiomII'; auto.
     + intros. apply H2 in H6. 
       destruct H6 as [δ [H6 H7]].
       exists δ. split; auto.
       intros. assert (x - x0 = x - x0 -0).
       { lra. }
       rewrite H9 in H8. apply H7 in H8.
       assert (\{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\ [x - x0] = (f [x0 + x -x0] - f [x0]) / (x - x0)).
       { apply f_x; auto. apply AxiomII'. 
         replace (x0 + (x - x0)) with (x0 + x - x0).
         auto. lra.  }
       replace (x0 + x - x0) with x in H10. rewrite H10 in H8.
       assert (\{\ λ x1 y,y = (f [x1] - f [x0]) / (x1 - x0) \}\ [x] = (f [x] - f [x0]) / (x - x0)).
       { apply f_x; auto. apply AxiomII'; auto.  }
       rewrite H11; auto. lra.
Qed.

(* 在某去心邻域导数 *)
Definition derivativeU (f : Fun) (x0 y0' δ' : R) :=
  Function f /\ (δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f]) /\
  (limit \{\ λ x y, y = (f[x] - f[x0]) / (x - x0) \}\ x0 y0').

(* 定义：可导 *)
Definition derivable (f : Fun) (x0 : R) := (∃ y0', derivative f x0 y0').
(***cc***)
Definition derivable' (f : Fun) (x0 : R) := (∃ y0', derivative' f x0 y0').

(* 右导数 *)
Definition derivative_pos (f : Fun) (x0 y0' : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ rightNeighbor x0 δ' ⊂ dom[f]) /\
  (limit_pos \{\ λ x y, y = (f[x] - f[x0]) / (x - x0) \}\ x0 y0').

(* 左导数 *)
Definition derivative_neg (f : Fun) (x0 y0' : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ leftNeighbor x0 δ' ⊂ dom[f]) /\
  (limit_neg \{\ λ x y, y = (f[x] - f[x0]) / (x - x0) \}\ x0 y0').

(* 导数唯一性 *)
Theorem derivativeUnique : ∀ (f : Fun) (x0 A B : R),
  derivative f x0 A -> derivative f x0 B -> A = B.
Proof.
  unfold derivative.
  intros f x0 A B [H0 [H1 H2]] [H3 [H4 H5]].
  eapply Theorem3_2; eauto.
Qed.

Definition der f x := cR \{ λ y', derivative f x y' \}.

Notation "f '[ x ]" := (der f x)(at level 20).

Theorem derEqual : ∀ (f : Fun) (x y' : R),
  derivative f x y' -> f '[x] = y'.
Proof.
  intros f x y' H0. 
  assert (H1 : derivative f x (f '[x])).
  { assert (I1 : NotEmpty \{ λ y', derivative f x y' \}).
    { exists y'. apply AxiomII. assumption. }
    apply AxiomcR in I1. applyAxiomII I1.
    assumption. }
  eapply derivativeUnique; eauto.
Qed.

Theorem derEqual_l : ∀ (f : Fun) (x y' : R),
  f '[x] = y' -> derivative f x y'.
Proof.
  intros f x y' H0. unfold der in H0.
  
  
 
  unfold cR in H0. unfold c in H0.
  destruct tf. 
  destruct (constructive_indefinite_description _ n) in H0.
  simpl in H0. applyAxiomII i. rewrite H0 in i; auto.
   
Admitted.
  

Theorem derEqual' : ∀ (f : Fun) (x y' : R),
  derivative' f x y' -> f '[x] = y'.
Proof.
  intros f x y' H0.
  rewrite <- Equaderivative in H0.
  apply derEqual in H0.
  apply H0.
Qed.

(* 定理5.1 可导一定连续 *)
Theorem Theorem5_1 : ∀ (f : Fun) (x0 : R), 
  derivable f x0 -> Continuous f x0.
Proof.
  intros f x0 [y0' [H0 [[δ' [H1 H2]] H3]]].
  assert (H4 : x0 ∈ dom[f]).
  { apply H2. apply AxiomII. rewrite Abs_ge; lra. }
  split; auto. unfold limit. split; auto. exists δ'.
  assert (H5 : Neighbor0 x0 δ' ⊂ dom[ f]).
  { intros x I1. apply H2. applyAxiomII I1.
    apply AxiomII. apply I1. }
  repeat split; auto. intros ε H6.
  unfold limit in H3. destruct H3 as [H3 [δ1' [H7 [H8 H9]]]].
  assert (H10 : ∀ ε', ε' > 0 -> ∃ δ, 0 < δ /\ (∀ x, 0 < Abs [x - x0] < δ
    -> (ε' + Abs[y0']) * Abs[x - x0] < ε)).
  { intros ε' I1. exists (ε / (ε' + Abs[y0'])).
    assert (I4 : 0 < ε' + Abs [y0']).
    { generalize (Abs_Rge0 y0'). intro J1. lra. }
    split.
    - apply Rdiv_lt_0_compat; auto.
    - intros x [I2 I3]. 
      apply Rmult_lt_compat_l with (r := ε' + Abs [y0']) in I3; auto.
      assert (I5 : (ε' + Abs [y0']) * (ε / (ε' + Abs [y0'])) = ε).
      { field; try lra. }
      rewrite I5 in I3. assumption. }
  assert (H11 : 1 > 0). lra.
  apply H10 in H11 as H12.
  destruct H12 as [δ0 [H12 H16]].
  apply H9 in H11 as H13.
  destruct H13 as [δ1 [H13 H14]].
  assert (H15 : ∃ δ, 0 < δ /\ δ < δ' /\ δ < δ1 /\ δ < δ0).
  { destruct (Rlt_or_le δ' δ1) as [I1 | I1].
    - destruct (Rlt_or_le δ' δ0) as [I2 | I2].
      + exists (δ' / 2). lra.
      + exists (δ0 / 2). repeat split; lra.
    - destruct (Rlt_or_le δ1 δ0) as [I2 | I2].
      + exists (δ1 / 2). lra.
      + exists (δ0 / 2). repeat split; lra. }
  destruct H15 as [δ [H17 [H18 [H19 H20]]]].
  exists δ. split; try lra. intros x H21.
  assert (H22 : 0 < Abs [x - x0] < δ0). lra.
  assert (H23 : 0 < Abs [x - x0] < δ1). lra.
  apply H16 in H22. apply H14 in H23.
  assert (H24 : \{\ λ x y, y = (f [x] - f [x0]) / (x - x0) \}\ [x]
      = (f [x] - f [x0]) / (x - x0)).
  { apply f_x; try apply H3. apply AxiomII'. reflexivity. }
  rewrite H24 in H23. clear H24.
  generalize (Abs_abs_minus' ((f [x] - f [x0]) / (x - x0)) y0').
  intro H24. assert (H25 : x - x0 <> 0).
  { apply Abs_not_eq_0. lra. }
  rewrite Abs_div in H24; auto.
  assert (H26 : Abs [f [x] - f [x0]] / Abs [x - x0] < 1 + Abs [y0']).  lra.
  assert (H27 : Abs [f [x] - f [x0]] < (1 + Abs [y0']) * Abs [x - x0]).
  { apply Rmult_lt_compat_r with (r := Abs [x - x0]) in H26; try apply H21.
    assert (I1 : Abs [f [x] - f [x0]] / Abs [x - x0] * Abs [x - x0]
      = Abs [f [x] - f [x0]]).
    { field. lra. }
    rewrite I1 in H26. assumption. }
  lra.
Qed.

(* 导函数 *)
Definition derivativeFun (f : Fun) := \{\ λ x y, derivative f x y \}\.

Definition derivativeFun' (f : Fun) := \{\ λ x y, derivative' f x y \}\.

Theorem derivativeIsFun : ∀ (f : Fun), Function (derivativeFun f).
Proof.
  intro f. unfold Function. intros x y z H1 H2. applyAxiomII' H1.
  applyAxiomII' H2. destruct H1 as [H1 [H3 H4]].
  destruct H2 as [H2 [H5 H6]]. eapply Theorem3_2; eauto.
Qed.

Theorem derivativeIsFun' : ∀ (f : Fun), Function (derivativeFun' f).
Proof.
  intro f. unfold Function. intros x y z H1 H2. applyAxiomII' H1.
  applyAxiomII' H2. 
  destruct H1 as [H [H3 H4]].
  destruct H2 as [H0 [H5 H6]]. eapply Theorem3_2; eauto.
Qed. 

(* 极值 *)
Definition localMax (f : Fun) (x0 : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f] /\
  (∀ x, x ∈ Neighbor x0 δ' -> f[x] <= f[x0])).

Definition localMin (f : Fun) (x0 : R) :=
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor x0 δ' ⊂ dom[f] /\
  (∀ x, x ∈ Neighbor x0 δ' -> f[x0] <= f[x])).

Definition extremum (f : Fun) (x0 : R) := localMax f x0 \/ localMin f x0.

(* 费马定理 *)
Theorem Theorem5_3 : ∀ (f : Fun) (x0 : R), derivable f x0
  -> extremum f x0 -> derivative f x0 0.
Proof.
  intros f x0 [y0' [H0 [[δ' [H2 H3]] H4]]] H5.
  assert (H6 : Function \{\ λ x y, y =
    (f [x] - f [x0]) / (x - x0) \}\).
  { intros x y z I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H7 : ∀ x, \{\ λ x y, y =
    (f [x] - f [x0]) / (x - x0) \}\ [x]
    = (f [x] - f [x0]) / (x - x0)).
  { intro x. apply f_x; auto. apply AxiomII'. reflexivity. }
  assert (H8 : y0' = 0).
  { apply NNPP. intro I1. apply Rdichotomy in I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2 (\{\ λ x y, y =
        (f [x] - f [x0]) / (x - x0) \}\) x0 y0' H4 I1).
      intro I2. assert (I3 : 0 < ((-y0') / 2) < -y0'). lra.
      apply I2 in I3 as I4. destruct I4 as [δ [I4 I5]].
      clear I2. destruct H5 as [I6 | I6].
      + destruct I6 as [I6 [δ0' [I7 [I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0' / 2). repeat split; lra.
          - exists (δ / 2). repeat split; lra. }
        destruct I10 as [δ0 [I10 [I11 I12]]].
        assert (I13 : x0 - δ0/2 ∈ Neighbor x0 δ0').
        { apply AxiomII. apply Abs_R. lra. }
        assert (I14 : x0 - δ0/2 ∈ Neighbor0 x0 δ).
        { apply AxiomII. split.
          - apply Abs_not_eq_0. lra.
          - apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14.
        rewrite H7 in I14.
        assert (I15 : (f [x0 - δ0 / 2] - f [x0])
          / (x0 - δ0 / 2 - x0) < 0). lra.
        assert (I16 : x0 - δ0 / 2 - x0 < 0). lra.
        apply Rmult_lt_gt_compat_neg_l
          with (r := x0 - δ0 / 2 - x0) in I15; auto.
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 - δ0 / 2 - x0) *
          ((f [x0 - δ0 / 2] - f [x0]) /
          (x0 - δ0 / 2 - x0)) = f [x0 - δ0 / 2] - f [x0]).
        { field. lra. }
        rewrite I17 in I15. lra.
      + destruct I6 as [I6 [δ0' [I7 [I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0' / 2). repeat split; lra.
          - exists (δ / 2). repeat split; lra. }
        destruct I10 as [δ0 [I10 [I11 I12]]].
        assert (I13 : x0 + δ0/2 ∈ Neighbor x0 δ0').
        { apply AxiomII. apply Abs_R. lra. }
        assert (I14 : x0 + δ0/2 ∈ Neighbor0 x0 δ).
        { apply AxiomII. split.
          - apply Abs_not_eq_0. lra.
          - apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14.
        rewrite H7 in I14.
        assert (I15 : (f [x0 + δ0 / 2] - f [x0])
          / (x0 + δ0 / 2 - x0) < 0). lra.
        assert (I16 : x0 + δ0 / 2 - x0 > 0). lra.
        apply Rmult_lt_compat_l with (r := x0 + δ0 / 2 - x0)
          in I15; auto. rewrite Rmult_0_r in I15.
        assert (I17 : (x0 + δ0 / 2 - x0) *
          ((f [x0 + δ0 / 2] - f [x0]) /
          (x0 + δ0 / 2 - x0)) = f [x0 + δ0 / 2] - f [x0]).
        { field. lra. }
        rewrite I17 in I15. lra.
    - generalize (Theorem3_4_1 (\{\ λ x y, y =
        (f [x] - f [x0]) / (x - x0) \}\) x0 y0' H4 I1).
      intro I2. assert (I3 : 0 < (y0' / 2) < y0'). lra.
      apply I2 in I3 as I4. destruct I4 as [δ [I4 I5]].
      clear I2. destruct H5 as [I6 | I6].
      + destruct I6 as [I6 [δ0' [I7 [I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0' / 2). repeat split; lra.
          - exists (δ / 2). repeat split; lra. }
        destruct I10 as [δ0 [I10 [I11 I12]]].
        assert (I13 : x0 + δ0/2 ∈ Neighbor x0 δ0').
        { apply AxiomII. apply Abs_R. lra. }
        assert (I14 : x0 + δ0/2 ∈ Neighbor0 x0 δ).
        { apply AxiomII. split.
          - apply Abs_not_eq_0. lra.
          - apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14.
        rewrite H7 in I14.
        assert (I15 : (f [x0 + δ0 / 2] - f [x0])
          / (x0 + δ0 / 2 - x0) > 0). lra.
        assert (I16 : x0 + δ0 / 2 - x0 > 0). lra.
        apply Rmult_lt_compat_l with (r := x0 + δ0 / 2 - x0)
          in I15; auto. rewrite Rmult_0_r in I15.
        assert (I17 : (x0 + δ0 / 2 - x0) *
          ((f [x0 + δ0 / 2] - f [x0]) /
          (x0 + δ0 / 2 - x0)) = f [x0 + δ0 / 2] - f [x0]).
        { field. lra. }
        rewrite I17 in I15. lra.
      + destruct I6 as [I6 [δ0' [I7 [I8 I9]]]].
        assert (I10 : ∃ δ0, 0 < δ0 /\ δ0 < δ0' /\ δ0 < δ).
        { destruct (Rlt_or_le δ0' δ) as [J1 | J1].
          - exists (δ0' / 2). repeat split; lra.
          - exists (δ / 2). repeat split; lra. }
        destruct I10 as [δ0 [I10 [I11 I12]]].
        assert (I13 : x0 - δ0/2 ∈ Neighbor x0 δ0').
        { apply AxiomII. apply Abs_R. lra. }
        assert (I14 : x0 - δ0/2 ∈ Neighbor0 x0 δ).
        { apply AxiomII. split.
          - apply Abs_not_eq_0. lra.
          - apply Abs_R. lra. }
        apply I9 in I13. apply I5 in I14.
        rewrite H7 in I14.
        assert (I15 : (f [x0 - δ0 / 2] - f [x0])
          / (x0 - δ0 / 2 - x0) > 0). lra.
        assert (I16 : x0 - δ0 / 2 - x0 < 0). lra.
        apply Rmult_lt_gt_compat_neg_l
          with (r := x0 - δ0 / 2 - x0) in I15; auto.
        rewrite Rmult_0_r in I15.
        assert (I17 : (x0 - δ0 / 2 - x0) *
          ((f [x0 - δ0 / 2] - f [x0]) /
          (x0 - δ0 / 2 - x0)) = f [x0 - δ0 / 2] - f [x0]).
        { field. lra. }
        rewrite I17 in I15. lra. }
  split; auto; split.
  - exists δ'. split; auto.
  - rewrite <- H8. assumption.
Qed.


End A5_1.

Export A5_1.