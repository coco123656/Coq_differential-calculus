Require Export A_6_3.

Module A6_4.


Theorem Div_inequal_neg : ∀(a b:R), b > 0 -> a / b <= 0
-> a <= 0.
Proof.
  intros. destruct (Rle_lt_dec a 0); auto.
  unfold Rdiv in H0. apply Rinv_0_lt_compat in H.
  pose proof (Rmult_gt_0_compat a (/b) r H).
  lra.
Qed.

Theorem Div_inequal_neg' : ∀(a b:R), b > 0 -> a / b < 0
-> a < 0.
Proof.
  intros. apply Rinv_0_lt_compat in H.
  destruct (Rle_lt_dec a 0); auto.
  unfold Rdiv in H0. 
  apply Rle_lt_or_eq_dec in r.
  destruct r; auto. rewrite e in H0. lra. 
  pose proof (Rmult_gt_0_compat a (/b) r H).
  lra.
Qed.

Theorem Div_inequal_neg'' : ∀(a b:R), b < 0 -> a / b < 0
-> a > 0.
Proof.
  intros. apply Rinv_lt_0_compat in H.
  destruct (Rle_lt_dec a 0); auto.
  unfold Rdiv in H0. 
  apply Rle_lt_or_eq_dec in r.
  destruct r. cut(a * / b > 0); intros.
  lra. apply Rmult_le_le; tauto. 
  rewrite e in H0. lra.
Qed. 


Theorem Div_inequal_pos : ∀(a b:R), b > 0 -> a / b >= 0
-> a >= 0.
Proof.
  intros. destruct (Rge_gt_dec a 0); auto.
  unfold Rdiv in H0. apply Rinv_0_lt_compat in H.
  assert(a * / b < 0).
  apply Rmult_le_gr; auto. lra.
Qed.

Theorem Div_inequal_pos' : ∀(a b:R), b > 0 -> a / b > 0
-> a > 0.
Proof.
  intros. apply Rinv_0_lt_compat in H.
  destruct (Rle_lt_dec a 0); auto.
  unfold Rdiv in H0. 
  apply Rle_lt_or_eq_dec in r.
  destruct r; auto. assert(a * / b < 0).
  apply Rmult_le_gr; auto. lra.
  rewrite e in H0. lra.
Qed.

Theorem Div_inequal_pos'' : ∀(a b:R), b < 0 -> a / b > 0
-> a < 0.
Proof.
  intros. apply Rinv_lt_0_compat in H.
  destruct (Rle_lt_dec a 0).
  unfold Rdiv in H0. 
  apply Rle_lt_or_eq_dec in r.
  destruct r; auto. 
  rewrite e in H0. lra.
  cut(a * / b < 0); intros.
  lra. rewrite Rmult_comm.
  apply Rmult_le_gr; tauto.  
Qed.

(* 极值的第一充分条件 *)
Theorem Theorem6_11 : ∀ (f : Fun) (x0 : R), Continuous f x0 -> 
(∃δ : R, δ > 0 /\ (∀x : R, x ∈ Neighbor0 x0 δ -> derivable f x)->
((∀x, x ∈ \( x0 - δ,x0 \) -> f '[x] <= 0) /\ (∀x, x ∈ \( x0,x0 + δ \) -> f '[x] >= 0) -> localMin f x0) /\ ((∀x, x ∈ \( x0 - δ,x0 \) -> f '[x] >= 0) /\ (∀x, x ∈ \( x0,x0 + δ \) -> f '[x] <= 0) -> localMax f x0)). 
Proof.
  intros. pose proof H as H'. red in H. destruct H.
  red in H0. destruct H0 as [H1[δ'[H2[H3 H4]]]].
  exists δ'. intros. split.
  - intros. red.  
    split; auto. destruct H0 as [_ H0].
    exists δ'. repeat split; auto. unfold Contain in *.
    intros. applyAxiomII H6. pose proof (Abs_Rge0 (z-x0)).
    destruct H7. apply H3. apply AxiomII.
    split; auto. apply <- Abs_eq_0 in H7. 
    apply Rminus_diag_uniq in H7.
    rewrite H7; auto. intros.
    apply Theorem4_1 in H'. 
    applyAxiomII H6. pose proof (Abs_Rge0 (x-x0)).
    destruct H7. 
    + assert (x ∈ Neighbor0 x0 δ').
      { apply AxiomII. split; auto.  } 
      apply H0 in H8 as H8'.
      apply Theorem5_1 in H8' as H9.
      apply Abs_R in H6. 
      destruct H6. apply Abs_not_eq_0 in H7.
      destruct H5 as [H5 H5'].
      apply Rdichotomy in H7. destruct H7.
      * assert(I1: ContinuousClose f x x0).
        { red. split.
          - red. intros. apply Theorem5_1.
          apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R.
          lra. 
          - apply Theorem4_1 in H9. split; tauto. }
        assert(I2: (∀ x', x < x' < x0 -> derivable f x')).
        { intros. apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R; lra.  }
        assert(I3:  x < x0). lra. 
        pose proof (Theorem6_2 f x x0 I3 I1 I2). 
        destruct H11 as [ξ[[H11 H12] H13]]. 
        apply derEqual in H13. 
        cut(ξ ∈ \( x0 - δ', x0 \)). intros.
        apply H5 in H14. rewrite H13 in H14.
        assert((x0 - x) > 0). lra. 
        apply (Div_inequal_neg (f [x0] - f [x]) (x0-x)) in H15; auto.
        lra. apply AxiomII. lra.
      * assert(I1: ContinuousClose f x0 x).
        { red. split.
          - red. intros. apply Theorem5_1.
          apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R.
          lra. 
          - apply Theorem4_1 in H9. split; tauto. }
        assert(I2: (∀ x', x0 < x' < x -> derivable f x')).
        { intros. apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R; lra.  }
        assert(I3:  x0 < x). lra. 
        pose proof (Theorem6_2 f x0 x I3 I1 I2). 
        destruct H11 as [ξ[[H11 H12] H13]]. 
        apply derEqual in H13. 
        cut(ξ ∈ \( x0 , x0 + δ' \)). intros.
        apply H5' in H14. rewrite H13 in H14.
        assert((x - x0) > 0). lra.  
        apply (Div_inequal_pos (f [x] - f [x0]) (x-x0)) in H15; auto.
        lra. apply AxiomII. lra.
    + apply Abs_eq_0 in H7. apply Rminus_diag_uniq in H7.
      rewrite H7. lra.
  - intros. red.  
    split; auto. destruct H0 as [_ H0].
    exists δ'. repeat split; auto. unfold Contain in *.
    intros. applyAxiomII H6. pose proof (Abs_Rge0 (z-x0)).
    destruct H7. apply H3. apply AxiomII.
    split; auto. apply <- Abs_eq_0 in H7. 
    apply Rminus_diag_uniq in H7.
    rewrite H7; auto. intros.
    apply Theorem4_1 in H'. 
    applyAxiomII H6. pose proof (Abs_Rge0 (x-x0)).
    destruct H7. 
    + assert (x ∈ Neighbor0 x0 δ').
      { apply AxiomII. split; auto.  } 
      apply H0 in H8 as H8'.
      apply Theorem5_1 in H8' as H9.
      apply Abs_R in H6. 
      destruct H6. apply Abs_not_eq_0 in H7.
      destruct H5 as [H5 H5'].
      apply Rdichotomy in H7. destruct H7.
      * assert(I1: ContinuousClose f x x0).
        { red. split.
          - red. intros. apply Theorem5_1.
          apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R.
          lra. 
          - apply Theorem4_1 in H9. split; tauto. }
        assert(I2: (∀ x', x < x' < x0 -> derivable f x')).
        { intros. apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R; lra.  }
        assert(I3:  x < x0). lra. 
        pose proof (Theorem6_2 f x x0 I3 I1 I2). 
        destruct H11 as [ξ[[H11 H12] H13]]. 
        apply derEqual in H13. 
        cut(ξ ∈ \( x0 - δ', x0 \)). intros.
        apply H5 in H14. rewrite H13 in H14.
        assert((x0 - x) > 0). lra. 
        apply (Div_inequal_pos (f [x0] - f [x]) (x0-x)) in H15; auto.
        lra. apply AxiomII. lra.
      * assert(I1: ContinuousClose f x0 x).
        { red. split.
          - red. intros. apply Theorem5_1.
          apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R.
          lra. 
          - apply Theorem4_1 in H9. split; tauto. }
        assert(I2: (∀ x', x0 < x' < x -> derivable f x')).
        { intros. apply H0. apply AxiomII. split.
          apply Abs_not_eq_0; lra. apply Abs_R; lra.  }
        assert(I3:  x0 < x). lra. 
        pose proof (Theorem6_2 f x0 x I3 I1 I2). 
        destruct H11 as [ξ[[H11 H12] H13]]. 
        apply derEqual in H13. 
        cut(ξ ∈ \( x0 , x0 + δ' \)). intros.
        apply H5' in H14. rewrite H13 in H14.
        assert((x - x0) > 0). lra.  
        apply (Div_inequal_neg (f [x] - f [x0]) (x-x0)) in H15; auto.
        lra. apply AxiomII. lra.
    + apply Abs_eq_0 in H7. apply Rminus_diag_uniq in H7.
      rewrite H7. lra.
Qed.


    
(* 极值的第二充分条件 *)
Theorem Theorem6_12 : ∀ (f : Fun) (x0 : R), Function f -> (∃δ : R, δ > 0 /\ (∀x : R, x ∈ Neighbor x0 δ -> derivable f x)) /\ derivable (dN f 1) x0 /\ f '[x0] =0 /\ (dN f 2)[x0] <> 0 -> ((dN f 2)[x0] > 0 -> 
localMin f x0 ) /\ ((dN f 2)[x0] < 0 -> localMax f x0).
Proof.
  intros f x0 H' H. pose proof (Theorem6_9 f 2 x0).
  destruct H as [H[H1[H2 H3]]]. 
  destruct H as [δ'[H H4]]. 
  red in H1. destruct H1 as [y0''].
  assert(L1: x0 ∈ dom[ dN f 2]).
  { apply AxiomII.  exists y0''.
    apply AxiomII'. auto. } 
  assert(L: (0 < 2)%nat). auto. apply H0 in L as L'; auto.
  clear H0. destruct L' as [o [H5 H6]].  
  assert(L2: ∀x:R, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [0%nat] = f[x0]).
    { intros. Function_ass; simpl; lra.  }
   assert(L4: ∀x:R, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [1%nat] = f '[x0]*(x-x0)).
   { intros. Function_ass. rewrite Lemma5_8. simpl. lra. }
   assert(L5: ∀x:R, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [2%nat] = (dN f 2) [x0]*(1/2)*(x - x0) ^^ 2).
   { intros. Function_ass. rewrite Lemma5_8. simpl. lra. }
   
   assert(L0: ∀x : R, (x - x0) ^^ 2 >= 0).
   { intros. red. destruct(classic (x = x0)).
     right. rewrite H0. simpl. lra.
     left. red. simpl. rewrite Rmult_1_r. 
     apply R_sqr.Rsqr_pos_lt. lra. }
  split.
  - intros. red. repeat split; auto.
    apply Lemma5_6' in L1. 
    destruct L1 as [δ1[L1 L3]]. 
    red in H5. destruct H5 as [H5[H7 H8]].
    destruct H8 as [H8 H9]. red in H9.
    destruct H9 as [H9[δ2'[H10[H11 H12]]]].
    assert(H0': (dN f 2) [x0] * (1/2) > 0).
    lra. apply H12 in H0' as H13. clear H12.
    destruct H13 as [δ2[[H13 H15] H14]]. 
    pose proof (Lemma1 δ1 δ2). apply H12 in L1 as H12'; auto.
    clear H12. destruct H12' as [δ[H12[H16 H17]]]. 
    exists δ. repeat split; auto.
    apply L3 in L. intros z L'. apply L.
    applyAxiomII L'. apply AxiomII. lra.
    intros. pose proof (H6 x).
    clear H6. simpl in H19.
    rewrite (L2 x) in H19. 
    rewrite (L4 x) in H19.
    rewrite (L5 x) in H19.    
    rewrite H2 in H19. rewrite Rmult_0_l in H19.
    applyAxiomII H18. pose proof (Abs_Rge0 (x - x0)).
    destruct H6.
    + assert(L0': (x - x0) ^^ 2 > 0).
      { simpl. apply Abs_not_eq_0 in H6. 
        rewrite Rmult_1_r. apply Rdichotomy in H6. 
        destruct H6. apply Rmult_le_le; auto.
        apply Rmult_gt_0_compat; auto. }
      assert(0 < Abs [x - x0] < δ2). lra.
      apply H14 in H20. clear H14. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ 2 \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ 2). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ 2 \}\ [x] = (x - x0) ^^ 2).
      intros. rewrite H14; auto. Function_ass. } 
      rewrite L6 in H20. clear L6. apply Abs_not_eq_0 in H6.
      rewrite Rminus_0_r in H20.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ 2)).
      assert(H21:(dN f 2) [x0] * (1 / 2) * (x - x0) ^^ 2 > 0).
      { apply Rmult_gt_0_compat; lra.  }
      destruct H14.
      apply Abs_not_eq_0 in H14.
      apply Rdichotomy in H14. 
      apply Abs_R in H20. unfold Rdiv in H20.
      destruct H20.  
      destruct H14. 
      * apply (Rmult_lt_compat_r ((x - x0) ^^ 2)) in H20; auto.
        rewrite Rmult_assoc in H20. rewrite Rinv_l in H20.
        rewrite Rmult_1_r in H20. lra. lra.
      * assert(o [x] > 0). 
        { apply (Div_inequal_pos' o [x] ((x - x0) ^^ 2)); auto. } lra.
      * rewrite <- Abs_eq_0 in H14. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H14.
          destruct H14. auto. 
          apply Rinv_0_lt_compat in L0'. lra. }
        rewrite H22 in H19. lra.   
    + rewrite <- Abs_eq_0 in H6.
      apply Rminus_diag_uniq in H6. rewrite H6. lra.
  - intros. red. repeat split; auto.
    apply Lemma5_6' in L1. 
    destruct L1 as [δ1[L1 L3]]. 
    red in H5. destruct H5 as [H5[H7 H8]].
    destruct H8 as [H8 H9]. red in H9.
    destruct H9 as [H9[δ2'[H10[H11 H12]]]].
    assert(H0': - (dN f 2) [x0] * (1/2) > 0).
    lra. apply H12 in H0' as H13. clear H12.
    destruct H13 as [δ2[[H13 H15] H14]]. 
    pose proof (Lemma1 δ1 δ2). apply H12 in L1 as H12'; auto.
    clear H12. destruct H12' as [δ[H12[H16 H17]]]. 
    exists δ. repeat split; auto.
    apply L3 in L. intros z L'. apply L.
    applyAxiomII L'. apply AxiomII. lra.
    intros. pose proof (H6 x).
    clear H6. simpl in H19.
    rewrite (L2 x) in H19. 
    rewrite (L4 x) in H19.
    rewrite (L5 x) in H19.    
    rewrite H2 in H19. rewrite Rmult_0_l in H19.
    applyAxiomII H18. pose proof (Abs_Rge0 (x - x0)).
    destruct H6.
    + assert(L0': (x - x0) ^^ 2 > 0).
      { simpl. apply Abs_not_eq_0 in H6. 
        rewrite Rmult_1_r. apply Rdichotomy in H6. 
        destruct H6. apply Rmult_le_le; auto.
        apply Rmult_gt_0_compat; auto. }
      assert(0 < Abs [x - x0] < δ2). lra.
      apply H14 in H20. clear H14. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ 2 \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ 2). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ 2 \}\ [x] = (x - x0) ^^ 2).
      intros. rewrite H14; auto. Function_ass. } 
      rewrite L6 in H20. clear L6. apply Abs_not_eq_0 in H6.
      rewrite Rminus_0_r in H20.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ 2)).
      assert(H21:(dN f 2) [x0] * (1 / 2) * (x - x0) ^^ 2 < 0).
      { apply Rmult_le_gr; lra.  }
      destruct H14.
      apply Abs_not_eq_0 in H14.
      apply Rdichotomy in H14. 
      apply Abs_R in H20. unfold Rdiv in H20.
      destruct H20.  
      destruct H14. 
      * assert(o [x] < 0). 
        { apply (Div_inequal_neg' o [x] ((x - x0) ^^ 2)); auto. } lra. 
      * apply (Rmult_lt_compat_r ((x - x0) ^^ 2)) in H22; auto.
        rewrite Rmult_assoc in H22. rewrite Rinv_l in H22.
        rewrite Rmult_1_r in H22. lra. lra. 
      * rewrite <- Abs_eq_0 in H14. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H14.
          destruct H14. auto. 
          apply Rinv_0_lt_compat in L0'. lra.  } 
        rewrite H22 in H19. lra.   
    + rewrite <- Abs_eq_0 in H6. 
      apply Rminus_diag_uniq in H6. rewrite H6. lra.
Qed. 

      
(* 极值的第三充分条件 *)
Theorem Theorem6_13 : ∀ (f : Fun) (x0 : R) (n : nat), Function f /\ (0 < n)%nat /\ (∃k:nat,n = (2 * k)%nat) -> (∃δ : R, δ > 0 /\  Neighbor x0 δ ⊂ dom[dN f (n-1)]) -> derivable (dN f n) x0  -> (∀ k, (0 < k < n)%nat 
-> (dN f k) [x0] = 0) ->((dN f n) [x0] <> 0) 
-> ((dN f n)[x0] > 0 -> localMin f x0) /\ ((dN f n)[x0] < 0 -> localMax f x0).
Proof.
  intros. destruct H as [H[H4[k H0']]]. 
  destruct H0 as [δ' [H6 H5]].
  red in H1. destruct H1 as [y0n H1].
  red in H1. destruct H1 as [H1[H7 H8]].
  destruct H7 as [δ1[H7 H9]].
  assert(H0: x0 ∈ dom[ dN f n]).
  { apply H9. apply AxiomII. 
    apply Abs_R; lra. }
  pose proof (Theorem6_9 f n x0); auto.
  apply H10 in H4 as H10'; auto. clear H10.
  destruct H10' as [o[H10 H11]]. 
  assert(L0: ∀x : R, ∀ k : nat, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [k] = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k ).
  { intros. Function_ass. } 
  assert(L: ∀k : nat,(0 < k < n)%nat -> ∀x : R, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [k] = 0).
  { intros. rewrite L0. unfold Rdiv. apply H2 in H12.
    rewrite H12. lra. }
  assert(L4: ∀x : R, Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ n = Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) + \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ [n]). 
  { intros. induction n. inversion H4.
    simpl.  apply Rplus_eq_compat_r.
    assert(H12: n = (n-0)%nat). 
    { induction n. simpl; auto. simpl; auto. }
      rewrite <- H12. auto.  } 
  assert(L4': ∀k : nat,(0 <= k < n)%nat -> ∀x : R, Σ
  \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\
              (k) = f[x0] ).
   { intros. induction k0. destruct H12. 
     simpl. rewrite L0. simpl. lra. simpl.
     assert((0 <= k0 < n)%nat).
     { split. apply Nat.le_0_l. destruct H12.
       pose proof (Nat.lt_succ_diag_r k0).
       apply (Nat.lt_trans k0 (S k0) n); auto.  }
     apply IHk0 in H13. rewrite H13.
     assert((0 < S k0 < n)%nat).
     { split.  apply gt_Sn_O. tauto. }
     cut(∀x : R,\{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\[S k0] = 0). intros.  
     pose proof (H15 x). rewrite H16. lra.
     apply L; auto. } 
    assert(H12: (0 <= (n-1) < n)%nat).
    { split. apply Nat.le_0_l. 
      apply Nat.sub_lt; auto. }
  split. 
  - intros. repeat split; auto. 
    apply Lemma5_6' in H0 as L3. 
    destruct L3 as [δ2[L1 L2]]. 
    apply L2 in H4 as L2'. 
    red in H10. destruct H10 as [H10[H14 [H15 H16]]].
    red in H16. destruct H16 as [J1[δ3'[J2[J3 J4]]]].
    assert(H16: (dN f n) [x0] / INR (n !) > 0).
    { unfold Rdiv. apply Rmult_gt_0_compat; auto.
      apply Rinv_0_lt_compat. apply lt_0_INR.
      apply Lemma6_3_1. }
     apply J4 in H16 as H16'. clear J4. 
    destruct H16' as [δ3[[J4 J6] J5]]. 
    pose proof (Lemma1 δ2 δ3). apply H17 in L1 as H17'; auto.
    clear H17. destruct H17' as [δ[H17[J7 J8]]].  
    exists δ. repeat split; auto.
    intros z K. apply L2'. applyAxiomII K. 
    apply AxiomII. lra.  
    intros.  pose proof (H11 x).
    clear H11. rewrite (L4 x) in H19. 
    rewrite (L0 x n) in H19. 
    assert(Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
   { apply L4'; auto.  } 
   rewrite H11 in H19. clear H11 L4' L4 L0.
   applyAxiomII H18. pose proof (Abs_Rge0 (x - x0)).
   destruct H11.
   + assert(H20: (x - x0) ^^ n > 0).
     { rewrite H0'. rewrite Lemma_pow2.  
       apply Lemma_pow3. simpl. 
       apply Abs_not_eq_0 in H11. 
       rewrite Rmult_1_r. apply Rdichotomy in H11. 
       destruct H11. apply Rmult_le_le; auto.
       apply Rmult_gt_0_compat; auto.  }
     assert(0 < Abs [x - x0] < δ3). lra.
     apply J5 in H21. clear J5. 
     assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H22; auto. Function_ass. }  
      rewrite L6 in H21. clear L6. apply Abs_not_eq_0 in H11.
      rewrite Rminus_0_r in H21.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)).
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n > 0).
      { apply Rmult_gt_0_compat; lra.  }
      destruct H22. 
      apply Abs_not_eq_0 in H22.
      apply Rdichotomy in H22. 
      apply Abs_R in H21. unfold Rdiv in H21.
      destruct H21. destruct H22. 
      * apply (Rmult_lt_compat_r ((x - x0) ^^ n)) in H21; auto.
        rewrite Rmult_assoc in H21. rewrite Rinv_l in H21.
        rewrite Rmult_1_r in H21. lra. lra.
      * assert(o [x] > 0). 
        { apply (Div_inequal_pos' o [x] ((x - x0) ^^ n)); auto. } lra.
      * rewrite <- Abs_eq_0 in H22. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H22.
          destruct H22. auto. 
          apply Rinv_0_lt_compat in H20. lra. }
        rewrite H23 in H19. lra.   
    + rewrite <- Abs_eq_0 in H11.
      apply Rminus_diag_uniq in H11. rewrite H11. lra.
  - intros. repeat split; auto. 
    apply Lemma5_6' in H0 as L3. 
    destruct L3 as [δ2[L1 L2]]. 
    apply L2 in H4 as L2'. 
    red in H10. destruct H10 as [H10[H14 [H15 H16]]].
    red in H16. destruct H16 as [J1[δ3'[J2[J3 J4]]]].
    assert(H16: - (dN f n) [x0] / INR (n !) > 0).
    { unfold Rdiv. apply Rmult_gt_0_compat; auto.
      apply Ropp_gt_lt_0_contravar; auto.
      apply Rinv_0_lt_compat. apply lt_0_INR.
      apply Lemma6_3_1. }
     apply J4 in H16 as H16'. clear J4. 
    destruct H16' as [δ3[[J4 J6] J5]]. 
    pose proof (Lemma1 δ2 δ3). apply H17 in L1 as H17'; auto.
    clear H17. destruct H17' as [δ[H17[J7 J8]]].  
    exists δ. repeat split; auto.
    intros z K. apply L2'. applyAxiomII K. 
    apply AxiomII. lra.  
    intros.  pose proof (H11 x).
    clear H11. rewrite (L4 x) in H19. 
    rewrite (L0 x n) in H19. 
    assert(Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
   { apply L4'; auto.  } 
   rewrite H11 in H19. clear H11 L4' L4 L0.
   applyAxiomII H18. pose proof (Abs_Rge0 (x - x0)).
   destruct H11.
   + assert(H20: (x - x0) ^^ n > 0).
     { rewrite H0'. rewrite Lemma_pow2.  
       apply Lemma_pow3. simpl. 
       apply Abs_not_eq_0 in H11. 
       rewrite Rmult_1_r. apply Rdichotomy in H11. 
       destruct H11. apply Rmult_le_le; auto.
       apply Rmult_gt_0_compat; auto.  }
     assert(0 < Abs [x - x0] < δ3). lra.
     apply J5 in H21. clear J5. 
     assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H22; auto. Function_ass. }  
      rewrite L6 in H21. clear L6. apply Abs_not_eq_0 in H11.
      rewrite Rminus_0_r in H21.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)). 
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n < 0).
      { apply Rmult_le_gr; lra. }
      destruct H22. 
      apply Abs_not_eq_0 in H22.
      apply Rdichotomy in H22. 
      apply Abs_R in H21. unfold Rdiv in H21.
      destruct H21. destruct H22. 
      * assert(o [x] < 0). 
        { apply (Div_inequal_neg' o [x] ((x - x0) ^^ n)); auto. } lra. 
      * apply (Rmult_lt_compat_r ((x - x0) ^^ n)) in H23; auto.
        rewrite Rmult_assoc in H23. rewrite Rinv_l in H23.
        rewrite Rmult_1_r in H23. lra. lra. 
      * rewrite <- Abs_eq_0 in H22. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H22.
          destruct H22. auto. 
          apply Rinv_0_lt_compat in H20. lra.  } 
        rewrite H23 in H19. lra.   
    + rewrite <- Abs_eq_0 in H11. 
      apply Rminus_diag_uniq in H11. rewrite H11. lra.
Qed.

Theorem Theorem6_13' : ∀ (f : Fun) (x0 : R) (n : nat), Function f /\ (0 < n)%nat /\ (∃k:nat,n = (2 * k + 1)%nat) -> (∃δ : R, δ > 0 /\  Neighbor x0 δ ⊂ dom[dN f (n-1)]) -> derivable (dN f n) x0  -> (∀ k, (0 < k < n)%nat 
-> (dN f k) [x0] = 0) ->((dN f n) [x0] <> 0) 
-> ~ (extremum f x0).
Proof.
  intros. intro. red in H4.
  destruct H as [H[H5 H6]].
  assert(L0: ∀x : R, ∀ k : nat, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [k] = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k ).
  { intros. Function_ass. } 
  assert(L: ∀k : nat,(0 < k < n)%nat -> ∀x : R, \{\ λ(k : nat)(v : R),v = (dN f k) [x0] / INR (k !) * (x - x0) ^^ k \}\ [k] = 0).
  { intros. rewrite L0. unfold Rdiv. apply H2 in H7.
    rewrite H7. lra. }
  assert(L4: ∀x : R, Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ n = Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) + \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ [n]). 
  { intros. induction n. inversion H5.
    simpl.  apply Rplus_eq_compat_r.
    assert(H12: n = (n-0)%nat). 
    { induction n. simpl; auto. simpl; auto. }
    rewrite <- H12. auto.  } 
  assert(L4': ∀k : nat,(0 <= k < n)%nat -> ∀x : R, Σ
  \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\
              (k) = f[x0] ).
   { intros. induction k. destruct H7. 
     simpl. rewrite L0. simpl. lra. simpl.
     assert((0 <= k < n)%nat).
     { split. apply Nat.le_0_l. destruct H7.
       pose proof (Nat.lt_succ_diag_r k).
       apply (Nat.lt_trans k (S k) n); auto.  }
     apply IHk in H8. rewrite H8.
     assert((0 < S k < n)%nat).
     { split.  apply gt_Sn_O. tauto. }
     cut(∀x : R,\{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\[S k] = 0). intros.  
     pose proof (H10 x). rewrite H11. lra.
     apply L; auto. } 
  assert(L5: (0 <= (n-1) < n)%nat).
    { split. apply Nat.le_0_l. 
      apply Nat.sub_lt; auto. }
  red in H1. destruct H1 as [y0'].
  red in H1. destruct H1 as [H1 [[δ1 [K1 K3]] K2]].
  assert(L1: x0 ∈ dom[ dN f n]).
  { apply K3. apply AxiomII. 
    apply Abs_R; lra. } 
  destruct H6 as [k].
  pose proof (Theorem6_9 f n x0); auto.
  apply H7 in H5 as H7'; auto. clear H7.
  destruct H7' as [o[I1 I2]].
  red in I1. destruct I1 as [I1[I3[I4 I5]]]. 
  clear I4. red in I5. destruct I5 as [I4[δ2'[I5[_ I7]]]].
  destruct H4. 
  - red in H4. destruct H4 as [_[δ'[H9 [H7 H8]]]] .
    apply Rdichotomy in H3. destruct H3.
    + assert(H16: - (dN f n) [x0] / INR (n !) > 0).
      { unfold Rdiv. apply Rmult_gt_0_compat; auto.
        apply Ropp_gt_lt_0_contravar; auto.
        apply Rinv_0_lt_compat. apply lt_0_INR.
        apply Lemma6_3_1. }
      apply I7 in H16. clear I7. 
      destruct H16 as [δ2[[H10 H11] H12]].  
      assert(L6: ∃x :R, x ∈ Neighbor x0 δ' /\ (x - x0) < 0 /\ 0 < Abs [x - x0] < δ2).
      { pose proof (Lemma1 δ' δ2). apply H4 in H9 as H4'; auto.
        clear H4. destruct H4' as [δ[H4 [H13 H14]]].
        exists (x0 - δ). split. apply AxiomII.
        rewrite Abs_lt; lra. split. lra.
        rewrite Abs_lt; lra. }  
      destruct L6 as [x[H13 [H14 H15]]]. 
      apply H8 in H13 as H13'. clear H8.
      apply H12 in H15. clear H12. 
      assert(H4: Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
      { apply L4'; auto.  } pose proof (L4 x).
      rewrite H4 in H8. rewrite (L0 x) in H8.
      pose proof (I2 x). rewrite H8 in H12.
      clear H4 H8 L4 L4' L L0. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H4; auto. Function_ass. } 
      rewrite L6 in H15. clear L6. 
      rewrite Rminus_0_r in H15.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)).
      assert((x - x0) ^^ n < 0).
      { rewrite H6. rewrite Lemma_pow1. 
        rewrite Rmult_comm. rewrite Lemma_pow2.
        replace ((x - x0) ^^ 1) with (x - x0).
        apply Rmult_le_gr. split; auto. 
        apply Lemma_pow3. simpl. rewrite Rmult_1_r.
        apply Rmult_le_le; tauto. simpl. lra.  }  
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n > 0).
      { apply Rmult_le_le; lra. }
      apply Abs_R in H15. destruct H15.
      destruct H4. apply Abs_not_eq_0 in H4.
      apply Rdichotomy in H4. destruct H4.
      * apply (Div_inequal_neg'' o [x] _) in H8; auto.
        lra. 
      * apply (Div_inequal_pos'' o [x] _) in H8 as H8'; auto.  
        apply (Rmult_lt_gt_compat_neg_l ((x - x0) ^^ n)) in H16; auto.
        unfold Rdiv in H16.
        rewrite <- Rmult_assoc in H16. rewrite Rmult_comm in H16.
        rewrite <- Rmult_assoc in H16. 
        rewrite Rinv_l in H16; lra.
      * rewrite <- Abs_eq_0 in H4. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H4.
          destruct H4. auto. 
          apply Rinv_lt_0_compat in H8. lra.  }
        rewrite H17 in H12. lra.
     + assert(H16: (dN f n) [x0] / INR (n !) > 0).
      { unfold Rdiv. apply Rmult_gt_0_compat; auto.
        apply Rinv_0_lt_compat. apply lt_0_INR.
        apply Lemma6_3_1. } 
      apply I7 in H16. clear I7. 
      destruct H16 as [δ2[[H10 H11] H12]].  
      assert(L6: ∃x :R, x ∈ Neighbor x0 δ' /\ (x - x0) > 0 /\ 0 < Abs [x - x0] < δ2).
      { pose proof (Lemma1 δ' δ2). apply H4 in H9 as H4'; auto.
        clear H4. destruct H4' as [δ[H4 [H13 H14]]].
        exists (x0 + δ). split. apply AxiomII.
        apply Abs_R; lra. split. lra. split.
        apply Abs_not_eq_0; lra. apply Abs_R; lra. }  
      destruct L6 as [x[H13 [H14 H15]]]. 
      apply H8 in H13 as H13'. clear H8.
      apply H12 in H15. clear H12. 
      assert(H4: Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
      { apply L4'; auto.  } pose proof (L4 x).
      rewrite H4 in H8. rewrite (L0 x) in H8.
      pose proof (I2 x). rewrite H8 in H12.
      clear H4 H8 L4 L4' L L0. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H4; auto. Function_ass. } 
      rewrite L6 in H15. clear L6. 
      rewrite Rminus_0_r in H15.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)).
      assert((x - x0) ^^ n > 0).
      { rewrite H6. rewrite Lemma_pow1. 
        rewrite Rmult_comm. rewrite Lemma_pow2.
        replace ((x - x0) ^^ 1) with (x - x0). 
        apply Rmult_gt_0_compat; auto.  
        apply Lemma_pow3. simpl. rewrite Rmult_1_r.
        apply Rmult_gt_0_compat; tauto. simpl. lra.  }  
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n > 0).
      { apply Rmult_gt_0_compat; lra. }
      apply Abs_R in H15. destruct H15.
      destruct H4. apply Abs_not_eq_0 in H4.
      apply Rdichotomy in H4. destruct H4.
      * apply (Div_inequal_neg' o [x] _) in H8 as H8'; auto.
        apply (Rmult_lt_compat_r ((x - x0) ^^ n)) in H15; auto.
        unfold Rdiv in H15. rewrite Rmult_assoc in H15.
        rewrite Rinv_l in H15. lra. apply Rgt_not_eq; auto.
      * apply (Div_inequal_pos' o [x] _) in H8 as H8'; auto. lra.  
      * rewrite <- Abs_eq_0 in H4. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H4.
          destruct H4. auto. 
          apply Rinv_0_lt_compat in H8. lra.  }
        rewrite H17 in H12. lra.
  - red in H4. destruct H4 as [_[δ'[H9 [H7 H8]]]] .
    apply Rdichotomy in H3. destruct H3.
    + assert(H16: - (dN f n) [x0] / INR (n !) > 0).
      { unfold Rdiv. apply Rmult_gt_0_compat; auto.
        apply Ropp_gt_lt_0_contravar; auto.
        apply Rinv_0_lt_compat. apply lt_0_INR.
        apply Lemma6_3_1. }
      apply I7 in H16. clear I7. 
      destruct H16 as [δ2[[H10 H11] H12]].  
      assert(L6: ∃x :R, x ∈ Neighbor x0 δ' /\ (x - x0) > 0 /\ 0 < Abs [x - x0] < δ2).
      { pose proof (Lemma1 δ' δ2). apply H4 in H9 as H4'; auto.
        clear H4. destruct H4' as [δ[H4 [H13 H14]]].
        exists (x0 + δ). split. apply AxiomII.
        apply Abs_R; lra. split. lra. split.
        apply Abs_not_eq_0; lra. apply Abs_R; lra. }  
      destruct L6 as [x[H13 [H14 H15]]]. 
      apply H8 in H13 as H13'. clear H8.
      apply H12 in H15. clear H12. 
      assert(H4: Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
      { apply L4'; auto.  } pose proof (L4 x).
      rewrite H4 in H8. rewrite (L0 x) in H8.
      pose proof (I2 x). rewrite H8 in H12.
      clear H4 H8 L4 L4' L L0. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H4; auto. Function_ass. } 
      rewrite L6 in H15. clear L6. 
      rewrite Rminus_0_r in H15.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)).
       assert((x - x0) ^^ n > 0).
      { rewrite H6. rewrite Lemma_pow1. 
        rewrite Rmult_comm. rewrite Lemma_pow2.
        replace ((x - x0) ^^ 1) with (x - x0).
        apply Rmult_gt_0_compat; auto.  
        apply Lemma_pow3. simpl. rewrite Rmult_1_r.
        apply Rmult_gt_0_compat; tauto. simpl. lra.  }  
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n < 0).
      { apply Rmult_le_gr; lra. }
      apply Abs_R in H15. destruct H15.
      destruct H4. apply Abs_not_eq_0 in H4.
      apply Rdichotomy in H4. destruct H4.
      * apply (Div_inequal_neg' o [x] _) in H8 as H8'; auto.
        apply (Rmult_lt_compat_r ((x - x0) ^^ n)) in H16; auto.
        unfold Rdiv in H16. rewrite Rmult_assoc in H16.
        rewrite Rinv_l in H16. lra. apply Rgt_not_eq; auto.
      * apply (Div_inequal_pos' o [x] _) in H8 as H8'; auto.
        apply (Rmult_lt_compat_r ((x - x0) ^^ n)) in H16; auto.
        unfold Rdiv in H16. rewrite Rmult_assoc in H16.
        rewrite Rinv_l in H16. lra. apply Rgt_not_eq; auto.
      * rewrite <- Abs_eq_0 in H4. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H4.
          destruct H4. auto. 
          apply Rinv_0_lt_compat in H8. lra.  }
        rewrite H17 in H12. lra.
     + assert(H16: (dN f n) [x0] / INR (n !) > 0).
      { unfold Rdiv. apply Rmult_gt_0_compat; auto.
        apply Rinv_0_lt_compat. apply lt_0_INR.
        apply Lemma6_3_1. } 
      apply I7 in H16. clear I7. 
      destruct H16 as [δ2[[H10 H11] H12]].  
      assert(L6: ∃x :R, x ∈ Neighbor x0 δ' /\ (x - x0) < 0 /\ 0 < Abs [x - x0] < δ2).
      { pose proof (Lemma1 δ' δ2). apply H4 in H9 as H4'; auto.
        clear H4. destruct H4' as [δ[H4 [H13 H14]]].
        exists (x0 - δ). split. apply AxiomII.
        apply Abs_R; lra. split. lra. split.
        apply Abs_not_eq_0; lra. apply Abs_R; lra. }  
      destruct L6 as [x[H13 [H14 H15]]]. 
      apply H8 in H13 as H13'. clear H8.
      apply H12 in H15. clear H12. 
      assert(H4: Σ \{\ λ(k0 : nat)(v : R),v = (dN f k0) [x0] / INR (k0 !) * (x - x0) ^^ k0 \}\ (n-1) = f [x0]).
      { apply L4'; auto.  } pose proof (L4 x).
      rewrite H4 in H8. rewrite (L0 x) in H8.
      pose proof (I2 x). rewrite H8 in H12.
      clear H4 H8 L4 L4' L L0. 
      assert(L6:\{\ λ x y,y = o [x] / \{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] \}\ [x] = o [x] / (x - x0) ^^ n). { Function_ass. 
      cut(\{\ λ x1 y0,y0 = (x1 - x0) ^^ n \}\ [x] = (x - x0) ^^ n).
      intros. rewrite H4; auto. Function_ass. } 
      rewrite L6 in H15. clear L6. 
      rewrite Rminus_0_r in H15.
      pose proof (Abs_Rge0 (o [x] / (x - x0) ^^ n)).
      assert((x - x0) ^^ n < 0).
      { rewrite H6. rewrite Lemma_pow1. 
        rewrite Rmult_comm. rewrite Lemma_pow2.
        replace ((x - x0) ^^ 1) with (x - x0).
        apply Rmult_le_gr. split; auto. 
        apply Lemma_pow3. simpl. rewrite Rmult_1_r.
        apply Rmult_le_le; tauto. simpl. lra.  }   
      assert(H21':(dN f n) [x0] * / INR (n !) * (x - x0) ^^ n < 0).
      { rewrite Rmult_comm.
        apply Rmult_le_gr. split; auto. 
        apply Rmult_gt_0_compat; auto. 
        apply Rinv_0_lt_compat. apply lt_0_INR.
         apply Lemma6_3_1. }
      apply Abs_R in H15. destruct H15.
      destruct H4. apply Abs_not_eq_0 in H4.
      apply Rdichotomy in H4. destruct H4.
      * apply (Div_inequal_neg'' o [x] _) in H8 as H8'; auto. 
        apply (Rmult_lt_gt_compat_neg_l ((x - x0) ^^ n)) in H15; auto.
        unfold Rdiv in H15.
        rewrite <- Rmult_assoc in H15. rewrite Rmult_comm in H15.
        rewrite Rinv_r_simpl_m in H15; lra.
      * apply (Div_inequal_pos'' o [x] _) in H8 as H8'; auto. lra.  
      * rewrite <- Abs_eq_0 in H4. 
        assert(o [x] = 0). 
        { apply Rmult_integral in H4.
          destruct H4. auto.  
          apply Rinv_lt_0_compat in H8. lra.  }
        rewrite H17 in H12. lra.
Qed. 
        


End A6_4.

Export A6_4.    
      
       
      
    
     
  

   
    
                        
      
  


 
  
  
  
  
  
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
  