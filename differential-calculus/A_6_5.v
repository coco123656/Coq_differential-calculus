Require Export A_6_4.

Module A6_5.

(* 定义： 凸函数 *)
Definition Convex_function (f : Fun) (I : sR) := Function f /\ 
I ⊂ dom[f] /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
-> f[ξ*x1 + (1-ξ)*x2] <= ξ*f[x1] + (1-ξ)*f[x2]).


(* 定义： 凹函数 *)
Definition Concave_function (f : Fun) (I : sR) := Function f /\ 
I ⊂ dom[f] /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
-> f[ξ*x1 + (1-ξ)*x2] >= ξ*f[x1] + (1-ξ)*f[x2]).


(* 定义： 严格凸函数 *)
Definition StrictlyConvex_function (f : Fun) (I : sR) := Function f /\ 
I ⊂ dom[f] /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
-> f[ξ*x1 + (1-ξ)*x2] < ξ*f[x1] + (1-ξ)*f[x2]).

(* 定义： 严格凹函数 *)
Definition StrictlyConcave_function (f : Fun) (I : sR) := Function f /\ 
I ⊂ dom[f] /\ (∀ (x1 x2 ξ: R), x1 ∈ I -> x2 ∈ I-> ξ ∈ \(0, 1\)
-> f[ξ*x1 + (1-ξ)*x2] > ξ*f[x1] + (1-ξ)*f[x2]).

Lemma LemmaRdiv : ∀(a b c : R), a = b / c -> c <> 0 -> a * c = b.
Proof.
  intros a b c H H1. apply (Rmult_eq_compat_r c) in H.
  unfold Rdiv in H. rewrite Rmult_assoc in H.
  rewrite Rinv_l in H; auto. lra.
Qed.

Lemma LemmaRminus : ∀(a b c : R), a < c - b -> a + b < c.
Proof.
  intros a b c H1. lra.
Qed.
 


Lemma LemmaRdiv_pose : ∀(a b c d: R), a * b <= c * d -> b > 0 -> 
d > 0 -> a / d <= c / b.
Proof.
  intros. apply (Rmult_le_reg_r d); auto.
  unfold Rdiv. rewrite Rmult_comm. 
  rewrite <- Rmult_assoc.
  rewrite Rinv_r_simpl_m;[| lra]. 
  rewrite Rmult_comm. 
  rewrite <- Rmult_assoc.
  apply (Rmult_le_reg_r b); auto. 
  rewrite Rmult_assoc. 
  rewrite Rinv_l; lra.
Qed.


Lemma Lemma6_13 :  ∀ (f : Fun) (a b : R), Function f /\ \( a, b \) ⊂ dom[ f] 
-> Convex_function f \( a, b \) <-> ( ∀x1 x2 x3 : R, x1 ∈ \( a, b \) -> x2 ∈ \( a, b \) -> x3 ∈ \( a, b \) -> x1 < x2 < x3 -> (f[x2] - f[x1])/(x2 - x1) <= (f[x3] - f[x2])/(x3 - x2)).
Proof.
  intros f a b L. split; intros. 
  - assert(∃ξ:R, ξ = (x3 - x2)/(x3 - x1)).
    { exists ((x3 - x2)/(x3 - x1)); auto. }
    destruct H4 as [ξ H4].
    assert(x2 = ξ * x1 + (1 - ξ)*x3).
    { apply LemmaRdiv in H4; lra. }
    red in H. destruct H as [H [H6 H7]].
    destruct H3 as [H3 H3']. 
    apply (H7 x1 x3 ξ) in H0; auto. 
    rewrite <- H5 in H0.
    assert(1 - ξ = (x2 - x1)/(x3 - x1)).
    { apply (Rmult_eq_reg_r (x3 - x1)).
      unfold Rdiv. rewrite Rmult_assoc.
      rewrite Rinv_l; lra. lra. } 
    rewrite H8 in H0. rewrite H4 in H0.
    apply (Rmult_le_compat_l (x3 - x1)) in H0.
    rewrite Rmult_plus_distr_l in H0.
    rewrite <- Rmult_assoc in H0. 
    unfold Rdiv in H0. rewrite <- Rmult_assoc in H0. 
    rewrite Rinv_r_simpl_m in H0; [|lra].
    rewrite Rplus_comm in H0. 
    rewrite <- Rmult_assoc in H0;
    rewrite <- Rmult_assoc in H0. 
    rewrite Rinv_r_simpl_m in H0;[|lra];
    rewrite Rplus_comm in H0. 
    rewrite Rmult_comm in H0. 
    apply LemmaRdiv_pose; lra. lra.
    rewrite H4. apply AxiomII. split;
    unfold Rdiv. apply Rmult_gt_0_compat. lra.
    apply Rinv_0_lt_compat; lra. 
    apply (Rmult_lt_reg_r (x3 - x1)). lra.
    rewrite Rmult_assoc. rewrite Rinv_l; lra.
  - red. destruct L. repeat split; auto. 
    intros x1 x3 ξ H2 H3 H4. 
    destruct (classic (x1 = x3)).
    + rewrite H5.  replace (ξ * x3 + (1 - ξ) * x3) with x3.
      lra. lra.
    + apply Rdichotomy in H5. destruct H5.
      * assert(∃x2 : R, x2 = ξ * x1 + (1 - ξ)* x3 /\ x2 ∈ \(x1, x3\)).
        { exists (ξ * x1 + (1 - ξ)* x3); split; auto.
          apply AxiomII. applyAxiomII H4.
          cut ((1 - ξ) > 0); intros; [|lra].
          split. apply (Rplus_gt_reg_l (- (ξ * x1))).
          rewrite <- Rplus_assoc.
          rewrite (Rplus_opp_l (ξ * x1)). 
          replace (- (ξ * x1) + x1) with ((1 - ξ) * x1).
          apply (Rmult_gt_compat_l (1 - ξ) x3 x1) in H6; auto.
          lra. lra. apply LemmaRminus. 
          replace (x3 - (1 - ξ) * x3) with (ξ * x3).
          apply Rmult_lt_compat_l; lra. lra. }
         destruct H6 as [x2 [H6 H7]]. applyAxiomII H7.
         assert(x2 ∈ \( a, b \)).
         { apply AxiomII. applyAxiomII H2.
           applyAxiomII H3. lra. } 
         apply (H x1 x2 x3) in H2; auto.
         rewrite <- H6. 
         assert(ξ = (x3 - x2)/(x3 - x1)). 
         { apply (Rmult_eq_reg_r (x3 - x1));[|lra].
           unfold Rdiv. rewrite Rmult_assoc. 
           rewrite Rinv_l. lra. lra. }
         apply (Rmult_le_compat_r (x2 - x1)) in H2;[|lra].
         unfold Rdiv in H2. rewrite Rmult_assoc in H2. 
         rewrite Rinv_l in H2;[|lra]. 
         rewrite Rmult_1_r in H2. rewrite Rmult_comm in H2.
         rewrite <- Rmult_assoc in H2.
          apply (Rmult_le_compat_r (x3 - x2)) in H2;[|lra].
          rewrite Rmult_assoc in H2. 
         rewrite Rinv_l in H2;[|lra]. 
         rewrite Rmult_1_r in H2. unfold Rminus. 
         rewrite Rmult_plus_distr_r. 
         rewrite <- Rplus_comm.  
         rewrite H9. unfold Rdiv. rewrite Rmult_assoc.
         apply (Rmult_le_reg_r (x3 -x1)). lra.
         rewrite Rmult_plus_distr_r.  
         replace ((x3 - x2) * (/ (x3 - x1) * f [x1]) * (x3 - x1)) 
         with ((x3 -x2)*f[x1]).
         rewrite Rmult_plus_distr_r.  
         replace (-((x3 - x2) * / (x3 - x1)) * f [x3] * (x3 - x1))
         with (-(x3 - x2)*f[x3]). lra. symmetry.
         rewrite <- Rmult_comm. rewrite <- Rmult_assoc.
         replace ((x3 - x1) * - ((x3 - x2) * / (x3 - x1))) with (- (x3 - x2)).
         lra. rewrite Ropp_mult_distr_l. 
         rewrite <- Rmult_assoc.  
         apply (Rmult_eq_reg_r (x3 - x1));[|lra].
         rewrite Rmult_assoc. rewrite Rinv_l; lra.
         rewrite Rmult_assoc. 
         replace (/ (x3 - x1) * f [x1] * (x3 - x1)) with (f [x1]).
         lra. rewrite Rmult_comm. rewrite <- Rmult_assoc.
         rewrite Rinv_r_simpl_r; lra.
      * assert(∃x2 : R, x2 = ξ * x1 + (1 - ξ)* x3 /\ x2 ∈ \(x3, x1\)).
        { exists (ξ * x1 + (1 - ξ)* x3); split; auto.
          apply AxiomII. applyAxiomII H4.
          cut ((1 - ξ) > 0); intros; [|lra].
          split. apply (Rplus_gt_reg_l (- (ξ * x1))).
          rewrite <- Rplus_assoc.
          rewrite (Rplus_opp_l (ξ * x1)).  
          unfold Rminus. rewrite Rmult_plus_distr_r.
          rewrite Rplus_0_l. rewrite Rmult_1_l. 
          rewrite Rplus_comm. 
          apply Rplus_gt_compat_r. 
          rewrite Ropp_mult_distr_l. 
          apply Rmult_lt_gt_compat_neg_l; lra.
          rewrite Rplus_comm.
          apply Lemma_budeng'. 
          replace (x1 - ξ * x1) with ((1 - ξ) * x1).
          apply Rmult_lt_compat_l; lra. lra. }
         destruct H6 as [x2 [H6 H7]]. applyAxiomII H7.
         assert(x2 ∈ \( a, b \)).
         { apply AxiomII. applyAxiomII H2.
           applyAxiomII H3. lra. } 
         apply (H x3 x2 x1) in H2; auto.
         rewrite <- H6. 
         assert(ξ = (x2 - x3)/(x1 - x3)). 
         { apply (Rmult_eq_reg_r (x1 - x3));[|lra].
           unfold Rdiv. rewrite Rmult_assoc. 
           rewrite Rinv_l. lra. lra. } 
         apply (Rmult_le_compat_r (x2 - x3)) in H2; [|lra].
         unfold Rdiv in H2. rewrite Rmult_assoc in H2. 
         rewrite Rinv_l in H2;[|lra]. 
         rewrite Rmult_1_r in H2. rewrite Rmult_comm in H2.
         rewrite <- Rmult_assoc in H2.
          apply (Rmult_le_compat_r (x1 - x2)) in H2;[|lra].
          rewrite Rmult_assoc in H2. 
         rewrite Rinv_l in H2;[|lra]. 
         rewrite Rmult_1_r in H2. unfold Rminus. 
         rewrite Rmult_plus_distr_r. 
         rewrite <- Rplus_comm.  
         rewrite H9. unfold Rdiv. rewrite Rmult_assoc.
         apply (Rmult_le_reg_r (x1 -x3)). lra.
         rewrite Rmult_plus_distr_r.  
         replace ((x2 - x3) * (/ (x1 - x3) * f [x1]) * (x1 - x3)) 
         with ((x2 - x3)*f[x1]).
         rewrite Rmult_plus_distr_r.  
         replace (-((x2 - x3) * / (x1 - x3)) * f [x3] * (x1 - x3))
         with (-(x2 - x3)*f[x3]). lra. symmetry.
         rewrite <- Rmult_comm. rewrite <- Rmult_assoc.
         replace ((x1 - x3) * - ((x2 - x3) * / (x1 - x3))) with (- (x2 - x3)).
         lra.  rewrite Ropp_mult_distr_l. 
         rewrite <- Rmult_assoc.  
         apply (Rmult_eq_reg_r (x1 - x3));[|lra].
         rewrite Rmult_assoc. rewrite Rinv_l; lra.
         rewrite Rmult_assoc. 
         replace (/ (x1 - x3) * f [x1] * (x1 - x3)) with (f [x1]).
         lra. rewrite Rmult_comm. rewrite <- Rmult_assoc.
         rewrite Rinv_r_simpl_r; lra.
Qed.
         

(* 定理6.14  1º -> 2º *)
Theorem Theorem6_14_1: ∀ (f : Fun) (a b : R), 
(∀x : R, x ∈ \(a, b \) -> derivable f x ) -> 
((Convex_function f \(a, b \)) -> IntervalIncreaseFun (dN f 1) \(a, b \)).
Proof.
  intros. pose proof H0 as H0'.  
  red in H0. destruct H0 as [H0[H1 H2]].
  red. repeat split.  apply Lemma5_16; auto.
  - simpl. intros z H3. apply AxiomII. 
    apply H in H3. red in H3. destruct H3 as [y0'].
    exists y0'. apply AxiomII'; auto.
  - intros. apply H in H3 as H3'.
    apply H in H4 as H4'. destruct H3' as [y1' H3'].
    destruct H4' as [y2' H4']. 
    assert(I0 : (dN f 1) [x1] = y1').
    { apply f_x. apply Lemma5_16; auto.
      apply AxiomII'; auto. } 
    assert(I1 : (dN f 1) [x2] = y2').
    { apply f_x. apply Lemma5_16; auto.
      apply AxiomII'; auto. } 
    rewrite I0. rewrite I1.
    red in H3'. destruct H3' as [L1[L2 L3]]. 
    red in L3. destruct L3 as [L3[δ1' [L4[L5 L6]]]].
    red in H4'. destruct H4' as [K1[K2 K3]]. 
    red in K3. destruct K3 as [K3[δ2' [K4[K5 K6]]]].
    assert(H6: ∃A : R, A = (f [x2] - f [x1]) / (x2 - x1)).
    exists ((f [x2] - f [x1]) / (x2 - x1)); auto.
    destruct H6 as [A].
    assert(H7: Function f /\ \( a, b \) ⊂ dom[ f]).
    split; auto. apply Lemma6_13 in H7. destruct H7.
    clear H8. 
    assert(I2 : ∃ δ', δ' > 0 /\ (∀ x, x ∈ \( x1 - δ', x1\) -> (f [x1] - f [x]) / (x1 - x) <= (f [x2] - f [x1]) / (x2 - x1))).
    { exists(x1 - a). applyAxiomII H3.
      split. lra. intros. applyAxiomII H8.
      apply (H7 H0' x x1 x2); auto. apply AxiomII; lra.
      apply AxiomII; auto. lra. }
     
    assert(I4: ∀x, \{\ λ x y,y = (f [x] - f [x1]) / (x - x1) \}\ [x] = (f [x] - f [x1]) / (x - x1)). 
    { intros. Function_ass.  }
     assert(I4': ∀x, \{\ λ x y,y = (f [x] - f [x2]) / (x - x2) \}\ [x] = (f [x] - f [x2]) / (x - x2)). 
    { intros. Function_ass.  }
    assert(y1' <= (f [x2] - f [x1]) / (x2 - x1)).
    { destruct I2 as [δ'[I3 I2]].
      rewrite <- H6. rewrite <- H6 in I2. 
      assert (H9 : ∀ ε, ε > 0 -> y1' < A + ε).
      { intros. apply L6 in H8. destruct H8 as [δ1[[H8 H9]H10]].
        pose proof (Lemma1 δ1 δ'). apply H11 in H8; auto.
        clear H11. destruct H8 as [δ[H8 [H12 H11]]].
        assert(∃ x, x ∈ \( x1 - δ', x1 \) /\ 0 < Abs [x - x1] < δ1).
        { exists (x1 - δ/2). split. apply AxiomII. lra. 
          split. apply Abs_not_eq_0; lra. apply Abs_R; lra. } 
        destruct H13 as [x[H13 H14]]. pose proof H14 as H14'. apply H10 in H14.
        apply I2 in H13. rewrite I4 in H14. 
        apply Abs_R in H14. 
        replace ((f [x1] - f [x]) / (x1 - x)) with ((f [x] - f [x1]) / (x - x1)) in H13. lra. field. destruct H14'. apply Abs_not_eq_0 in H15. lra. }
     apply Rnot_gt_le. intro. 
     assert (H12 : (y1' - A) / 2 > 0). lra. apply H9 in H12 as H13. lra. }
    assert(I5 : ∃ δ', δ' > 0 /\ (∀ x, x ∈ \( x2, x2 + δ'\) -> (f [x2] - f [x1]) / (x2 - x1) <= (f [x] - f [x2]) / (x - x2))).
    { exists(b - x2). applyAxiomII H4.
      split. lra. intros. applyAxiomII H9.
      apply (H7 H0' x1 x2 x); auto. apply AxiomII; lra.
      apply AxiomII; auto. lra. lra. } 
   assert(y2' >= (f [x2] - f [x1]) / (x2 - x1)).
   {  destruct I5 as [δ'[I3 I6]].
      rewrite <- H6. rewrite <- H6 in I6. 
      assert (H9 : ∀ ε, ε > 0 -> y2' > A - ε).
      { intros. apply K6 in H9. destruct H9 as [δ2[[H9 H10]H11]].
        pose proof (Lemma1 δ2 δ'). apply H12 in H9; auto.
        clear H12. destruct H9 as [δ[H9 [H12 H13]]].
        assert(∃ x, x ∈ \( x2, x2 + δ' \) /\ 0 < Abs [x - x2] < δ2).
        { exists (x2 + δ/2). split. apply AxiomII. lra. 
          split. apply Abs_not_eq_0; lra. apply Abs_R; lra. }
        destruct H14 as [x[H15 H14]]. apply H11 in H14.
        apply I6 in H15. rewrite I4' in H14. 
        apply Abs_R in H14. lra. } 
     apply Rnot_gt_ge. intro. 
     assert (H12 : (A - y2') / 2 > 0). lra. apply H9 in H12 as H13. lra. }
     lra.
Qed.
    

(* 定理6.14  2º -> 3º *)
Theorem Theorem6_14_2 : ∀ (f : Fun) (a b : R), 
(∀x : R, x ∈ \(a, b \) -> derivable f x ) -> IntervalIncreaseFun (dN f 1) \(a, b \) -> (∀x1 x2: R, x1 ∈ \(a, b \) -> x2 ∈ \(a, b \) -> 
f[x2] >= f[x1] + f '[x1]*(x2 - x1)).
Proof.
  intros. red in H0. destruct H0 as [H0[H3 H4]].
  assert(H5': ∀x:R, x ∈ \( a, b \) -> (dN f 1) [x] = f '[x]).
  { intros. apply f_x; auto. apply AxiomII'.
    apply H in H5. red in H5. destruct H5 as [y'].
    apply derEqual in H5 as H6'. rewrite H6'; auto. }
  destruct (classic (x1 = x2)).
  - rewrite H5. lra.
  - apply Rdichotomy in H5. destruct H5.
    + assert(L0: ContinuousClose f x1 x2).
      { red. split. applyAxiomII H1; applyAxiomII H2.
        red. intros. apply Theorem5_1.
        apply H. apply AxiomII; lra.
        split. apply H in H1; apply Theorem5_1 in H1;
        apply Theorem4_1 in H1; tauto.
        apply H in H2; apply Theorem5_1 in H2; 
        apply Theorem4_1 in H2; tauto. }
      assert(L1: (∀ x, x1 < x < x2 -> derivable f x)).
      { intros. apply H. applyAxiomII H1; applyAxiomII H2.
        apply AxiomII; lra. }
      pose proof (Theorem6_2 f x1 x2 H5 L0 L1).
      destruct H6 as [ξ[H7 H8]]. 
      apply derEqual in H8. cut(ξ ∈ \( a, b \)); intros. 
      apply (H4 x1 ξ) in H1 as H1'; auto.
      rewrite H5' in H1'; auto.   
      rewrite H5' in H1'; auto.
      apply LemmaRdiv in H8; [|lra]. 
      assert(f '[ x1] * (x2 - x1) <= f '[ ξ] * (x2 - x1)).
      { apply Rmult_le_compat_r; lra. }
      lra. lra. apply AxiomII; applyAxiomII H1; applyAxiomII H2;lra.
    + assert(L0: ContinuousClose f x2 x1).
      { red. split. applyAxiomII H1; applyAxiomII H2.
        red. intros. apply Theorem5_1.
        apply H. apply AxiomII; lra.
        split. apply H in H2; apply Theorem5_1 in H2;
        apply Theorem4_1 in H2; tauto.
        apply H in H1; apply Theorem5_1 in H1; 
        apply Theorem4_1 in H1; tauto. }
      assert(L1: (∀ x, x2 < x < x1 -> derivable f x)).
      { intros. apply H. applyAxiomII H1; applyAxiomII H2.
        apply AxiomII; lra. }
      pose proof (Theorem6_2 f x2 x1 H5 L0 L1).
      destruct H6 as [ξ[H7 H8]]. 
      apply derEqual in H8. cut(ξ ∈ \( a, b \)); intros. 
      apply (H4 ξ x1) in H1 as H1'; auto;[|lra].
      rewrite H5' in H1'; auto.   
      rewrite H5' in H1'; auto.
      apply LemmaRdiv in H8; [|lra].
      assert((x2 - x1)* f '[ x1] <= ((x2 - x1) * f '[ ξ])).
      { apply Rmult_le_compat_neg_l; lra. }
      lra. apply AxiomII; applyAxiomII H1; applyAxiomII H2;lra.
Qed.

(* 定理6.14  3º -> 1º *)
Theorem Theorem6_14_3 : ∀ (f : Fun) (a b : R),a < b -> \( a, b \) ⊂ dom[ f] -> (∀x : R, x ∈ \(a, b \) -> derivable f x ) -> (∀x1 x2: R, x1 ∈ \(a, b \) -> x2 ∈ \(a, b \) 
-> f[x2] >= f[x1] + f '[x1]*(x2 - x1)) -> (Convex_function f \(a, b \)).
Proof.
  intros. red. 
  assert(∃x : R, x ∈ \( a, b \)).
  { exists((a+b)/2). apply AxiomII. lra. } 
  destruct H3 as [x H3]. apply H1 in H3. 
  red in H3. destruct H3 as [y']. red in H3.
  split. tauto. split; auto.
  intros. assert(∃x3 : R, x3 = ξ * x1 + (1 - ξ)*x2).
  { exists (ξ * x1 + (1 - ξ) * x2); auto. } 
  destruct H7 as [x3 H7]. 
  assert((x1 - x3) = (1 - ξ) * (x1 - x2)).
  { rewrite H7. lra. }
  assert((x2 - x3) = ξ * (x2 - x1)).
  { rewrite H7. lra.  } 
  assert(x3 ∈ \( a, b \)).
  { rewrite H7. apply AxiomII. applyAxiomII H4.
    applyAxiomII H5; applyAxiomII H6. 
    destruct H4. destruct H6. destruct H5.
    assert(0 < (1 - ξ) < 1).
    lra. assert(ξ * x1 > ξ * a).
    apply Rmult_gt_compat_l; lra. 
    assert((1 - ξ) * x2 > (1 - ξ) * a).
    apply Rmult_gt_compat_l; lra. split. lra.
    assert(ξ * x1 < ξ * b). 
    apply Rmult_lt_compat_l; lra.
    assert((1 - ξ) * x2 < (1 - ξ) * b).
    apply Rmult_gt_compat_l; lra. lra. }
  apply (H2 x3 x1) in H10 as H10'; auto. 
  rewrite H8 in H10'. applyAxiomII H6.
  apply (H2 x3 x2) in H10 as H10''; auto.
  rewrite H9 in H10''. rewrite <- H7.
  apply (Rmult_ge_compat_l ξ f[x1] _) in H10'; [|lra].
  apply (Rmult_ge_compat_l (1 - ξ)) in H10''; [|lra].
  lra. 
Qed.
 
      
Theorem Theorem6_15 : ∀ (f : Fun) (a b : R),a < b -> \( a, b \) ⊂ dom[ f] -> (∀x : R, x ∈ \(a, b \) -> derivable f x ) -> (∀x : R, x ∈ \(a, b \) -> derivable (dN f 1) x) -> (Convex_function f \(a, b \) <-> (∀x : R, x ∈ \(a, b \) -> (dN f 1) '[x] >= 0)).
Proof.
  split; intros.
  - apply -> (Theorem6_3 (dN f 1) a b); auto.
    apply Theorem6_14_1; auto. 
    split. applyAxiomII H4. lra.
    split. intros z H5; apply AxiomII.
    apply H1 in H5. red in H5. destruct H5 as [z'].
    exists (z'). apply AxiomII'; auto.
    apply H2.
  - apply Theorem6_14_3; auto.    
    apply Theorem6_14_2; auto.
    assert(IntervalIncreaseFun (dN f 1) \( a, b \) <->
    (∀x : R,x ∈ \( a, b \) -> (dN f 1) '[ x] >= 0)).
    { apply Theorem6_3. repeat split; auto. 
      intros z H5; apply AxiomII.
      apply H1 in H5. red in H5. destruct H5 as [z'].
      exists (z'). apply AxiomII'; auto. }
     destruct H4.  apply H5; auto.
Qed.


End A6_5.

Export A6_5.   

     
     
       
   
    
    
    
    
  
  
 






















