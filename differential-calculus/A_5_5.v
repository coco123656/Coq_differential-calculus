Require Export A_5_4.

Module A5_5.

(* 定义1 ：可微  *)
Definition differentiable (f : Fun) (x0: R) := Function f /\ (∃δ, δ >0 /\ Neighbor x0 δ ⊂ dom[f] /\ (∃ (o : Fun), InfinitesimalHigherOrder o \{\ λ x y, y = x \}\ 0 /\ (∃ A, ∀δx, (δx + x0) ∈ Neighbor x0 δ -> ∃ δy, δy = f[x0 + δx] - f[x0] /\ δy = A * δx + o[δx]))). 



Lemma Lemma_Inf: ∀ (f : Fun) (x0 A: R), limit \{\ λ x y, y = f [x]  \}\ x0 A <-> 
  Infinitesimal (\{\ λ x y, y = f[x] - A \}\) x0 .
Proof.  
  split; intros.
  - red. red. red in H. destruct H as [H [δ [H1 [H2 H3]]]].
    split. 
    + red. intros.  
      applyAxiomII H0. destruct H0 as [x1 [y1 [H0 H0']]].
      applyAxiomII H4. destruct H4 as [x2 [y2 [H4 H4']]].
      apply ProdEqual in H0. apply ProdEqual in H4.
      destruct H0. destruct H4.
      rewrite H5. rewrite H6. rewrite H0'. rewrite H4'.
      rewrite <- H0. rewrite <- H4. auto.
    + exists δ. split. auto. split. 
      * red. intros. apply AxiomII. exists (f [z] - A). apply AxiomII'. auto.
      * intros. apply H3 in H0. destruct H0 as [δ' [H0 H0']].
        exists δ'. split; auto. intros. apply H0' in H4.  
        assert (\{\ λ x1 y, y = f [x1] - A\}\ [x] = f [x] - A).
        { apply f_x.
          - red. intros.
            applyAxiomII H5. destruct H5 as [x1' [y1' [H5 H5']]].
            applyAxiomII H6. destruct H6 as [x2' [y2' [H6 H6']]].
            apply ProdEqual in H5. apply ProdEqual in H6.
            destruct H5. destruct H6.
            rewrite H7. rewrite H8. rewrite H5'. rewrite H6'.
            rewrite <- H5. rewrite <- H6. auto.
          - apply AxiomII. exists x, ( f [x] - A). split; auto. }
        rewrite H5.
        assert (\{\ λ x1 y, y = f [x1] \}\ [x] = f [x]).
        { apply f_x.
          - red. intros.
            applyAxiomII H6. destruct H6 as [x1' [y1' [H6 H6']]].
            applyAxiomII H7. destruct H7 as [x2' [y2' [H7 H7']]].
            apply ProdEqual in H6. apply ProdEqual in H7.
            destruct H6. destruct H7.
            rewrite H8. rewrite H9. rewrite H6'. rewrite H7'.
            rewrite <- H6. rewrite <- H7. auto.
          - apply AxiomII. exists x, f[x]. split; auto. }
        rewrite H6 in H4. rewrite Rminus_0_r. auto.
  - red in H. red in H. destruct H as [H [δ [H1 [H2 H3]]]]. red.
    split.
    + red. intros.
      applyAxiomII' H0. applyAxiomII' H4. 
      rewrite H0. rewrite H4. auto.
    + exists δ. split. auto. split. 
      * red. intros. apply AxiomII. exists (f [z]). apply AxiomII'. auto.
      * intros. apply H3 in H0. destruct H0 as [δ' [H0 H0']].
        exists δ'. split; auto. intros. apply H0' in H4.
        assert (\{\ λ x1 y, y = f [x1] - A \}\ [x] = f [x] - A).
        { apply f_x.
          - red. intros.
            applyAxiomII H5. destruct H5 as [x1' [y1' [H5 H5']]].
            applyAxiomII H6. destruct H6 as [x2' [y2' [H6 H6']]].
            apply ProdEqual in H5. apply ProdEqual in H6.
            destruct H5. destruct H6.
            rewrite H7. rewrite H8. rewrite H5'. rewrite H6'.
            rewrite <- H5. rewrite <- H6. auto.
          - apply AxiomII. exists x, ( f [x] - A). split; auto. }
        rewrite H5 in H4.
        assert (\{\ λ x1 y, y = f [x1] \}\ [x] = f [x]).
        { apply f_x.
          - red. intros.
            applyAxiomII H6. destruct H6 as [x1' [y1' [H6 H6']]].
            applyAxiomII H7. destruct H7 as [x2' [y2' [H7 H7']]].
            apply ProdEqual in H6. apply ProdEqual in H7.
            destruct H6. destruct H7.
            rewrite H8. rewrite H9. rewrite H6'. rewrite H7'.
            rewrite <- H6. rewrite <- H7. auto.
          - apply AxiomII. exists x, f[x]. split; auto. }
        rewrite H6.
        rewrite Rminus_0_r in H4. auto.
Qed.


Theorem Theorem5_9' : ∀(f : Fun) (x0: R), differentiable f x0 <->
derivable f x0.
Proof.
intros. split; intros.
- red. red in H. destruct H as [H[δ[H1[H2 [o [H3[A H4]]]]]]]. 
  exists A.
  apply <- (Equaderivative f x0 A).
  red. 
  split; auto. split. exists δ. split; auto. red.  
  assert (H': Function \{\ λ h y,y = (f [x0 + h] - f [x0]) / h \}\).
  { QED_function. }  
  split. auto. 
  red in H3. destruct H3 as [H3[H5 H6]].
  destruct H6 as [[δ1 [H6 [H7 [H8 H9]]]] H10]. 
  red in H10. destruct H10 as [H10[δ1' [H11[H12 H13]]]]. 
  assert (∃δ', δ' > 0 /\ δ' < δ).
  { exists (δ / 2); split; lra. } 
  destruct H0 as [δ'[H0 H0']]. exists δ'. split; auto.
  split. + 
  intros z H4'. apply AxiomII. exists ((f [x0 + z] - f [x0]) / z ).
  apply AxiomII'; auto. 
  + intros. assert(ε/2 > 0). lra.
  apply H13 in H15. destruct H15 as [δ1''[[H16 H16'] H17]].
  clear H13. 
   pose proof (Lemma1 δ' δ1'').
    apply H13 in H0 as H1'; auto. clear H13. 
    destruct H1' as [δ0[H18 [H19 H20]]].
    exists δ0; split; auto. intros δx H13.
    pose proof (H4 δx). 
    assert(δx + x0 ∈ Neighbor x0 δ).
    { apply AxiomII. replace (δx + x0 - x0) with (δx - 0); lra.  }
    assert(0 < Abs [δx - 0] < δ1''). lra.
    
    apply H15 in H21 as H15'. clear H15. 
    destruct H15' as [δy [H15' H17']].
    assert (\{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\ [δx] = ((f [x0 + δx] - f [x0])/ δx)). 
    { apply f_x; auto. apply AxiomII'; auto.  }
    rewrite H15. rewrite <- H15'.  rewrite H17'.
    replace ((A * δx + o [δx]) / δx - A) with ((o [δx]) / δx).
    apply H17 in H22. 
    assert(\{\ λ x y,y = o [x] / \{\ λ x0 y0,y0 = x0 \}\ [x] \}\ [δx] = o [δx]/δx). { apply f_x; auto. apply AxiomII. exists δx, (o [δx] / δx).
    split; auto. assert(\{\ λ x1 y0,y0 = x1 \}\ [δx] = δx).
    apply f_x; auto. apply AxiomII. exists δx,δx. split; auto.
    rewrite H23. auto. } rewrite H23 in H22.
    rewrite Rminus_0_r in H22. lra. 
    rewrite Rdiv_plus_distr. 
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_r. lra. destruct H22.
    rewrite Rminus_0_r in H22. apply Abs_not_eq_0; auto.
 - red in H. red. destruct H as [A H]. 
    pose proof H as H'.
    red in H. destruct H as [H [H1 H2]].
    split; auto. destruct H1 as [δ [H1 H3]]. 
    exists δ. split; auto. split; auto. 
    rewrite (Equaderivative f x0 A) in H'.
    red in H'. destruct H' as [H' [H4 H5]].
    exists (\{\ λ h y, y = (f [x0 + h] - f [x0]) - h*A \}\).
    split.
    + red. split. 
      * red. intros. applyAxiomII' H0. applyAxiomII' H6.
        rewrite H0. rewrite H6. auto.
      * split. red. intros. applyAxiomII' H0. applyAxiomII' H6.
        rewrite H0. rewrite H6. auto.
        split.
        -- exists δ. split; auto. split. red. intros.
           apply AxiomII. exists (f [x0 + z] - f [x0] - z * A). apply AxiomII'.
           auto. split. red. intros. apply AxiomII. exists z. apply AxiomII'.
           auto. intros. 
           assert (\{\ λ x1 y, y = x1 \}\ [x] = x).
           { apply f_x. red. intros. applyAxiomII' H6. applyAxiomII' H7.
             rewrite H6. rewrite H7. auto. apply AxiomII'. auto. }
           rewrite H6. applyAxiomII H0. rewrite Rminus_0_r in H0.
           apply Lemma2 in H0. destruct H0. auto. 
        -- assert (∃g: Fun, \{\ λ x y, y = g [x]  \}\ = 
                   \{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\ ).
           { exists (\{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\).
             assert (∀x, \{\ λ h y0, y0 = (f [x0 + h] - f [x0]) / h \}\ [x]
                      =  (f [x0 + x] - f [x0]) / x).  
             { intros. apply f_x.
               - red. intros. applyAxiomII' H0. applyAxiomII' H6.
                 rewrite H0. rewrite H6. auto.
               - apply AxiomII'. auto. }
             apply AxiomI. split; intros. apply AxiomII; applyAxiomII H6;
             destruct H6 as [x[y[H7 H8]]]; exists x,y;
             rewrite H0 in H8; split; auto. apply AxiomII. applyAxiomII H6.
             destruct H6 as [x[y[H7 H8]]]; exists x,y. split; auto.
             rewrite H0. auto. }   
           destruct H0 as [g]. pose proof H5 as H5'. rewrite <- H0 in H5. 
           rewrite (Lemma_Inf g 0 A) in H5. 
           red in H5.
           assert (\{\ λ x y, y = \{\ λ h y0, y0 = f [x0 + h] - f [x0] - h * A 
                   \}\ [x] / \{\ λ x1 y0, y0 = x1 \}\ [x] \}\ = 
                   \{\ λ h y, y =(f [x0 + h] - f [x0] - h * A ) / (h) \}\ ).
           { apply AxiomI. split; intros. apply AxiomII; applyAxiomII H6;
             destruct H6 as [x[y[H7 H8]]]; exists x,y.
             split; auto. 
             assert (\{\ λ h y0,y0 = f [x0 + h] - f [x0] - h * A \}\ [x]
                      = (f [x0 + x] - f [x0] - x * A )).
             { apply f_x. red. intros. applyAxiomII H6. applyAxiomII H9.
               destruct H6 as [x2[y2[H6 H6']]].
               destruct H9 as [x3[y3[H9 H9']]].
               apply ProdEqual in H6. destruct H6.
               apply ProdEqual in H9. destruct H9.
               rewrite H10. rewrite H11. rewrite H6'. rewrite H9'. 
               rewrite <- H6. rewrite <- H9. auto.
               apply AxiomII'. auto. }
             rewrite H6 in H8. 
             assert (\{\ λ x1 y0, y0 = x1 \}\ [x] = x).
             { apply f_x. red. intros. applyAxiomII H9. applyAxiomII H10.
               destruct H9 as [x2[y2[H9 H9']]].
               destruct H10 as [x3[y3[H10 H10']]].
               apply ProdEqual in H9. destruct H9.
               apply ProdEqual in H10. destruct H10.
               rewrite H11. rewrite H12. rewrite H9'. rewrite H10'.
               rewrite <- H9. rewrite <- H10. auto.
               apply AxiomII'. auto. }
             rewrite H9 in H8. auto. 
             apply AxiomII. applyAxiomII H6. destruct H6 as [x1[y1[H6 H6']]].
             exists x1, y1. split; auto.
             assert (\{\ λ h y0,y0 = f [x0 + h] - f [x0] - h * A \}\ [x1]
                      = (f [x0 + x1] - f [x0] - x1 * A )).
             { apply f_x. red. intros. applyAxiomII H7. applyAxiomII H8.
               destruct H7 as [x2[y2[H7 H7']]].
               destruct H8 as [x3[y3[H8 H8']]].
               apply ProdEqual in H7. destruct H7.
               apply ProdEqual in H8. destruct H8.
               rewrite H9. rewrite H10. rewrite H7'. rewrite H8'. 
               rewrite <- H7. rewrite <- H8. auto.
               apply AxiomII'. auto. }
             rewrite H7.
             assert (\{\ λ x2 y0, y0 = x2 \}\ [x1] = x1).
             { apply f_x. red. intros. applyAxiomII H8. applyAxiomII H9.
               destruct H8 as [x2[y2[H8 H8']]].
               destruct H9 as [x3[y3[H9 H9']]].
               apply ProdEqual in H8. destruct H8.
               apply ProdEqual in H9. destruct H9.
               rewrite H10. rewrite H11. rewrite H8'. rewrite H9'.
               rewrite <- H8. rewrite <- H9. auto.
               apply AxiomII'. auto. }
             rewrite H8. auto. }
             rewrite H6.  
           red in H5. destruct H5 as [H5 [δ' [H7 [H8 H9]]]].
           red. split.
           red. intros. applyAxiomII' H10. applyAxiomII' H11.
           rewrite H10. auto. exists δ'. split; auto.
           split. red. intros. apply AxiomII. 
           exists ((f [x0 + z] - f [x0] - z * A) / z). apply AxiomII'. auto. 
           intros. apply H9 in H10. destruct H10 as [δ'' [H10 H11]].
           exists δ''. split; auto. intros. 
           pose proof H12 as H12'. apply H11 in H12. 
           assert (∀x, \{\ λ x y, y = g [x] \}\ [x] =
                   \{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\ [x]).
           { intros. rewrite H0. auto. }
           pose proof (H13 x) as H13'. 
           assert (\{\ λ h y, y = (f [x0 + h] - f [x0] - h * A) / h \}\ [x]
                                = ( (f [x0 + x] - f [x0] - x * A) / x)).
           { apply f_x. red. intros. applyAxiomII' H14.
             applyAxiomII' H15. rewrite H14. auto. apply AxiomII'. auto. }
           rewrite H14. 
           assert (\{\ λ x y, y = g [x] - A \}\ [x]
                   = g [x] - A).
           { apply f_x. red. intros. applyAxiomII' H15.
             applyAxiomII' H16. rewrite H15. auto.
             apply AxiomII'. auto. }
           rewrite H15 in H12. 
           rewrite (Rdiv_minus_distr (f [x0 + x] - f [x0]) (x * A) x).
           assert (\{\ λ h y, y = (f [x0 + h] - f [x0]) / h \}\ [x]
                   = ((f [x0 + x] - f [x0]) / x)).
           { apply f_x. red. intros. applyAxiomII' H16. applyAxiomII' H17.
             rewrite H16; auto.
             apply AxiomII'. auto. }
           rewrite H16 in H13'.
           assert (\{\ λ x y, y = g [x] \}\ [x] = g [x]).
           { apply f_x. red. intros. applyAxiomII' H17. applyAxiomII' H18.
             rewrite H17. auto. apply AxiomII'. auto. }
           rewrite H17 in H13'. rewrite <- H13'.
           assert (x * A / x = A).
           { unfold Rdiv. apply Rinv_r_simpl_m.
             rewrite Rminus_0_r in H12'.
             destruct H12'. apply Abs_not_eq_0 in H18. auto. }
           rewrite H18. apply H12.
      + exists A. intros. exists (f [x0 + δx] - f [x0]). split; auto.
        assert (\{\ λ h y, y = f [x0 + h] - f [x0] - h * A \}\ [δx]
                = (f [x0 + δx] - f [x0] - δx * A)).
        { apply f_x. red. intros. applyAxiomII' H6. applyAxiomII' H7.
          rewrite H6. auto. apply AxiomII'. auto. }
        rewrite H6. lra.
Qed.

(* 一阶微分 优先等级？ *)
Notation "'dy =' f '[ x ] 'dx'" := (differentiable f x)(at level 50).

(* n阶微分 *)
Notation "'dⁿy =' f '^' n [ x ] 'dx'" := (differentiable (dN f n) x)(at level 50). 

End A5_5. 
Export A5_5.   















