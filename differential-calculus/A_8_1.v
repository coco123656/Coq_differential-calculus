Require Export A_6_5.

Module A8_1.


(* 定义：原函数 *)
Definition Primitive_f (f F: Fun) (D : sR) := Function f /\ Function F /\
D ⊂ dom[f] /\ D ⊂ dom[F] /\ 
(∀ x : R, x ∈ D -> derivative F x (F '[x]) /\ F '[x] = f[x]).


(* 定理8.1 原函存在定理 *)

(* 定理8.2  *)
Theorem Theorem8_2 : ∀ (f F : Fun)(D : sR), Primitive_f f F D ->
∀C :R, Primitive_f f  \{\λ x y, y = F [x] + \{\ λ x y, y = C \}\[x] \}\ D.
Proof. 
  intros. 
  assert(H':∀x : R, \{\ λ x y, y = C \}\[x] = C).
  { intros. Function_ass. }
  destruct H as [H[H1[H2 [H3 H4]]]].
  unfold Primitive_f in *. 
  split; auto. split.
  QED_function. split; auto.
  split. red. intros. 
  apply AxiomII. 
  exists (F[z] + C). apply AxiomII'.
  rewrite H'. auto. intros. 
  pose proof (Lemma5_12 C x).
  apply derEqual in H5 as H5'.
  assert(derivative \{\ λ x0 y,y = F [x0] + \{\ λ _ y0,y0 = C \}\ 
  [x0] \}\ x  f[x]).
  { replace f[x] with (f[x] + \{\ λ _ y,y = C \}\ '[ x]).
  apply H4 in H0 as [H0' H6].
  rewrite <- H6.
  apply Theorem5_4_1; red.
  exists (F '[x]); auto. 
  exists 0. apply Lemma5_12.
  rewrite H5'; lra. } 
  apply derEqual in H6 as H6'.
  rewrite H6'; split; auto.
Qed.


Lemma Lemma8_4' :∀(F G: Fun) (a b : R), a < b ->
  (∀x : R,x ∈ \(a,b\) -> 
  derivative \{\ λ x0 y, y = F [x0] - G [x0] \}\ x 0) ->
 (∃C : R,∀x : R,x ∈ \(a,b\) -> F [x] - G [x] = C).
Proof.
  intros. 
  assert(∃x1 : R, x1 ∈ \( a, b \)).
  { exists ((a+b)/2). apply AxiomII; lra. }
  destruct H1 as [x1]. 
  exists (F [x1] - G [x1]). intros. 
  destruct(classic (x = x1)).
  rewrite H3; auto. 
  assert(∃h : Fun, h = \{\ λ x0 y,y = F [x0] - G [x0] \}\).
  { exists \{\ λ x0 y,y = F [x0] - G [x0] \}\; auto. }
  destruct H4 as [h]. 
  assert(∀x : R,x ∈ \( a, b \) -> Continuous h x).
  { intros. rewrite H4. apply Theorem5_1. 
    red. exists 0; auto. }
  apply H5 in H1 as H1'; apply Theorem4_1 in H1'.
  apply H5 in H2 as H2'; apply Theorem4_1 in H2'. 
  applyAxiomII H1. applyAxiomII H2.
  assert(∀x : R, h[x] = F [x] - G [x]).
  { intros. rewrite H4. Function_ass.  }  
  apply Rdichotomy in H3. 
  destruct H3.
  - assert(ContinuousClose h x x1).
    { red; split. red. intros. 
      apply H5. apply AxiomII. lra.
      split; tauto. }
    assert(∀ x0, x < x0 < x1 -> derivable h x0).
    { intros. rewrite H4. red. exists 0. 
      apply H0; apply AxiomII; lra. } 
    apply (Theorem6_2 h x x1) in H7; auto.
    destruct H7 as [ξ[H7 H9]].
    cut(ξ ∈ \( a, b \)). intros.
    apply H0 in H10. 
    rewrite <- H4 in H10. 
    apply (derivativeUnique _ _ ((h [x1] - h [x]) / (x1 - x)) 0) in H9; auto.
    symmetry in H9.   
    apply LemmaRdiv in H9;[|lra].
    rewrite H6 in H9. rewrite H6 in H9.
    lra. apply AxiomII. lra.  
  - assert(ContinuousClose h x1 x).
    { red; split. red. intros. 
      apply H5. apply AxiomII. lra.
      split; tauto. }
    assert(∀ x0, x1 < x0 < x -> derivable h x0).
    { intros. rewrite H4. red. exists 0. 
      apply H0; apply AxiomII; lra. } 
    apply (Theorem6_2 h x1 x) in H7; auto.
    destruct H7 as [ξ[H7 H9]].
    cut(ξ ∈ \( a, b \)). intros.
    apply H0 in H10. 
    rewrite <- H4 in H10.  
    apply (derivativeUnique _ _ ((h [x] - h [x1]) / (x - x1)) 0) in H9; auto. 
    symmetry in H9.   
    apply LemmaRdiv in H9;[|lra].
    rewrite H6 in H9. rewrite H6 in H9.
    lra. apply AxiomII. lra.
Qed.



Theorem Theorem8_2': ∀ (f : Fun)(a b : R), a < b -> 
(∀F G : Fun,Primitive_f f F \(a,b\) /\ Primitive_f f G \(a, b\) -> 
∃C : R, ∀x, x ∈ \(a,b\) -> F[x] - G[x] = C).
Proof. 
  intros. destruct H0.  
  red in H0, H1. destruct H0 as [_[H0[_[H7 H8]]]]. 
  destruct H1 as [_[H6[_[H9 H10]]]]. 
  assert(∀x : R,x ∈ \(a,b\) -> derivative \{\λ x0 y,y = F[x0] - G[x0]\}\ x 0). 
  { intros. apply H8 in H1 as H8'. destruct H8'.
    apply H10 in H1 as H10'. destruct H10'. 
    cut((F '[ x]) - (G '[ x]) = 0); intros. 
    rewrite <- H11. 
    apply Theorem5_4_2; red;[exists (F '[ x])|exists (G '[ x])]; auto.
    lra.  }
  apply Lemma8_4'; auto.
Qed.

  
Definition cF (x : (set Fun)) : Fun := c x \{\ λ x y, y = 0 \}\.
  
(* 定义：区间D上的不定积分 *)
Definition Indef_integral_f (f : Fun) (D : sR) := \{ λ F, Primitive_f f F D \}.




Definition Indef_integral (f :Fun)(D : sR) := cF(Indef_integral_f f D).

Notation "∫ D f 'xdx'" := (Indef_integral f D)(at level 200).

Theorem AxiomcF : ∀ (x : (set Fun)), NotEmpty x -> (cF x) ∈ x.
Proof. intros x H0. unfold cF. apply Axiomc. auto. Qed.

Lemma Lemma8_1: ∀(f F: Fun) (D : sR), Primitive_f f F D -> 
(Primitive_f f (cF (Indef_integral_f f D)) D).
Proof. 
  intros. 
  assert(cF (Indef_integral_f f D) ∈ (Indef_integral_f f D)).
  { apply AxiomcF. exists F. apply AxiomII; auto. }
  applyAxiomII H0; auto.
Qed.


Lemma Lemma8_2 :∀(f F: Fun) (a b : R),a < b -> Primitive_f f F \(a,b\) 
-> (∃C : R,∀x : R,x ∈ \( a, b \) -> (cF (Indef_integral_f f \( a, b \)))[x] - F [x] = C).
Proof. 
  intros. pose proof H0 as H0'.
  destruct H0 as [H0[H1[H2[H3 H4]]]].
  apply Lemma8_1 in H0' as H6.
  Print Theorem8_2'.
  apply (Theorem8_2' f); auto.
Qed.
 
 
Theorem Lemma8_3 :∀(f : Fun) (D : sR), Function (cF (Indef_integral_f f D)).
Proof. 
  intros.
  destruct (classic (NotEmpty (Indef_integral_f f D))).
  - apply AxiomcF in H.  unfold Indef_integral in H.
    applyAxiomII H. red in H. tauto.
  - assert(cF (Indef_integral_f f D) = \{\ λ x y, y = 0 \}\).
    { unfold cF. unfold c. destruct tf. contradiction.
      auto. }
    rewrite H0. QED_function.
Qed.  
  
Lemma Lemma8_4 : ∀(f F: Fun) (D : sR), Primitive_f f F D -> (∀x : R, x ∈ D -> derivative (cF (Indef_integral_f f D)) x f[x]).
Proof.
  intros. pose proof H as H'.
  red in H. destruct H as [H[H1[H2[H3 H4]]]].
  apply H4 in H0 as H0'. destruct H0' as [H5 H6].
  rewrite H6 in H5. 
  assert(cF (Indef_integral_f f D) ∈ (Indef_integral_f f D)).
  { apply AxiomcF. exists F. apply AxiomII; auto. }
  applyAxiomII H7. red in H7.
  destruct H7 as [_[_[_[H7 H8]]]].
  apply H8 in H0 as H0'. clear H8. destruct H0' as [H0' H8].
  rewrite <- H8; auto.
Qed.
  


 
Theorem Theorem8_3 : ∀(f g F G: Fun) (D : sR)(k1 k2 : R), Primitive_f f F D /\ Primitive_f g G D -> (∃P, Primitive_f \{\ λ x y, y = k1 * f[x] + k2 * g[x] \}\ P D).
Proof.
  intros. destruct H.
  exists \{\ λ x y, y = k1 * F[x] + k2 * G[x] \}\.
  destruct H as [H[H1[H2[H3 H4]]]].
  destruct H0 as [H0[H5[H6[H7 H8]]]]. 
  split. QED_function. split. QED_function.
  split. intros z H'. apply AxiomII. 
  exists (k1 * f [z] + k2 * g [z]).
  apply AxiomII'; auto. split. 
  intros z H'. apply AxiomII. exists (k1 * F [z] + k2 * G [z]).
  apply AxiomII'; auto. intros. 
  apply H4 in H9 as H4'. apply H8 in H9 as H8'.
  destruct H8'. destruct H4'.  
  cut(derivable F x); intros. 
  apply (Lemma5_3 F k1 x) in H14. 
  cut(derivable G x); intros.
  apply (Lemma5_3 G k2 x) in H15. 
  assert(∀x : R,\{\ λ x y,y = k1 * F [x] \}\[x] = k1* F[x]).
  { intros. Function_ass. }
  assert(∀x : R,\{\ λ x y,y = k2 * G [x] \}\[x] = k2* G[x]).
  { intros. Function_ass. } 
  assert(\{\ λ x0 y,y = k1 * F [x0] + k2 * G [x0] \}\ = \{\ λ x0 y,y = \{\ λ x y,y = k1 * F [x] \}\[x0] + \{\ λ x y,y = k2 * G [x] \}\[x0] \}\).
  { apply AxiomI. split; intros.
    - applyAxiomII H18. destruct H18 as [x'[y'[H18 H19]]].
      apply AxiomII. exists x',y'. split; auto.
      rewrite H16. rewrite H17. auto.
    - applyAxiomII H18. destruct H18 as [x'[y'[H18 H19]]].
      apply AxiomII. exists x',y'. split; auto.
      rewrite H16 in H19. rewrite H17 in H19. auto. }
  assert(derivative \{\ λ x0 y,y = k1 * F [x0] + k2 * G [x0] \}\ x  
  (\{\ λ x y,y = k1 * F [x] \}\ '[x] + \{\ λ x y,y = k2 * G [x] \}\'[x])).
  { rewrite H18.
    apply Theorem5_4_1. red. exists ((k1 * F '[ x])); auto.
    red. exists ((k2 * G '[ x])); auto. }
  apply derEqual in H19 as H19'. split.
  rewrite H19'; auto. rewrite H19'.
  apply derEqual in H14. rewrite H14.
  apply derEqual in H15. rewrite H15.     
  rewrite H11. rewrite H13. 
  symmetry. Function_ass. 
  red. exists (G '[ x]); auto.
  red. exists (F '[ x]); auto.
Qed.
 
 
Lemma Lemma5_82 : ∀ (f h : Fun), Comp f h -> Function f -> Function h -> Function (f ◦ h).
Proof.
  intros. red. intros. applyAxiomII' H2;
  applyAxiomII' H3. destruct H2 as [y0[H2 H2']].
  destruct H3 as [y1[H3 H3']].
  assert(y0 = y1). 
  apply (H1 x _ _); auto.
  rewrite H4 in H2'. 
  apply(H0 y1); auto.
Qed. 



Theorem Theorem8_4 : ∀(f ψ F G:Fun)(a b c d:R), a < b -> c < d ->
  \(a,b\) ⊂ dom[f] -> Function ψ -> \(c,d\) ⊂ dom[ψ] ->  
  (∀t:R, t ∈ \(c,d\) -> derivable ψ t /\ ψ[t] ∈ \(a,b\)) -> 
  (∀x, x∈ \(a,b\)-> (∃t,t∈ \(c,d\) /\ Inverse_Function ψ f /\ x = ψ[t] /\ t = ψ﹣¹[x]))
   ->  Primitive_f f F \(a,b\) -> Comp F ψ /\ Comp G (ψ﹣¹)->
  Primitive_f \{\λ t y,y = f[ψ[t]] * ψ '[t] \}\ G \(c,d\) ->
  Primitive_f f \{\λ x y, y =G[ψ ﹣¹[x]] \}\ \(a,b\).
Proof.   
  intros f ψ F G a b c d. intros I1 I2 H H0 H1 H2 H3 H4 H5 H6.
  red. 
  red in H4. destruct H4 as [H4[H7[_[H8 H9]]]]. 
  red in H6. destruct H6 as [H6[H10[H11[H12 H13]]]].  
  destruct H5 as [H5 H5']. 
  assert (∀t:R, t ∈ \( c, d \) ->  
          derivative \{\ λ t y,y = (F ◦ ψ)[t] - G [t]\}\ t 0).
  { intros. 
    assert (J1: derivative (F ◦ ψ) t (F '[ψ[t]] * ψ '[t])).
    apply Theorem5_8; auto. apply H2 in H14; tauto.
    red. exists (F '[ψ[t]]). apply H9. apply H2. auto.
    assert (derivative \{\ λ t y,y = (F ◦ ψ)[t] - G[t] \}\ t
          ((F '[ψ[t]]) * ψ '[t] - G '[t])).
    assert (derivative G t (G '[t])).
    apply H13. auto.
    assert (derivative \{\ λ t0 y,y = (F ◦ ψ) [t0] - G [t0] \}\
    t ((F ◦ ψ) '[t] - G '[t])).
    apply (Theorem5_4_2 (F ◦ ψ) G t). red. 
    exists (F '[ ψ [t]] * ψ '[ t]). auto.
    red. exists (G '[ t]). auto.
    apply derEqual in J1. rewrite J1 in H16.
    auto.
    assert ((F '[ ψ [t]] * ψ '[ t] - G '[ t]) =
          (f[ ψ [t]] * ψ '[ t] - f[ ψ [t]] * ψ '[ t])).
    assert (ψ [t] ∈ \( a, b \)). apply H2 in H14. tauto. 
    apply H9 in H16. destruct H16. rewrite H17.
    apply H13 in H14. destruct H14.
    rewrite H18. 
    assert (\{\ λ t0 y, y = f [ψ [t0]] * ψ '[ t0] \}\ [t] =
               f [ψ [t]] * ψ '[t]).
    apply f_x. QED_function. apply AxiomII'. auto.
    rewrite H19. auto. rewrite H16 in H15. 
    cut ((f [ψ [t]] * ψ '[ t] - f [ψ [t]] * ψ '[ t])=0).
    intros. rewrite H17 in H15. auto. lra. }
  split; auto. split. 
  red. intros. applyAxiomII' H15. applyAxiomII' H16.
  rewrite H15;auto.
  split; auto. split. red. intros.
  apply AxiomII.
  exists G [(ψ ﹣¹) [z]]. apply AxiomII'. auto.
  intros. apply (H3 x ) in H15 as H3'; auto.
  destruct H3' as [t[H3'[H3'' [H3''' H3'''']]]].
  apply (Lemma8_4' (F ◦ ψ) G c d) in I2 as H16; auto.   
  destruct H16 as [C H16'].
  assert (∀x,x ∈ \( a, b \)->
          (F ◦ ψ) [(ψ ﹣¹) [x]] - G [(ψ ﹣¹) [x]] = C).
  { intros. assert ((ψ ﹣¹) [x0] ∈ \( c, d \)). apply H3 in H16.
    destruct H16 as [t'[H16[_[_ H16''']]]].
    rewrite H16''' in H16. auto. apply H16' in H17.
    auto. }  
  assert (∀t, t ∈ \( c, d \) -> (F ◦ ψ)[t] = F[ψ[t]]). 
  { intros. apply f_x. apply Lemma5_82; tauto. 
    apply AxiomII'. exists ψ[t0]. split. apply x_fx; auto.
    apply x_fx; auto. apply H8. apply H2 in H17. tauto. }
  assert (∀x, x ∈ \( a, b \) -> (F ◦ ψ)[(ψ ﹣¹) [x]] = F[x]).
  { intros. assert ((ψ ﹣¹) [x0] ∈ \( c, d \)). apply H3 in H18.
    destruct H18 as [t'[H18[_[_ H18''']]]].
    rewrite H18''' in H18. tauto. apply H17 in H19.
    rewrite H19.
    assert (ψ [(ψ ﹣¹) [x0]] = x0).
    apply (Lemma_Inverse' ψ f x0). auto. red in H3''.
    destruct H3''. rewrite <- H21. apply H. auto.
    rewrite H20. auto. } 
  assert (derivative F x (F '[ x]) /\ F '[ x] = f [x]).
  { apply H9 in H15 as H9'. auto. }
  assert (derivative \{\ λ x0 y, y = F [x0] - C \}\ x f[x]).
  { destruct H19. rewrite H20 in H19. 
    red in H19. destruct H19 as [_[H23 H24]].
    red. split. QED_function. split. 
    destruct H23 as [δ[H23 H23']].
    exists δ. split; auto. red. intros.
    apply AxiomII. exists (F [z] - C). apply AxiomII'. auto.
    assert (\{\λ x0 y, y =
            (\{\ λ x1 y0, y0 = F [x1] - C\}\ [x0] -
             \{\ λ x1 y0, y0 = F [x1] - C\}\ [x]) / 
            (x0 - x) \}\ = 
           \{\ λ x0 y, y = (F [x0] - F [x]) / (x0 - x) \}\ ).
     { assert (∀x0, \{\ λ x1 y0, y0 = F [x1]-C\}\[x0]=F[x0] - C).
       intros. function_ass.
       apply AxiomI. intros; split; intros; applyAxiomII H21;
       destruct H21 as [x0[y0[H21 H21']]];
       apply AxiomII; exists x0,y0; split; auto.
       rewrite (H19 x0) in H21'. rewrite (H19 x) in H21'.
       cut ((F [x0] - C - (F [x] - C)) =  (F [x0] - F [x])).
       intros. rewrite H22 in H21'; auto.
       lra.
       rewrite (H19 x0). rewrite (H19 x).
       cut ((F [x0] - C - (F [x] - C)) =  (F [x0] - F [x])).
       intros. rewrite H22. auto. lra. }
     rewrite H19. auto. } 
  assert (∀x : R,x ∈ \( a, b \) -> F [x] - C = G [(ψ ﹣¹) [x]]).
  { intros. apply H16 in H21 as H16''.
    apply H18 in H21 as H21'.
    lra. } 
  assert (derivative \{\ λ x0 y, y = G [(ψ ﹣¹) [x0]] \}\ x f[x]).
  { red. split. QED_function.
    red in H20. destruct H20 as [H20[H22 H23]].
    destruct H22 as [δ[H22 H22']].
    split. exists δ. split;auto.
    red. intros. apply AxiomII. exists G [(ψ ﹣¹) [z]].
    apply AxiomII'. auto. 
    assert (\{\ λ x0 y, y =
           (\{\ λ x1 y0, y0 = F [x1] - C \}\ [x0] -
            \{\ λ x1 y0, y0 = F [x1] - C \}\ [x]) / (x0 - x)\}\ =
            \{\ λ x0 y, y = (F [x0] - F [x])/(x0 - x)\}\).
    { assert (∀x0, \{\ λ x1 y0, y0 = F [x1]-C\}\[x0]=F[x0] - C).
       intros. function_ass.
      apply AxiomI. split; intros; applyAxiomII H25;
      destruct H25 as [x0[y0[H25 H25']]];
      apply AxiomII; exists x0,y0; split; auto.
      rewrite (H24 x0) in H25'. rewrite (H24 x) in H25'.
      cut ((F [x0] - C - (F [x] - C)) = (F [x0] - F [x])).
      intros. rewrite H26 in H25'. auto. lra.
      rewrite (H24 x0). rewrite (H24 x).
      cut ((F [x0] - C - (F [x] - C)) = (F [x0] - F [x])).
      intros. rewrite H26. auto. lra. }
    rewrite H24 in H23. clear H24.
    assert (\{\ λ x0 y , y =
           (\{\ λ x1 y0, y0 = G [(ψ ﹣¹) [x1]] \}\ [x0] -
         \{\ λ x1 y0,y0 =G [(ψ ﹣¹) [x1]] \}\ [x])/(x0 - x) \}\ =
 \{\ λ x0 y, y =(G [(ψ ﹣¹) [x0]] - G [(ψ ﹣¹) [x]])/(x0 - x)\}\).
    { assert (∀x0, \{\ λ x1 y0, y0 = G [(ψ ﹣¹) [x1]] \}\ [x0] =
      G [(ψ ﹣¹) [x0]] ).
      intros. function_ass.
      apply AxiomI. split; intros; applyAxiomII H25;
      destruct H25 as [x0[y0[H25 H25']]];
      apply AxiomII; exists x0,y0; split; auto.
      rewrite (H24 x0) in H25'. rewrite (H24 x) in H25'. auto.
      rewrite (H24 x0). rewrite (H24 x). auto. }
    rewrite H24. clear H24.
    red in H23. 
    destruct H23 as [H23[δ'[H24[H25 H26]]]]. 
    red. split. QED_function.  
    assert (Rbasic_fun.Rmin ((x-a)/2) ((b-x)/2) > 0).
    { unfold Rbasic_fun.Rmin. 
      destruct (Rle_dec ((x-a)/2) ((b-x)/2)); auto.  
      applyAxiomII H15.
      lra. applyAxiomII H15. lra. } 
    exists (Rbasic_fun.Rmin ((x-a)/2) ((b-x)/2)). split. auto.
    split. red. intros. apply AxiomII. 
    exists ((G [(ψ ﹣¹) [z]] - G [(ψ ﹣¹) [x]]) / (z - x)).
    apply AxiomII'. auto.
    intros. apply H26 in H28.
    destruct H28 as [δ''[H28 H29]].
    pose proof (Lemma1 δ''(Rbasic_fun.Rmin ((x-a)/2) ((b-x)/2))).
    destruct H28.
    apply H30 in H28 as H30'; auto. clear H30.
    destruct H30' as [δ'''[H30[H30' H30'']]].
    exists δ'''. split; auto. intros.
    assert (0 < Abs [x0 - x] < δ''). lra.
    apply H29 in H33.
    assert (\{\ λ x0 y,y = (F [x0] - F [x]) / (x0 - x) \}\ [x0]=
            (F [x0] - F [x]) / (x0 - x) ).
    function_ass. rewrite H34 in H33. clear H34.
    assert(\{\ λ x1 y, y = (G [(ψ ﹣¹) [x1]] - G [(ψ ﹣¹) [x]])
            / (x1 - x) \}\ [x0] = 
            (G [(ψ ﹣¹) [x0]] - G [(ψ ﹣¹) [x]])/ (x0 - x)).
    function_ass. rewrite H34. clear H34.
    assert (x0 ∈ \( a, b \)).
    { apply AxiomII.
      assert (0<Abs [x0 - x]<Rbasic_fun.Rmin((x-a)/2) ((b-x)/2)).
      lra. destruct H34. unfold Rbasic_fun.Rmin in H35.
      destruct (Rle_dec ((x - a) / 2) ((b - x) / 2)).
      - apply Abs_R in H35. destruct H35. 
        split. lra. lra.
      - apply Abs_R in H35. destruct H35. 
        split. lra. lra. }
    apply H21 in H34. apply H21 in H15 as H15'.
    rewrite <- H34. rewrite <- H15'.
    cut ((F [x0] - C - (F [x] - C)) = (F [x0] - F [x])).
    intros. rewrite H35. auto. lra. }
  apply derEqual in H22 as H22'. rewrite H22'. tauto.
Qed.



End A8_1.

Export A8_1.





 



  
  
  
  
  
  
  
  






























