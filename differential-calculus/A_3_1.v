Require Export A_2_3.

Module A3_1.



(* 3.1 函数极限的概念 *)

(* 定义函数类型 *)
Definition Fun : Type := set (prod R R).
Definition plus_fun (f g : Fun) :=
   (\{\ λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\ y = f[x] + g[x] \}\).
Notation "f \+ g" := (plus_fun f g) (at level 45, left associativity).
Definition plus'_fun (f :Fun) (a:R):=
   (\{\ λ x y, x ∈ dom[f] /\ y = f[x] + a \}\).
Notation "f \\+ a" := (plus'_fun f a)(at level 45, left associativity).

Definition sub_fun (f g : Fun) :=
   (\{\ λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\ y = f[x] - g[x] \}\).
Notation "f \- g" := (sub_fun f g)(at level 45, left associativity).

Definition mult_fun (f g : Fun) :=
   (\{\ λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\ y = f[x] * g[x] \}\).
Notation "f ** g" := (mult_fun f g) (at level 40, left associativity).
Definition mult'_fun (f : Fun)(a : R) :=
   (\{\ λ x y, x ∈ dom[f] /\ y = f[x] * a \}\).
Notation "f \* a" := (mult'_fun f a)(at level 40, left associativity).

Definition div_fun (f g : Fun) :=
   (\{\ λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\ g[x] <> 0 /\ y = f[x] / g[x] \}\).
Notation "f // g" := (div_fun f g)(at level 40, left associativity).
Definition div'_fun (f: Fun)(a :R) :=
   (\{\ λ x y, x ∈ dom[f] /\ f[x] <> 0 /\ y = a / f[x]  \}\).
Notation "a /// f" := (div'_fun f a)(at level 40, left associativity).

(***函数的四则运算***)
Definition plus_point f1 f2 (x : R) : R := f1 x + f2 x.
Definition minus_point f1 f2 (x : R) : R := f1 x - f2 x.


(* 区间上的有界函数 *)
Definition IntervalBoundedFun (f : sR2) (D : sR) : Prop :=
    Function f /\ D ⊂ dom[f]
    /\ ∃ M : R, (∀ x : R, x ∈ D -> Abs[f[x]] <= M).

(* 最大值 *)
Definition MaxValue (f : Fun) (D : sR) (m : R) :=
  D ⊂ dom[f] /\ (∀ x, x ∈ D -> f[x] <= m) /\ (∃ x0, x0 ∈ D /\ f[x0] = m).

(* 最小值 *)
Definition MinValue (f : Fun) (D : sR) (m : R) :=
  D ⊂ dom[f] /\ (∀ x, x ∈ D -> m <= f[x]) /\ (∃ x0, x0 ∈ D /\ f[x0] = m).
(***这里的function f 是否需要加上???***)

(* 区间上的单调函数 *)

(* 区间上的增函数 *)
Definition IntervalIncreaseFun (f : sR2) (D : sR) : Prop :=
    Function f /\ D ⊂ dom[f] 
    /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D
    -> x1 < x2 -> f[x1] <= f[x2]).
(* 区间上的严格增函数 *)
Definition IntervalStrictlyIncreaseFun (f : sR2) (D : sR) : Prop :=
    Function f /\ D ⊂ dom[f] 
    /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D
    -> x1 < x2 -> f[x1] < f[x2]).

(* 区间上的减函数 *)
Definition IntervalDecreaseFun (f : sR2) (D : sR) :=
    Function f /\ D ⊂ dom[f] 
    /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D
    -> x1 < x2 -> f[x1] >= f[x2]).
(* 区间上的严格减函数 *)
Definition IntervalStrictlyDecreaseFun (f : sR2) (D : sR) :=
    Function f /\ D ⊂ dom[f] 
    /\ (∀ (x1 x2 : R), x1 ∈ D -> x2 ∈ D
    -> x1 < x2 -> f[x1] > f[x2]).

(* 区间上的单调函数 *)
Definition IntervalMonotonicFun (f : sR2) (D : sR) :=
  IntervalIncreaseFun f D \/ IntervalDecreaseFun f D.
  
(* 区间上的严格单调函数 *)
Definition IntervalStrictlyMonotonicFun (f : sR2) (D : sR) :=
  IntervalStrictlyIncreaseFun f D
  \/ IntervalStrictlyDecreaseFun f D.

(* x 趋于 ∞ 时的极限 *)

(* 定义1 : x 趋于 +∞ 时的极限*)
Definition limit_pos_inf (f : Fun) (A : R) :=
  Function f /\ (∃ a, \[a, +∞ \) ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ M, M >= a /\ (∀ x, x > M -> Abs[f[x] - A] < ε))).

(* 定义1' : x 趋于 -∞ 时的极限*)
Definition limit_neg_inf (f : Fun) (A : R) :=
  Function f /\ (∃ a, \( -∞ , a \] ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ M, M <= a /\ (∀ x, x < M -> Abs[f[x] - A] < ε))).

(* 定义1'' : x 趋于 ∞ 时的极限*)
Definition limit_inf (f : Fun) (A : R) :=
  Function f /\ (∃ a, \( -∞ , -a \] ∪ \[a, +∞ \) ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ M, M >= a /\
     (∀ x, Abs[x] > M -> Abs[f[x] - A] < ε))).

(* 定理: 函数极限的等价 *)
Theorem limit_inf_equal : ∀ (f : Fun) (A : R),
  (limit_inf f A <-> (limit_pos_inf f A /\ limit_neg_inf f A)).
Proof.
  intros f A. split; intro H0.
  - split.
    + destruct H0 as [H0 [a [H1 H2]]]. split; auto. exists a. split.
      * intros z I1. apply H1. apply AxiomII. right. apply I1.
      * intros ε H3. apply H2 in H3 as H4. destruct H4 as [M [H4 H5]].
        exists M. split; auto. intros x H6. apply H5.
        apply Rlt_le_trans with (r2 := x); auto. apply Abs_neg_pos.
    + destruct H0 as [H0 [a [H1 H2]]]. split; auto. exists (-a). split.
      * intros z I1. apply H1. apply AxiomII. left. apply I1.
      * intros ε H3. apply H2 in H3 as H4. destruct H4 as [M [H4 H5]].
        exists (-M). split; try lra. intros x H6. apply H5.
        assert (H7 : M < -x). lra.
        apply Rlt_le_trans with (r2 := -x); auto.
        rewrite Abs_eq_neg. apply Abs_neg_pos.
  - destruct H0 as [[H0 [a1 [H1 H2]]] [H3 [a2 [H4 H5]]]].
    split; auto. assert (H6 : ∃ a, a > a1 /\ -a < a2).
    { destruct (Rlt_or_le a1 (-a2)) as [I1 | I1].
      - exists (-a2+1). split; lra.
      - exists (a1+1). split; lra. }
    destruct H6 as [a [H6 H7]]. exists a. split.
    + intros z I1. applyAxiomII I1. destruct I1 as [I1 | I1].
      * apply H4. applyAxiomII I1. apply AxiomII. lra.
      * apply H1. applyAxiomII I1. apply AxiomII. lra.
    + intros ε H8. apply H2 in H8 as H9. apply H5 in H8 as H10.
      destruct H9 as [M1 [H9 H11]]. destruct H10 as [M2 [H10 H12]].
      assert (H13 : ∃ M, M >= a /\ M >= M1 /\ (-M) <= M2).
      { destruct (Rlt_or_le M1 (-M2)) as [I2 | I2].
        - destruct (Rlt_or_le a (-M2)) as [I3 | I3].
          + exists (-M2). repeat split; lra.
          + exists a. repeat split; lra.
        - destruct (Rlt_or_le a M1) as [I3 | I3].
          + exists M1. repeat split; lra.
          + exists a. repeat split; lra. }
      destruct H13 as [M [H13 [H14 H15]]]. exists M. split; try lra.
      intros x H16. destruct (Rlt_or_le x 0) as [H17 | H17].
      * rewrite Abs_lt in H16; auto. apply H12. lra.
      * apply Rle_ge in H17. rewrite Abs_ge in H16; auto.
        apply H11. lra.
Qed.

(* x 趋于 x0 时的极限 *)

(* 定义2 : 函数极限的 ε-δ 定义 *)
Definition limit (f : Fun) (x0 A : R) := 
  Function f /\ (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, 0 < Abs[x-x0] < δ -> Abs[f[x] - A] < ε))).

Definition limitU (f : Fun) (x0 A δ' : R) := 
  Function f /\ (δ' > 0 /\ Neighbor0 x0 δ' ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, 0 < Abs[x-x0] < δ -> Abs[f[x] - A] < ε))).

(* 定义3 : 右极限 *)
Definition limit_pos (f : Fun) (x0 A : R) := 
  Function f /\ (∃ δ', δ' > 0 /\ rightNeighbor0 x0 δ' ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, x0 < x < x0+δ -> Abs[f[x] - A] < ε))).

(* 定义3 : 左极限 *)
Definition limit_neg (f : Fun) (x0 A : R) := 
  Function f /\ (∃ δ', δ' > 0 /\ leftNeighbor0 x0 δ' ⊂ dom[f] /\
     (∀ ε : R, ε > 0 -> ∃ δ, 0 < δ < δ' /\
       (∀ x, x0-δ < x < x0 -> Abs[f[x] - A] < ε))).

(* 定理3.1 *)
Theorem Theorem3_1 : ∀ (f : Fun) (x0 A : R),
  limit f x0 A <-> (limit_pos f x0 A /\ limit_neg f x0 A).
Proof.
  intros f x0 A. split; intro H0.
  - destruct H0 as [H0 [δ' [H1 [H2 H3]]]]. split.
    + split; auto. exists δ'. split; auto. split.
      * intros z I1. apply H2. applyAxiomII I1. apply AxiomII. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
      * intros ε H4. apply H3 in H4 as H5. destruct H5 as [δ [H5 H6]].
        exists δ. split; auto. intros x H7. apply H6. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
    + split; auto. exists δ'. split; auto. split.
      * intros z I1. apply H2. applyAxiomII I1. apply AxiomII. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
      * intros ε H4. apply H3 in H4 as H5. destruct H5 as [δ [H5 H6]].
        exists δ. split; auto. intros x H7. apply H6. split.
        -- apply Abs_not_eq_0. lra.
        -- apply Abs_R. split; lra.
  - destruct H0 as [[H0 [δ0' [H1 [H2 H3]]]] [H4 [δ1' [H5 [H6 H7]]]]].
    split; auto. assert (H8 : ∃ δ' : R, δ' > 0 /\ δ' <= δ0' /\ δ' <= δ1').
    { destruct (Rlt_or_le δ0' δ1') as [I1 | I1].
      - exists δ0'. split; lra.
      - exists δ1'. split; lra. }
    destruct H8 as [δ' [H8 [H9 H10]]]. exists δ'. split; auto. split.
    + intros z I1. applyAxiomII I1. destruct I1 as [I1 I2].
      apply Abs_R in I2. destruct (Rlt_or_le (z-x0) 0) as [I3 | I3].
      * apply H6. apply AxiomII. split; lra.
      * apply H2. apply AxiomII. apply Abs_not_eq_0 in I1. split; lra.
    + intros ε H11. apply H3 in H11 as H12. apply H7 in H11 as H13.
      destruct H12 as [δ0 [H12 H14]]. destruct H13 as [δ1 [H13 H15]].
      assert (H16 : ∃ δ : R, 0 < δ < δ' /\ δ <= δ0 /\ δ <= δ1).
      { destruct (Rlt_or_le δ0 δ1) as [I1 | I1].
        - destruct (Rlt_or_le δ0 δ') as [I2 | I2].
          + exists δ0. split; lra.
          + exists (δ'/2). repeat split; lra.
        - destruct (Rlt_or_le δ1 δ') as [I2 | I2].
          + exists δ1. split; lra.
          + exists (δ'/2). repeat split; lra. }
      destruct H16 as [δ [H16 [H17 H18]]].
      exists δ. split; auto. intros x H19. destruct H19 as [H19 H20].
      apply Abs_not_eq_0 in H19. apply Abs_R in H20.
      destruct (Rlt_or_le (x-x0) 0) as [H21 | H21];
      [apply H15 | apply H14]; lra.
Qed.

End A3_1.

Export A3_1.