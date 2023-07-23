Require Export A_6_3.

Module A9_1.

Lemma IsFun : ∀ (X Y : Type) (f : X -> Y),
  Function \{\ λ x y, y = f x \}\.
Proof.
  intros X Y f n v1 v2 H0 H1.
  applyAxiomII' H0. applyAxiomII' H1.
  rewrite H1. assumption.
Qed.

Lemma FunIsSeq : ∀ (f : nat -> R),
  IsSeq \{\ λ n y, y = f n \}\.
Proof.
  intros f. split; [apply IsFun | apply AxiomI].
  intros n. split; intros H0; applyAxiomII H0;
  apply AxiomII; auto.
  exists (f n). apply AxiomII'.
  reflexivity.
Qed.

Lemma FunValue : ∀ (X Y : Type) (f : X -> Y) (x : X)
  (o : Y), \{\ λ x y, y = f x \}\[x | o] = f x.
Proof.
  intros X Y f x o.
  apply f_x_T; [apply IsFun | apply AxiomII'].
  reflexivity.
Qed.

Lemma FunValueR : ∀ (X : Type) (f : X -> R) (x : X),
  \{\ λ t y, y = f t \}\[x] = f x.
Proof.
  intros X f n. apply FunValue.
Qed.

(* 定义：T为闭区间[a, b]的分割 *)
Definition seg (T : Seq) (a b :R) (n : nat) :=
  (0 < n)%nat /\ IsSeq T /\
  (∀ k : nat, T[k] < T[S k])
  /\ T[O] = a /\ T[n] = b.

(* Definition seg' (T : Seq) (a b :R) (n : nat) :=
  (0 < n)%nat /\ IsSeq T /\
  (∀ k : nat, T[k] < T[S k])
  /\ T[O] = a /\ T[n] = b/\. *)

(* 定义：x为分割T的模 *)
Definition segMold T n x :=
  (∃ k, (k < n)%nat /\ T[S k] - T[k] = x) /\
  (∀ m, (m < n)%nat -> T[S m] - T[m] <= x).
(*第Sk项减k项是x/\这个x最大*)

Definition mold T n := cR \{ λ x, segMold T n x \}.
(*取出x的意义？？*)

(* 引理：任何分割都存在模 *)
Lemma Lemma9_1_1 : ∀ T a b n, seg T a b n
  -> ∃ x, segMold T n x.
Proof.
  intros T a b n [H3 [H0 [H1 H2]]].
  clear H2. induction n as [|n IHn].
  - apply Nat.lt_irrefl in H3.
    contradiction.
  - apply lt_n_Sm_le in H3.
    apply le_lt_or_eq in H3 as [I1 | I1].
    + generalize (IHn I1);
      intros [x1 [[k [I2 I3]] I4]].
      destruct (Rlt_or_le x1 (T[S n] - T[n]))
        as [J1 | J1].
      * exists (T[S n] - T[n]). split.
        -- exists n. split; auto.
        -- intros m J2. apply lt_n_Sm_le in J2.
          apply le_lt_or_eq in J2 as [J2 | J2].
          ++ apply I4 in J2. lra.
          ++ rewrite J2. lra.
      * exists x1. split.
        -- exists k. split; auto.
        -- intros m J2. apply lt_n_Sm_le in J2.
          apply le_lt_or_eq in J2 as [J2 | J2]; auto.
          rewrite J2. assumption.
    + rewrite <- I1. exists (T[1%nat] - T[O]).
      split.
      * exists O. split; auto.
      * intros m J1. apply lt_n_Sm_le in J1.
        apply le_n_0_eq in J1.
        rewrite <- J1. lra.
Qed.

(* 引理：分割的任何小区间长度均小于等于模 *)
Lemma Lemma9_1_2 : ∀ T a b n k, (k < n)%nat ->
  seg T a b n -> T[S k] - T[k] <= (mold T n).
Proof.
  intros T a b n k H0 H1.
  apply Lemma9_1_1 in H1 as H2.
  destruct H2 as [x H2].
  assert (H3 : NotEmpty \{ λ x, segMold T n x \}).
  { exists x. apply AxiomII. assumption. }
  apply AxiomcR in H3.
  applyAxiomII H3. destruct H3 as [H3 H4].
  auto.
Qed.

(* 定义：分割T上的点集{ξ} *)
Definition segPoint (T ξ : Seq) :=
  IsSeq ξ /\ ∀ n, T[n] <= ξ[n] <= T[S n].
  
(* 定义：积分和 *)
Definition Riemann_Sum (T ξ : Seq)(f : Fun)(a b L: R)(n : nat) := 
  Function f /\ a < b /\ (\[a, b\]) ⊂ dom[f] /\ seg T a b (S n)
  /\ segPoint T ξ ->
  L = (Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n). 
  

(* 定义：J为f在区间[a, b]上的定积分 *)
Definition defIntegral (f : Fun) (a b J : R) :=
  Function f /\ a < b /\ (\[a, b\]) ⊂ dom[f] /\
  ∀ ε, 0<ε -> (∃ δ, 0<δ /\ (∀ T ξ n, seg T a b (S n) ->
    segPoint T ξ -> (mold T (S n) < δ)
    -> Abs[Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n - J] < ε)).


Lemma Increase_seg:∀ T a b n, seg T a b n -> 
(∀n1 n2,(n1 < n2)%nat -> T[n1] < T[n2]).
Proof.
  intros T a b n H0 n1 n2. 
  destruct H0 as [H0[H0'[H0''[H1 H1']]]].
  induction n2 as [|n2 IHn2].
  - intro H2. exfalso. apply (Nat.nlt_0_r n1). auto.
  - destruct (Nat.lt_total n1 n2) as [H2 | [H2 | H2]]; intro H3.
    + apply Rlt_trans with (r2 := T[n2]); auto.
    + rewrite H2. apply H0''.
    + apply lt_n_Sm_le in H3. exfalso.
      apply lt_not_le in H2. auto.
Qed.

Lemma equal_seg: ∀ T a b n, seg T a b n -> 
(∀n1 n2, T[n1] = T[n2] -> (n1 = n2)%nat).
Proof.
  intros. destruct (classic (n1 = n2%nat)).
  auto. apply nat_total_order in H1.
  destruct H1. apply (Increase_seg T a b n H) in H1.
  lra. apply (Increase_seg T a b n H) in H1.
  lra.
Qed.

End A9_1.

Export A9_1.
