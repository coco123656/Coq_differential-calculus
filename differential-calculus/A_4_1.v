Require Export A_3_5.

Module A4_1.

(* 4.1 连续性的概念 *)
(* 定义1：函数在一点的连续性 *)
Definition Continuous (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit f x0 f[x0].

(* 左连续 *)
Definition ContinuousLeft (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit_neg f x0 f[x0].

(* 右连续 *)
Definition ContinuousRight (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit_pos f x0 f[x0].

(* 定义：函数在开区间上的连续 *)
Definition ContinuousOpen (f : Fun) (a b : R) :=
  ∀ x, a < x < b -> Continuous f x.

(* 定义：函数在闭区间上的连续 *)
Definition ContinuousClose (f : Fun) (a b : R) :=
  ContinuousOpen f a b /\ ContinuousRight f a
  /\ ContinuousLeft f b.
(*以上两个没LaTeX*)

(*f在一点处连续的充要条件*)
Theorem Theorem4_1 : ∀ (f : Fun) (x0 : R), Continuous f x0 <->
  ContinuousLeft f x0 /\ ContinuousRight f x0.
Proof.
  intros; split; intros.
  - unfold Continuous in *. split. destruct H.
    + unfold ContinuousLeft. split; auto.
      apply Theorem3_1 in H0; tauto.
    + unfold ContinuousRight; split. tauto.
      destruct H. apply Theorem3_1 in H0; tauto.
  - unfold Continuous. destruct H. unfold ContinuousLeft in H.
    split. tauto. unfold ContinuousRight in H0.
    destruct H. destruct H0. apply <- Theorem3_1. split; auto.
Qed.

(*可去间断点*)
Definition RemoveDiscontinuous (f : Fun) (x0 A : R) :=
  (x0 ∉ dom[f] /\ limit f x0 A) \/ ( x0 ∈ dom[f] /\ limit f x0 A /\ f[x0] <> A).


(*跳跃间断点*)
Definition LeapDiscontinuous (f : Fun) (x0 : R) :=
  ∃ A B, limit_pos f x0 A /\ limit_neg f x0 B /\ A <> B.

(*第一类间断点*)
Definition firstDiscontinuous (f : Fun) (x0 A : R) :=
  RemoveDiscontinuous f x0 A \/ LeapDiscontinuous f x0.

(*第二类间断点*)
Definition secondDiscontinuous (f : Fun) (x0 : R) :=
  (∀A, ~ limit_pos f x0 A) \/ (∀B, ~ limit_neg f x0 B).

(*间断点*)
Definition Discontinuous (f : Fun) (x0 A : R) :=
  firstDiscontinuous f x0 A \/ secondDiscontinuous f x0.


End A4_1.

Export A4_1.