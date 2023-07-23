Require Export Classical.
Require Export Coq.Reals.RIneq.
Require Export Coq.Logic.Epsilon.
Require Export Lra.
Open Scope R_scope.

Module A0.

Set Implicit Arguments.

Notation "∀ x .. y , P" := (forall x, .. (forall y , P) ..)
(at level 200, x binder, y binder, right associativity, 
format "'[' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y , P) ..)
(at level 200, x binder, y binder, right associativity,
format "'[' ∃ x .. y ']' , P" ) :type_scope.

Notation "'λ' x .. y , t " := ( fun x => .. (fun y => t) ..)
(at level 200, x binder, y binder, right associativity,
format "'[' 'λ' x .. y ']' , t" ).

(* 定义：集合 *)
Parameter set :Type -> Type.
(*输入一个类型A输出一个类型set A*)

(* 定义：属于 *)
Parameter In : ∀ (A : Type), A -> (set A) -> Prop.
Notation "x ∈ A" :=(In x A) (at level 80).

(* 公理I：外延公理 *)
Axiom AxiomI : ∀ (A :Type) (x y : (set A)), x = y
  <-> (∀ z : A, z ∈ x <-> z ∈ y).

Parameter Classifier : ∀ (A: Type) (P: A -> Prop), (set A).
Notation "\{ P \}" := (Classifier P) (at level 0).

(* 公理II：分类公理图式 *)
Axiom AxiomII : ∀ (A : Type) (b : A) (P : A -> Prop),
  b ∈ \{ P \} <-> (P b).

Ltac applyAxiomII H := apply -> AxiomII in H; simpl in H.

(* 定义: 非空集 *)
Definition NotEmpty (A : Type) (S : (set A)) := ∃ (x : A), x ∈S.

(* 定义：两集合中的关系 *)
Definition Union (A : Type) (x y :(set A)) : (set A) :=
  \{ λ z : A, z ∈ x \/ z ∈ y  \} .
Notation "x ∪ y" := (Union x y)(at level 65, right associativity).

Definition Intersection (A : Type) (x y :(set A)) : (set A) :=
  \{ λ z : A, z ∈ x /\ z ∈ y \}.
Notation "x ∩ y" := (Intersection x y)(at level 65, right associativity).

Definition NotIn (A: Type) (x : A) (y : (set A)) : Prop :=
  ~(x ∈ y).
Notation "x ∉ y" := (NotIn x y)(at level 80).

Definition Complement (A : Type) (x : (set A)) := \{ λ y : A, y ∉ x \}.
Notation "～ x" := (Complement x) (at level 5, right associativity).

Definition Difference (A : Type) (x y :(set A)) : (set A) := x ∩ (～ y).
Notation "x \~ y" := (Difference x y)(at level 50).

(* 定义：空集 *)
Definition Empty (A : Type) := \{λ x : A, x <> x \}.

(* 定义：满集 *)
Definition Full (A : Type)  := \{ λ x : A, x = x \}.

(* 非空集性质 *)
Theorem not_empty : ∀ (X : Type) (A : set X), A <> (Empty X) <-> NotEmpty A.
Proof.
  intros X A. unfold NotEmpty. split; intro H0.
  - apply not_all_not_ex. intro H1.
    apply H0. apply AxiomI. intro z; split; intro H2.
    + exfalso. apply (H1 z). auto.
    + exfalso. applyAxiomII H2. apply H2; auto.
  - intro H1. destruct H0 as [x H2]. rewrite H1 in H2. applyAxiomII H2.
    contradiction.
Qed.

(* Definition Inter (A : Type) (x : set (set A)) :=
    \{ λ z : A, ∀ y, y ∈ x -> z ∈ y  \}.
Notation "∩ x" := (Inter x) (at level 55,right associativity).

Definition Un (A : Type) (x : set (set A)) :=
    \{ λ z : A, ∃ y, y ∈ x /\ z ∈ y \}.
Notation "∪ x" := (Un x) (at level 55, right associativity). *)

Definition Contain (A : Type) (x y : (set A))  := ∀ z, z ∈ x -> z ∈ y.
Notation "x ⊂ y" := (Contain x y) (at level 70).

Definition Singleton (A: Type) (x : A): (set A) := \{ λ z, z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0,right associativity).
(* Parameter c : ∀ (A : Type) (x : (set A)) ,  A.
Inductive nn : Type :=.
Theorem aa : 1=0.
Proof.
  assert (exists n: nn, n=n).
  { Print Empty. exists (@c nn (@Empty nn)). auto. }
  destruct H. destruct x.
Qed.
Axiom Axiomc : ∀ (A : Type) (x : (set A)), NotEmpty x -> (c x) ∈ x. *)
(* 公理：选择公理 *)
(* Parameter c : ∀ (A : Type) (x : (set A)) (a : A),  A. *)
(*选择函数*)

Fact tf : ∀ P, {P} + {~P}.

Proof.
  intros. assert ({x:bool | if x then P else ~P}).
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true; auto.
    - exists false; auto. }
  destruct H. destruct x. auto. auto.
Qed.

Definition c {T : Type} (x : (set T)) (a : T) :=
  match tf (NotEmpty x) with
  | left l => proj1_sig (constructive_indefinite_description _ l)
  | right _ => a
  end.

Theorem Axiomc : ∀ (A : Type) (x : (set A)) a , NotEmpty x -> (c x a) ∈ x.
Proof.
  intros. unfold c. destruct tf. 
  destruct (constructive_indefinite_description _ n); auto.
  contradiction.
Qed.

Definition cR (x : (set R)) : R := c x 0.
Definition cN (x : (set nat)) : nat := c x 0%nat.


Theorem AxiomcR : ∀ (x : (set R)), NotEmpty x -> (cR x) ∈ x.
Proof. intros x H0. unfold cR. apply Axiomc. auto. Qed.
Theorem AxiomcN : ∀ (x : (set nat)), NotEmpty x -> (cN x) ∈ x.
Proof. intros x H0; apply Axiomc; auto. Qed.
Theorem ChooseSingleton : ∀ (A : Type) (x a : A), c [x] a = x.
Proof.
  intros A x a. assert (H0 : c [x] a ∈ [x]).
  { apply Axiomc. unfold NotEmpty. exists x. apply <- AxiomII. auto. }
  applyAxiomII H0. apply H0.
Qed.

Theorem ChooseSingletonR : ∀ (x : R), cR [x] = x.
Proof. intros x; apply ChooseSingleton. Qed.

Theorem ChooseSingletonN : ∀ (x : nat), cN [x] = x.
Proof. intros x; apply ChooseSingleton. Qed.

Print prod.
Print pair.
Locate "*".

(* 定义：有序对 *)  
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Notation "[ x , y ]" := (pair x y).


Definition fst (X Y : Type) (p : (prod X Y)) : X := 
  match p with 
  | [x , y] => x
  end.

Definition snd (X Y : Type) (p : (prod X Y)) : Y := 
  match p with
  | [x , y] => y
  end.

Theorem ProdEqual : ∀ (X Y : Type) (x u : X) (y v : Y),
  [x , y] = [u , v] -> x = u /\ y = v.
Proof.
  intros X Y x u y v H0. assert (H1 : fst [x, y] = x). auto.
  assert (H2 : snd [x, y] = y). auto. 
  assert (H3 : fst [u, v] = u). auto.
  assert (H4 : snd [u, v] = v). auto. split.
  - rewrite H0 in H1. rewrite H1 in H3. auto .
  - rewrite H0 in H2. rewrite H2 in H4. auto.
Qed.

Definition Relation (X Y : Type) (r : set (prod X Y)) : Prop :=
  ∀ z , z ∈ r -> (∃ x y, z = [x , y]). 

(* 引入符号((x, y) : ...) *)
Definition Classifier_P (X Y : Type) (P : X -> Y -> Prop) :=
  \{ λ u , ∃ x y, u = [x , y] /\ P x y \}.
Notation "\{\ P \}\ " := (Classifier_P P) (at level 0).

Definition Comosition (X Y Z : Type) (r : set (prod Y Z)) (s : set (prod X Y))
  : set (prod X Z) := \{\ λ x z, (∃ y, [x, y] ∈ s /\ [y, z] ∈ r ) \}\.
Notation "r ◦ s" := (Comosition r s) (at level 50,no associativity).

Definition Inverse (X Y : Type)( r : set (prod X Y)) : set (prod Y X) :=
  \{\ λ x y, [y, x] ∈ r  \}\.
Notation "r ﹣¹" := (Inverse r) (at level 5).

Theorem AxiomII' : ∀ (X Y : Type) (x : X) (y : Y) (P : X -> Y -> Prop),
  [x, y] ∈ \{\ P \}\  <-> P x y.
Proof.
  intros X Y x y P. split;intros.
  - applyAxiomII H. destruct H as [u [v [H H0]]].
    apply ProdEqual in H. destruct H. rewrite H,H1. auto.
  - apply AxiomII. exists x, y. split;auto.
Qed.

Ltac applyAxiomII' H := apply -> AxiomII' in H; simpl in H.


(* 定义：函数  *)
Definition Function (A B : Type) (f : set (prod A B)) : Prop := 
  ∀ x y z, [x, y] ∈ f -> [x, z] ∈ f -> y = z.

(* 定义：定义域 *)
Definition Domain (X Y : Type) (f : set (prod X Y)) :=
  \{ λ x, ∃ y, [x, y] ∈ f \}.
Notation "dom[ f ]" := (Domain f) (at level 5).

(* 定义：值域 *)
Definition Range (X Y : Type) (f : set (prod X Y)) :=
  \{ λ y, ∃ x, [x, y] ∈ f \}.
Notation "ran[ f ]" := (Range f) (at level 5).

(* 定义：值 *)
Definition Value (X Y : Type) (f : set (prod X Y)) (x : X) (o : Y) :=
  c \{ λ y, [x, y] ∈ f \} o.
Definition ValueR (X : Type) (f : set (prod X R)) (x : X) :=
  cR \{ λ y, [x, y] ∈ f \}.
Definition ValueN (X : Type) (f : set (prod X nat)) (x : X) :=
  cN \{ λ y, [x, y] ∈ f \}.
Notation "f [ x | y ]" := (Value f x y) (at level 5).
Notation "f [ x ]" := (ValueR f x) (at level 5).
Notation "f \[ x \]" := (ValueN f x) (at level 5).

Theorem f_x_T : ∀ (X Y : Type) (f : set (prod X Y)) (x : X)(y o : Y) ,
  Function f -> [x, y] ∈ f -> f[ x | o ] = y.
Proof.
  intros X Y f x y o H1 H2. unfold Value.
  assert (H3 : \{ λ y0 : Y, [x, y0] ∈ f \} = [y]). 
  { apply AxiomI. intro z. split; intro H3.
    + apply -> AxiomII in H3. simpl in H3. apply  AxiomII.
      apply H1 with (x := x);auto.
    + apply AxiomII. apply -> AxiomII in H3. simpl in H3.
      rewrite H3. auto. }
  rewrite H3. apply ChooseSingleton.
Qed.

Theorem f_x : ∀ (X : Type) (f : set (prod X R)) (x : X)(y : R) ,
  Function f -> [x, y] ∈ f -> f[ x ] = y.
Proof.
  intros X f x y H1 H2. unfold ValueR. 
  assert (H3 : \{ λ y0 : R, [x, y0] ∈ f \} = [y]). 
  { apply AxiomI. intro z. split; intro H3.
    + applyAxiomII H3. apply  AxiomII.
      apply (H1 x);auto.
    + apply AxiomII. applyAxiomII H3. rewrite H3. auto. }
  rewrite H3. apply ChooseSingletonR. 
Qed.

Theorem f_x_N : ∀ (X : Type) (f : set (prod X nat)) (x : X)(y : nat) ,
  Function f -> [x, y] ∈ f -> f\[ x \] = y.
Proof.
  intros X f x y H1 H2. unfold ValueN. 
  assert (H3 : \{ λ y0 : nat, [x, y0] ∈ f \} = [y]). 
  { apply AxiomI. intro z. split; intro H3.
    + applyAxiomII H3. apply  AxiomII.
      apply (H1 x);auto.
    + apply AxiomII. applyAxiomII H3. rewrite H3. auto. }
  rewrite H3. apply ChooseSingletonN. 
Qed.

Theorem fx_ran : ∀ (X : Type) (f : set (prod X R)) (x : X),
  Function f -> x ∈ dom[f] -> f[x] ∈ ran[f].
Proof.
  intros X f x H0 H1. applyAxiomII H1.
  destruct H1 as [y H1]. apply f_x in H1 as H2; auto. rewrite H2.
  apply <- AxiomII. exists x; auto.
Qed.

Theorem fx_ran_N : ∀ (X : Type) (f : set (prod X nat)) (x : X),
  Function f -> x ∈ dom[f] -> f\[x\] ∈ ran[f].
Proof.
  intros X f x H0 H1. applyAxiomII H1.
  destruct H1 as [y H1]. apply f_x_N in H1 as H2; auto. rewrite H2.
  apply <- AxiomII. exists x; auto.
Qed.

Theorem x_fx_T : ∀ (X Y : Type) (f : set (prod X Y)) (x : X) (o : Y),
  Function f -> x ∈ dom[f] -> [x, f[x | o]] ∈ f.
Proof.
  intros X Y f x o H0 H1. apply -> AxiomII in H1; simpl in H1.
  destruct H1 as [y H1]. apply f_x_T with (o := o) in H1 as H2; auto.
  rewrite H2; auto.
Qed.

Theorem x_fx : ∀ (X : Type) (f : set (prod X R)) (x : X),
  Function f -> x ∈ dom[f] -> [x, f[x]] ∈ f.
Proof.
  intros X f x H0 H1. applyAxiomII H1.
  destruct H1 as [y H1]. apply f_x in H1 as H2; auto.
  rewrite H2; auto.
Qed.

Theorem x_fx_N : ∀ (X : Type) (f : set (prod X nat)) (x : X),
  Function f -> x ∈ dom[f] -> [x, f\[x\]] ∈ f.
Proof.
  intros X f x H0 H1. applyAxiomII H1.
  destruct H1 as [y H1]. apply f_x_N in H1 as H2; auto.
  rewrite H2; auto.
Qed.

(* 定义:笛卡尔积 *)
Definition Cartesian (X Y : Type) (x : set X) (y : set Y) :=
  \{\ λ u v, u ∈ x /\ v ∈ y \}\.
Notation "x × y" := (Cartesian x y)(at level 2, right associativity).

(* 定义:限制 *)
Definition Restriction (X Y : Type) (f : set (prod X Y)) (x : set X) :=
  f ∩ (x × (Full Y)).
Notation "f | [ x ]" := (Restriction f x)(at level 30).

Lemma RF_F : ∀ (X : Type) (f : set (prod X R)) (x : set X),
  Function f -> (Function (f|[x])).
Proof.
  intros X f x H0. unfold Function. intros x0 y z H1 H2. applyAxiomII H1.
  destruct H1 as [H1 H3]. applyAxiomII H2. destruct H2 as [H2 H4].
  unfold Function in H0. apply H0 with (x := x0); auto.
Qed.

Theorem RestrictFun : ∀ (X : Type) (f : set (prod X R)) (x : set X),
  Function f -> (Function (f|[x]) /\ dom[f|[x]] = (x ∩ (dom[f]))
  /\ (∀ x0, x0 ∈ dom[f|[x]] -> (f|[x])[x0] = f[x0] )).
Proof. 
  intros X f x H0. split; [auto | split]. 
  - apply RF_F; auto.
  - apply AxiomI. split; intro H1.
    + applyAxiomII H1. destruct H1 as [v H2]. 
      applyAxiomII H2. destruct H2 as [H3 H4].
      apply AxiomII. split.
      * applyAxiomII' H4. destruct H4; auto.
      * apply AxiomII. exists v; auto.
    + applyAxiomII H1. destruct H1 as [H2 H3].
      applyAxiomII H3. destruct H3 as [v H4]. apply AxiomII.
      exists v. apply AxiomII. split; auto. apply AxiomII'.
      split; auto. apply AxiomII. auto.
  - intros x0 H1. applyAxiomII H1. destruct H1 as [y H2]. 
    apply f_x in H2 as H4.
    + rewrite H4. applyAxiomII H2. destruct H2 as [H3 H5].
      apply f_x in H3; auto.
    + apply RF_F; auto.
Qed.

Lemma RF_F' : ∀ (X : Type) (f : set (prod X nat)) (x : set X),
  Function f -> (Function (f|[x])).
Proof.
  intros X f x H0. unfold Function. intros x0 y z H1 H2. applyAxiomII H1.
  destruct H1 as [H1 H3]. applyAxiomII H2. destruct H2 as [H2 H4].
  unfold Function in H0. apply H0 with (x := x0); auto.
Qed.


Theorem RestrictFun_N : ∀ (X : Type) (f : set (prod X nat)) (x : set X),
  Function f -> (Function (f|[x]) /\ dom[f|[x]] = (x ∩ (dom[f]))
  /\ (∀ y, y ∈ dom[f|[x]] -> (f|[x])\[y\] = f\[y\] )).
Proof.
  intros X f x H0. split; [auto | split].
  - apply RF_F'; auto.
  - apply AxiomI. split; intro H1.
    + applyAxiomII H1. destruct H1 as [v H2]. 
      applyAxiomII H2. destruct H2 as [H3 H4].
      apply AxiomII. split.
      * applyAxiomII' H4. destruct H4; auto.
      * apply AxiomII. exists v; auto.
    + applyAxiomII H1. destruct H1 as [H2 H3].
      applyAxiomII H3. destruct H3 as [v H4]. apply AxiomII.
      exists v. apply AxiomII. split; auto. apply AxiomII'.
      split; auto. apply AxiomII. auto.
  - intros x0 H1. applyAxiomII H1. destruct H1 as [y H2].  
    apply f_x_N in H2 as H4.
    + rewrite H4. applyAxiomII H2. destruct H2 as [H3 H5].
      apply f_x_N in H3; auto.
    + apply RF_F'; auto.
Qed.

(* 定义:1_1函数 *)
Definition Function1_1 (A B : Type) (f : set (prod A B)) : Prop :=
  Function f /\ Function (f﹣¹).

Theorem RestrictFun1_1 : ∀ (X : Type) (f : set (prod X R)) (x : set X),
  Function1_1 f -> Function1_1 (f|[x]).
Proof.
  intros X f x H0. destruct H0 as [H0 H1].  
  apply RestrictFun with (x := x) in H0 as H2. 
  destruct H2 as [H2[H3 H4]]. split; auto.
  unfold Function. intros x0 y0 z0 H5 H6. applyAxiomII' H5. applyAxiomII' H6.
  applyAxiomII H5. applyAxiomII H6. destruct H5 as [H5 H7].
  destruct H6 as [H6 H8]. apply H1 with (x := x0); apply <- AxiomII'; auto.
Qed.

Theorem RestrictFun1_1_N : ∀ (X : Type) (f : set (prod X nat)) (x : set X),
  Function1_1 f -> Function1_1 (f|[x]).
Proof.
  intros X f x H0. destruct H0 as [H0 H1].  
  apply RestrictFun_N with (x := x) in H0 as H2. 
  destruct H2 as [H2[H3 H4]]. split; auto.
  unfold Function. intros x0 y0 z0 H5 H6. applyAxiomII' H5. applyAxiomII' H6.
  applyAxiomII H5. applyAxiomII H6. destruct H5 as [H5 H7].
  destruct H6 as [H6 H8]. apply H1 with (x := x0); apply <- AxiomII'; auto.
Qed.


Definition IsNaturalNumber (r : R) : Prop := ∃ (n : nat), (INR n) = r.
Definition IsInteger (r : R) : Prop := ∃ (n : Z), (IZR n) = r.

Theorem Rlt_not_ge : forall r1 r2 : R, r1 < r2 -> ~ (r1 >= r2).
Proof.  
  intros r1 r2 H0 H1. destruct H1 as [H1 | H1].
  - apply Rlt_asym in H0. auto.
  - rewrite H1 in H0. apply Rlt_asym in H0 as H2. contradiction.
Qed.
(***Rlt_asym ∀r1 r2 : R,r1 < r2 -> ~ r2 < r1***)

Theorem Rgt_not_le : forall r1 r2 : R, r1 > r2 -> ~(r1 <= r2).
Proof.
  intros r1 r2 H0 H1. destruct H1 as [H1 | H1].
  - apply Rlt_asym in H0. auto.
  - rewrite H1 in H0. apply Rlt_asym in H0 as H2. auto.
Qed.

Theorem Rge_lt :∀ r1 r2 : R, r1 >= r2 \/ r1 < r2.
Proof.
  intros r1 r2. 
  destruct (total_order_T r1 r2) as [[I1 | I1] | I1].
  - right; auto.
  - left; right; auto.
  - left; left; auto.
Qed.
(***total_order_T: ∀r1 r2 : R,{r1 < r2} + {r1 = r2} + {r2 < r1}***)

(* 定义：绝对值函数 *)
Definition Abs := \{\ λ x y , (x <0 /\ y = -x) \/ (x >= 0 /\ y = x) \}\.

(***Abs是函数***)
Theorem Fun_Abs : Function Abs.
Proof.
  unfold Abs. unfold Function. intros x y z H0 H1.
  applyAxiomII' H0. applyAxiomII' H1.
  destruct H0,H1,H0,H.
  + rewrite <- H2 in H1. auto. 
  + apply Rlt_not_ge in H. contradiction.
  + apply Rlt_not_ge in H0. contradiction.
  + rewrite <- H2 in H1. auto.
Qed.

Definition sR := (set R).
Definition R2 := prod R R.
Definition sR2 := (set R2).

(* 非空有限集 *)
Definition NotEmptyFinite {X : Type} (A : set X) : Prop :=
     ∃ (n : nat) (f : set (prod nat X)),
    Function1_1 f /\ dom[f] = \{ λ (x : nat), (x <= n)%nat \} /\ ran[f] = A.

(* 有限集 *)
Definition Finite {X : Type} (A : set X) : Prop :=
    NotEmptyFinite A \/ A = (Empty X).

(* 单点集为非空有限集 *)
Theorem SingletonFinite : ∀ (X : Type) (x : X), (NotEmptyFinite ([x])).
Proof. 
  intros X a. unfold NotEmptyFinite.
  exists 0%nat, \{\ λ u v, u = 0%nat /\ v = a \}\. split; [idtac | split].
  - split.
    + unfold Function. intros x y z J1 J2. applyAxiomII' J1. applyAxiomII' J2.
      destruct J2 as [J2 J3]. rewrite J3. apply J1.
    + unfold Function. intros x y z J1 J2. applyAxiomII' J1. applyAxiomII' J1.
      applyAxiomII' J2. applyAxiomII' J2. destruct J2 as [J2 J3].
      rewrite J2. apply J1.
  - apply AxiomI. intro z; split; intro J1.
    + applyAxiomII J1. destruct J1 as [y J1].
      applyAxiomII' J1. destruct J1 as [J1 J2]. apply <- AxiomII. 
      rewrite J1. auto.
    + applyAxiomII J1. apply <- AxiomII. exists a. apply <- AxiomII'. split; auto.
      apply le_n_0_eq in J1. rewrite J1. auto.
  - apply AxiomI. intro z; split; intro J1.
    + applyAxiomII J1. destruct J1 as [x J1].
      applyAxiomII' J1. destruct J1 as [J1 J2].
      rewrite J2. apply <- AxiomII; auto.
    + applyAxiomII J1. apply <- AxiomII. exists 0%nat. apply <- AxiomII'. 
      split; auto.
Qed.

(* 小于等于某个数的自然数集为非空有限集 *)
Theorem NatFinite : ∀ n : nat, NotEmptyFinite \{ λ u : nat, (u <= n)%nat \}.
Proof.
  intros n. unfold NotEmptyFinite.
  exists n, \{\ λ u v, v = u /\ (u <= n)%nat \}\.
  split; [idtac | split].
  - split.
    + unfold Function. intros x y z H0 H1. applyAxiomII' H0.
      applyAxiomII' H1. destruct H1 as [H1 H2]. rewrite H1. apply H0.
    + unfold Function. intros x y z H0 H1. applyAxiomII' H0.
      applyAxiomII' H1. applyAxiomII' H0. applyAxiomII' H1.
      destruct H0 as [H0 H2]. rewrite <- H0. apply H1.
  - apply AxiomI; intro z; split; intro H0.
    + applyAxiomII H0. destruct H0 as [y H0]. applyAxiomII' H0.
      apply <- AxiomII. apply H0.
    + apply <- AxiomII. exists z. apply <- AxiomII'. applyAxiomII H0.
      split; auto.
  - apply AxiomI; intro z; split; intro H0.
    + applyAxiomII H0. destruct H0 as [x H0]. applyAxiomII' H0.
      apply <- AxiomII. destruct H0 as [H0 H1]. rewrite H0; auto.
    + apply <- AxiomII. exists z. apply <- AxiomII'. applyAxiomII H0.
      split; auto.
Qed.

(* 有限集的子集为有限集 *)
Theorem SubSetFinite_R : ∀ (A B : set R),
    Finite A -> B ⊂ A -> Finite B.
Proof.
  intros A B H0 H1. unfold Finite in *. destruct H0 as [H0 | H0].
  - destruct classic with (P := B = Empty R) as [H2 | H2];
    [right | idtac]; auto. apply not_empty in H2. left.
    unfold NotEmptyFinite in H0. destruct H0 as [n H0].
    generalize dependent H0. generalize dependent A. generalize dependent B.
    induction n as [|n H0].
    + intros B H2 A H0 H1. destruct H1 as [f [H1 [H3 H4]]].
      assert (H5 : A = [f[0%nat]]).
      { apply AxiomI. intro z; split; intro J1.
        - rewrite <- H4 in J1. applyAxiomII J1.
          destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
          { apply <- AxiomII. exists z. auto. }
          rewrite H3 in J2. applyAxiomII J2.
          apply le_n_0_eq in J2. apply <- AxiomII. rewrite J2.
          symmetry. apply f_x; auto. apply H1.
        - applyAxiomII J1. rewrite <- H4. apply <- AxiomII.
          exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
          { rewrite H3. apply <- AxiomII. auto. }
          applyAxiomII J2. destruct J2 as [y J2].
          apply f_x in J2 as J3; try apply H1. rewrite J1. rewrite J3.
          auto. }
      assert (H6 : B = [f[0%nat]]).
      { apply AxiomI. intro z; split; intro H6.
        - rewrite <- H5. auto.
        - unfold NotEmpty in H2. destruct H2 as [x H2]. assert (J1 : x ∈ A).
          auto. rewrite H5 in J1. applyAxiomII H6.
          applyAxiomII J1. rewrite H6. rewrite <- J1. auto. }
      rewrite H6. apply SingletonFinite.
    + intros B H2 A H1 H3. destruct H3 as [f [H3 [H4 H5]]].
      assert (H6 : ∃ C, C = \{ λ x : nat,(x <= n)%nat \}).
      { exists \{ λ x : nat,(x <= n)%nat \}; auto. }
      destruct H6 as [C H6]. assert (H7 : Function1_1 f). auto.
      destruct H7 as [H7 H8]. assert (H9 : ran[f|[C]] ∪ [f[S n]] = A).
      { apply AxiomI. intro z; split; intro J1.
        - applyAxiomII J1. destruct J1 as [J1 | J1].
          + rewrite <- H5. applyAxiomII J1.
            destruct J1 as [x J1]. applyAxiomII J1.
            destruct J1 as [J1 J2]. apply <- AxiomII. exists x. auto.
          + rewrite <- H5. applyAxiomII J1. rewrite J1. 
            apply fx_ran; auto. rewrite H4. apply <- AxiomII. apply le_n.
        - rewrite <- H5 in J1. applyAxiomII J1. destruct J1 as [x J1]. 
          assert (J2 : x ∈ dom[f]).
          { apply <- AxiomII. exists z. auto. }
          rewrite H4 in J2. applyAxiomII J2. 
          apply Nat.le_succ_r in J2 as J3. apply <- AxiomII.
          destruct J3 as [J3 | J3].
          + left. apply <- AxiomII. exists x. apply <- AxiomII. split; auto.
            apply <- AxiomII'. split.
            * rewrite H6. apply <- AxiomII. auto.
            * apply <- AxiomII. auto.
          + right. apply <- AxiomII. symmetry. apply f_x; auto. rewrite <- J3.
            auto. }
      apply RestrictFun with (x := C) in H7 as H10.
      destruct H10 as [H10 [H11 H12]].
      assert (H13 : dom[f|[C]] = C).
      { rewrite H11. apply AxiomI. intro z; split; intro J1.
        - apply -> AxiomII in J1. apply J1.
        - apply <- AxiomII. split; auto. rewrite H4. apply <- AxiomII.
          rewrite H6 in J1. apply -> AxiomII in J1; simpl in J1.
          apply le_S. auto. }
      assert (H14 : (B \~ ([f[S n]])) ⊂ (A \~ ([f[S n]]))).
      { intros z J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 J2]. apply -> AxiomII in J2; simpl in J2.
        apply <- AxiomII. split; auto. apply <- AxiomII. auto. }
      assert (H20 : ran[ f | [C]] = A \~ [f [S n]]).
      { apply AxiomI. intro z; split; intro K1.
        - apply <- AxiomII. split.
          + rewrite <- H9. apply <- AxiomII. left; auto.
          + apply <- AxiomII. intro K2. apply -> AxiomII in K1;
            simpl in K1. destruct K1 as [x K1]. apply -> AxiomII in K2;
            simpl in K2. assert (K3 : x ∈ (C ∩ dom[f])).
            { rewrite <- H11. apply <- AxiomII. exists z. auto. }
            apply -> AxiomII in K3; simpl in K3.
            destruct K3 as [K3 K4]. rewrite H6 in K3.
            apply -> AxiomII in K3; simpl in K3.
            apply -> AxiomII in K1; simpl in K1.
            assert (K5 : [S n, z] ∈ f).
            { assert (L1 : S n ∈ dom[f]).
              { rewrite H4. apply <- AxiomII. auto. }
              apply -> AxiomII in L1; simpl in L1.
              destruct L1 as [y L1]. apply f_x in L1 as L2; auto.
              rewrite K2. rewrite L2. auto. }
            destruct K1 as [K1 K6]. assert (K7 : x = S n).
            { apply H8 with (x := z); apply <- AxiomII'; auto. }
            rewrite K7 in K3. assert (K8 : (n < S n)%nat).
            { apply Nat.lt_succ_diag_r. }
            apply lt_not_le in K8. auto.
        - apply -> AxiomII in K1; simpl in K1.
          destruct K1 as [K1 K2]. rewrite <- H9 in K1.
          apply -> AxiomII in K2; simpl in K2.
          apply -> AxiomII in K1; simpl in K1.
          destruct K1 as [K1 | K1]; auto. exfalso. auto. }
      destruct classic with (P := f[S n] ∈ B) as [H15 | H15].
      * destruct classic with (P := (B \~ ([f[S n]])) = Empty R) as [J1 | J1].
        -- assert (J2 : B = [f[S n]]).
          { apply AxiomI. intro z; split; intro K1.
            - apply <- AxiomII. apply NNPP. intro K2.
              assert (K3 : z ∈ (Empty R)).
              { rewrite <- J1. apply <- AxiomII. split; auto. apply <- AxiomII.
                intro L1. apply K2. apply -> AxiomII in L1. auto. }
              apply -> AxiomII in K3; simpl in K3. auto.
            - apply -> AxiomII in K1; simpl in K1. rewrite K1. auto. }
          rewrite J2. apply SingletonFinite.
        -- assert (J2 : NotEmptyFinite (B \~ [f[S n]])).
          { apply H0 with (A := (A \~ [f[S n]])); auto.
            - apply not_empty. auto.
            - exists (f|[C]). split; [idtac | split]; auto.
              + apply RestrictFun1_1. auto.
              + rewrite H13. auto. }
          unfold NotEmptyFinite in J2. destruct J2 as [n0 [f0 [J3 [J4 J5]]]].
          unfold NotEmptyFinite. exists (S n0), (f0 ∪ [[(S n0), f[S n]]]).
          split; [idtac | split].
          ++ split.
            ** unfold Function. intros x y z K1 K2.
              apply -> AxiomII in K1; simpl in K1.
              apply -> AxiomII in K2; simpl in K2.
              destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
                +++ destruct J3 as [J3 J6]. apply J3 with (x := x); auto.
                +++ exfalso. apply -> AxiomII in K2; simpl in K2.
                  apply ProdEqual in K2. destruct K2 as [K2 K3].
                  assert (K4 : x ∈ dom[f0]).
                  { apply <- AxiomII. exists y; auto. }
                  rewrite J4 in K4. apply -> AxiomII in K4; simpl in K4.
                  rewrite K2 in K4. assert (K5 : (n0 < S n0)%nat).
                  { apply Nat.lt_succ_diag_r. }
                  apply lt_not_le in K5. auto.
              --- destruct K2 as [K2 | K2].
                +++ exfalso. apply -> AxiomII in K1; simpl in K1.
                  apply ProdEqual in K1. destruct K1 as [K1 K3].
                  assert (K4 : x ∈ dom[f0]).
                  { apply <- AxiomII. exists z; auto. }
                  rewrite J4 in K4. apply -> AxiomII in K4; simpl in K4.
                  rewrite K1 in K4. assert (K5 : (n0 < S n0)%nat).
                  { apply Nat.lt_succ_diag_r. }
                  apply lt_not_le in K5. auto.
                +++ apply -> AxiomII in K1; simpl in K1.
                    apply -> AxiomII in K2; simpl in K2.
                    apply ProdEqual in K1. apply ProdEqual in K2.
                    destruct K2 as [K2 K3]. rewrite K3. apply K1.
            ** unfold Function. intros x y z K1 K2.
              apply -> AxiomII' in K1; simpl in K1.
              apply -> AxiomII' in K2; simpl in K2.
              apply -> AxiomII in K1; simpl in K1.
              apply -> AxiomII in K2; simpl in K2.
              destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
                +++ apply J3 with (x := x); apply <- AxiomII'; auto.
                +++ exfalso. apply -> AxiomII in K2; simpl in K2.
                  apply ProdEqual in K2. destruct K2 as [K2 K3].
                  assert (K4 : x ∈ ran[f0]).
                  { apply <- AxiomII. exists y. auto. }
                  rewrite J5 in K4. apply -> AxiomII in K4; simpl in K4.
                  destruct K4 as [K4 K5]. apply -> AxiomII in K5; simpl in K5.
                  apply K5. apply <- AxiomII. auto.
              --- destruct K2 as [K2 | K2].
                +++ exfalso. apply -> AxiomII in K1; simpl in K1.
                  apply ProdEqual in K1. destruct K1 as [K1 K3].
                  assert (K4 : x ∈ ran[f0]).
                  { apply <- AxiomII. exists z. auto. }
                  rewrite J5 in K4. apply -> AxiomII in K4; simpl in K4.
                  destruct K4 as [K4 K5]. apply -> AxiomII in K5; simpl in K5.
                  apply K5. apply <- AxiomII. auto.
                +++ apply -> AxiomII in K1; simpl in K1.
                    apply -> AxiomII in K2; simpl in K2.
                    apply ProdEqual in K1. apply ProdEqual in K2.
                    destruct K2 as [K2 K3]. rewrite K2. apply K1.
          ++ apply AxiomI. intro z; split; intro K1.
            ** apply -> AxiomII in K1; simpl in K1. destruct K1 as [y K1].
              apply -> AxiomII in K1; simpl in K1. destruct K1 as [K1 | K1].
              --- assert (K2 : z ∈ dom[f0]).
                { apply <- AxiomII. exists y. auto. }
                rewrite J4 in K2. apply -> AxiomII in K2; simpl in K2.
                apply <- AxiomII. apply le_S. auto.
              --- apply -> AxiomII in K1; simpl in K1.
                apply ProdEqual in K1. destruct K1 as [K1 K2].
                apply <- AxiomII. rewrite K1. auto.
            ** apply -> AxiomII in K1; simpl in K1.
              apply Nat.le_succ_r in K1 as K2. apply <- AxiomII.
              destruct K2 as [K2 | K2].
              --- assert (K3 : z ∈ dom[f0]).
                { rewrite J4. apply <- AxiomII. auto. }
                apply -> AxiomII in K3; simpl in K3.
                destruct K3 as [y K3]. exists y. apply <- AxiomII.
                left; auto.
              --- exists (f[S n]). apply <- AxiomII. right.
                apply <- AxiomII. rewrite K2. auto.
          ++ apply AxiomI. intro z; split; intro K1.
            ** apply -> AxiomII in K1; simpl in K1. destruct K1 as [x K1].
              apply -> AxiomII in K1; simpl in K1. destruct K1 as [K1 | K1].
              ---  assert (K2 : z ∈ ran[f0]).
                { apply <- AxiomII. exists x. auto. }
                rewrite J5 in K2. apply -> AxiomII in K2; simpl in K2.
                apply K2.
              --- apply -> AxiomII in K1; simpl in K1.
                apply ProdEqual in K1. destruct K1 as [K1 K2]. rewrite K2.
                auto.
            ** apply <- AxiomII.
              destruct classic with (P := z = f[S n]) as [K2 | K2].
              --- exists (S n0). apply <- AxiomII. right. apply <- AxiomII.
                rewrite K2. auto.
              --- assert (K3 : z ∈ ran[f0]).
                { rewrite J5. apply <- AxiomII. split; auto. apply <- AxiomII.
                  intro K3. apply K2. apply -> AxiomII in K3. auto. }
                apply -> AxiomII in K3; simpl in K3. destruct K3 as [x K3].
                exists x. apply <- AxiomII. left. auto.
      * assert (H16 : B ⊂ (A \~ ([f[S n]]))).
        { assert (I1 : (B \~ ([f[S n]])) = B).
          { apply AxiomI. intro z; split; intro I1.
            - apply -> AxiomII in I1; simpl in I1. apply I1.
            - apply <- AxiomII. split; auto. apply <- AxiomII. intro I2.
              apply -> AxiomII in I2; simpl in I2. rewrite <- I2 in H15.
              auto. }
          rewrite <- I1. auto. }
        apply H0 with (A := (A \~ [f[S n]])); auto. exists (f|[C]).
        split; [idtac | split]; auto.
        -- apply RestrictFun1_1. auto.
        -- rewrite H13. auto.
  - right. apply AxiomI. intro z; split; intro H2.
    + rewrite <- H0. auto.
    + exfalso. apply -> AxiomII in H2; simpl in H2. auto.
Qed.

Theorem SubSetFinite_N : ∀ (A B : set nat),
    Finite A -> B ⊂ A -> Finite B.
Proof.
  intros A B H0 H1. unfold Finite in *. destruct H0 as [H0 | H0].
  - destruct classic with (P := B = Empty nat) as [H2 | H2];
    [right | idtac]; auto. apply not_empty in H2. left.
    unfold NotEmptyFinite in H0. destruct H0 as [n H0].
    generalize dependent H0. generalize dependent A. generalize dependent B.
    induction n as [|n H0].
    + intros B H2 A H0 H1. destruct H1 as [f [H1 [H3 H4]]].
      assert (H5 : A = [f\[0%nat\]]).
      { apply AxiomI. intro z; split; intro J1.
        - rewrite <- H4 in J1. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
          { apply <- AxiomII. exists z. auto. }
          rewrite H3 in J2. apply -> AxiomII in J2; simpl in J2.
          apply le_n_0_eq in J2. apply <- AxiomII. rewrite J2.
          symmetry. apply f_x_N; auto. apply H1.
        - apply -> AxiomII in J1; simpl in J1. rewrite <- H4. apply <- AxiomII.
          exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
          { rewrite H3. apply <- AxiomII. auto. }
          apply -> AxiomII in J2; simpl in J2. destruct J2 as [y J2].
          apply f_x_N in J2 as J3; try apply H1. rewrite J1. rewrite J3.
          auto. }
      assert (H6 : B = [f\[0%nat\]]).
      { apply AxiomI. intro z; split; intro H6.
        - rewrite <- H5. auto.
        - unfold NotEmpty in H2. destruct H2 as [x H2]. assert (J1 : x ∈ A).
          auto. rewrite H5 in J1. apply -> AxiomII in H6; simpl in H6.
          apply -> AxiomII in J1; simpl in J1. rewrite H6. rewrite <- J1.
          auto. }
      rewrite H6. apply SingletonFinite.
    + intros B H2 A H1 H3. destruct H3 as [f [H3 [H4 H5]]].
      assert (H6 : ∃ C, C = \{ λ x : nat,(x <= n)%nat \}).
      { exists \{ λ x : nat,(x <= n)%nat \}; auto. }
      destruct H6 as [C H6]. assert (H7 : Function1_1 f). auto.
      destruct H7 as [H7 H8]. assert (H9 : ran[f|[C]] ∪ [f\[S n\]] = A).
      { apply AxiomI. intro z; split; intro J1.
        - apply -> AxiomII in J1; simpl in J1. destruct J1 as [J1 | J1].
          + rewrite <- H5. apply -> AxiomII in J1; simpl in J1.
            destruct J1 as [x J1]. apply -> AxiomII in J1; simpl in J1.
            destruct J1 as [J1 J2]. apply <- AxiomII. exists x. auto.
          + rewrite <- H5. apply -> AxiomII in J1; simpl in J1.
            rewrite J1. apply fx_ran_N; auto. rewrite H4. apply <- AxiomII.
            apply le_n.
        - rewrite <- H5 in J1. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
          { apply <- AxiomII. exists z. auto. }
          rewrite H4 in J2. apply -> AxiomII in J2; simpl in J2.
          apply Nat.le_succ_r in J2 as J3. apply <- AxiomII.
          destruct J3 as [J3 | J3].
          + left. apply <- AxiomII. exists x. apply <- AxiomII. split; auto.
            apply <- AxiomII'. split.
            * rewrite H6. apply <- AxiomII. auto.
            * apply <- AxiomII. auto.
          + right. apply <- AxiomII. symmetry. apply f_x_N; auto.
            rewrite <- J3. auto. }
      apply RestrictFun_N with (x := C) in H7 as H10.
      destruct H10 as [H10 [H11 H12]].
      assert (H13 : dom[f|[C]] = C).
      { rewrite H11. apply AxiomI. intro z; split; intro J1.
        - apply -> AxiomII in J1. apply J1.
        - apply <- AxiomII. split; auto. rewrite H4. apply <- AxiomII.
          rewrite H6 in J1. apply -> AxiomII in J1; simpl in J1.
          apply le_S. auto. }
      assert (H14 : (B \~ ([f\[S n\]])) ⊂ (A \~ ([f\[S n\]]))).
      { intros z J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 J2]. apply -> AxiomII in J2; simpl in J2.
        apply <- AxiomII. split; auto. apply <- AxiomII. auto. }
      assert (H20 : ran[ f | [C]] = A \~ [f \[S n\]]).
      { apply AxiomI. intro z; split; intro K1.
        - apply <- AxiomII. split.
          + rewrite <- H9. apply <- AxiomII. left; auto.
          + apply <- AxiomII. intro K2. apply -> AxiomII in K1;
            simpl in K1. destruct K1 as [x K1]. apply -> AxiomII in K2;
            simpl in K2. assert (K3 : x ∈ (C ∩ dom[f])).
            { rewrite <- H11. apply <- AxiomII. exists z. auto. }
            apply -> AxiomII in K3; simpl in K3.
            destruct K3 as [K3 K4]. rewrite H6 in K3.
            apply -> AxiomII in K3; simpl in K3.
            apply -> AxiomII in K1; simpl in K1.
            assert (K5 : [S n, z] ∈ f).
            { assert (L1 : S n ∈ dom[f]).
              { rewrite H4. apply <- AxiomII. auto. }
              apply -> AxiomII in L1; simpl in L1.
              destruct L1 as [y L1]. apply f_x_N in L1 as L2; auto.
              rewrite K2. rewrite L2. auto. }
            destruct K1 as [K1 K6]. assert (K7 : x = S n).
            { apply H8 with (x := z); apply <- AxiomII'; auto. }
            rewrite K7 in K3. assert (K8 : (n < S n)%nat).
            { apply Nat.lt_succ_diag_r. }
            apply lt_not_le in K8. auto.
        - apply -> AxiomII in K1; simpl in K1.
          destruct K1 as [K1 K2]. rewrite <- H9 in K1.
          apply -> AxiomII in K2; simpl in K2.
          apply -> AxiomII in K1; simpl in K1.
          destruct K1 as [K1 | K1]; auto. exfalso. auto. }
      destruct classic with (P := f\[S n\] ∈ B) as [H15 | H15].
      * destruct classic with (P := (B \~ ([f\[S n\]])) =
          Empty nat) as [J1 | J1].
        -- assert (J2 : B = [f\[S n\]]).
          { apply AxiomI. intro z; split; intro K1.
            - apply <- AxiomII. apply NNPP. intro K2.
              assert (K3 : z ∈ (Empty nat)).
              { rewrite <- J1. apply <- AxiomII. split; auto. apply <- AxiomII.
                intro L1. apply K2. apply -> AxiomII in L1. auto. }
              apply -> AxiomII in K3; simpl in K3. auto.
            - apply -> AxiomII in K1; simpl in K1. rewrite K1. auto. }
          rewrite J2. apply SingletonFinite.
        -- assert (J2 : NotEmptyFinite (B \~ [f\[S n\]])).
          { apply H0 with (A := (A \~ [f\[S n\]])); auto.
            - apply not_empty. auto.
            - exists (f|[C]). split; [idtac | split]; auto.
              + apply RestrictFun1_1_N. auto.
              + rewrite H13. auto. }
          unfold NotEmptyFinite in J2. destruct J2 as [n0 [f0 [J3 [J4 J5]]]].
          unfold NotEmptyFinite. exists (S n0), (f0 ∪ [[(S n0), f\[S n\]]]).
          split; [idtac | split].
          ++ split.
            ** unfold Function. intros x y z K1 K2.
              apply -> AxiomII in K1; simpl in K1.
              apply -> AxiomII in K2; simpl in K2.
              destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
                +++ destruct J3 as [J3 J6]. apply J3 with (x := x); auto.
                +++ exfalso. apply -> AxiomII in K2; simpl in K2.
                  apply ProdEqual in K2. destruct K2 as [K2 K3].
                  assert (K4 : x ∈ dom[f0]).
                  { apply <- AxiomII. exists y; auto. }
                  rewrite J4 in K4. apply -> AxiomII in K4; simpl in K4.
                  rewrite K2 in K4. assert (K5 : (n0 < S n0)%nat).
                  { apply Nat.lt_succ_diag_r. }
                  apply lt_not_le in K5. auto.
              --- destruct K2 as [K2 | K2].
                +++ exfalso. apply -> AxiomII in K1; simpl in K1.
                  apply ProdEqual in K1. destruct K1 as [K1 K3].
                  assert (K4 : x ∈ dom[f0]).
                  { apply <- AxiomII. exists z; auto. }
                  rewrite J4 in K4. apply -> AxiomII in K4; simpl in K4.
                  rewrite K1 in K4. assert (K5 : (n0 < S n0)%nat).
                  { apply Nat.lt_succ_diag_r. }
                  apply lt_not_le in K5. auto.
                +++ apply -> AxiomII in K1; simpl in K1.
                    apply -> AxiomII in K2; simpl in K2.
                    apply ProdEqual in K1. apply ProdEqual in K2.
                    destruct K2 as [K2 K3]. rewrite K3. apply K1.
            ** unfold Function. intros x y z K1 K2.
              apply -> AxiomII' in K1; simpl in K1.
              apply -> AxiomII' in K2; simpl in K2.
              apply -> AxiomII in K1; simpl in K1.
              apply -> AxiomII in K2; simpl in K2.
              destruct K1 as [K1 | K1].
              --- destruct K2 as [K2 | K2].
                +++ apply J3 with (x := x); apply <- AxiomII'; auto.
                +++ exfalso. apply -> AxiomII in K2; simpl in K2.
                  apply ProdEqual in K2. destruct K2 as [K2 K3].
                  assert (K4 : x ∈ ran[f0]).
                  { apply <- AxiomII. exists y. auto. }
                  rewrite J5 in K4. apply -> AxiomII in K4; simpl in K4.
                  destruct K4 as [K4 K5]. apply -> AxiomII in K5; simpl in K5.
                  apply K5. apply <- AxiomII. auto.
              --- destruct K2 as [K2 | K2].
                +++ exfalso. apply -> AxiomII in K1; simpl in K1.
                  apply ProdEqual in K1. destruct K1 as [K1 K3].
                  assert (K4 : x ∈ ran[f0]).
                  { apply <- AxiomII. exists z. auto. }
                  rewrite J5 in K4. apply -> AxiomII in K4; simpl in K4.
                  destruct K4 as [K4 K5]. apply -> AxiomII in K5; simpl in K5.
                  apply K5. apply <- AxiomII. auto.
                +++ apply -> AxiomII in K1; simpl in K1.
                    apply -> AxiomII in K2; simpl in K2.
                    apply ProdEqual in K1. apply ProdEqual in K2.
                    destruct K2 as [K2 K3]. rewrite K2. apply K1.
          ++ apply AxiomI. intro z; split; intro K1.
            ** apply -> AxiomII in K1; simpl in K1. destruct K1 as [y K1].
              apply -> AxiomII in K1; simpl in K1. destruct K1 as [K1 | K1].
              --- assert (K2 : z ∈ dom[f0]).
                { apply <- AxiomII. exists y. auto. }
                rewrite J4 in K2. apply -> AxiomII in K2; simpl in K2.
                apply <- AxiomII. apply le_S. auto.
              --- apply -> AxiomII in K1; simpl in K1.
                apply ProdEqual in K1. destruct K1 as [K1 K2].
                apply <- AxiomII. rewrite K1. auto.
            ** apply -> AxiomII in K1; simpl in K1.
              apply Nat.le_succ_r in K1 as K2. apply <- AxiomII.
              destruct K2 as [K2 | K2].
              --- assert (K3 : z ∈ dom[f0]).
                { rewrite J4. apply <- AxiomII. auto. }
                apply -> AxiomII in K3; simpl in K3.
                destruct K3 as [y K3]. exists y. apply <- AxiomII.
                left; auto.
              --- exists (f\[S n\]). apply <- AxiomII. right.
                apply <- AxiomII. rewrite K2. auto.
          ++ apply AxiomI. intro z; split; intro K1.
            ** apply -> AxiomII in K1; simpl in K1. destruct K1 as [x K1].
              apply -> AxiomII in K1; simpl in K1. destruct K1 as [K1 | K1].
              ---  assert (K2 : z ∈ ran[f0]).
                { apply <- AxiomII. exists x. auto. }
                rewrite J5 in K2. apply -> AxiomII in K2; simpl in K2.
                apply K2.
              --- apply -> AxiomII in K1; simpl in K1.
                apply ProdEqual in K1. destruct K1 as [K1 K2]. rewrite K2.
                auto.
            ** apply <- AxiomII.
              destruct classic with (P := z = f\[S n\]) as [K2 | K2].
              --- exists (S n0). apply <- AxiomII. right. apply <- AxiomII.
                rewrite K2. auto.
              --- assert (K3 : z ∈ ran[f0]).
                { rewrite J5. apply <- AxiomII. split; auto. apply <- AxiomII.
                  intro K3. apply K2. apply -> AxiomII in K3. auto. }
                apply -> AxiomII in K3; simpl in K3. destruct K3 as [x K3].
                exists x. apply <- AxiomII. left. auto.
      * assert (H16 : B ⊂ (A \~ ([f\[S n\]]))).
        { assert (I1 : (B \~ ([f\[S n\]])) = B).
          { apply AxiomI. intro z; split; intro I1.
            - apply -> AxiomII in I1; simpl in I1. apply I1.
            - apply <- AxiomII. split; auto. apply <- AxiomII. intro I2.
              apply -> AxiomII in I2; simpl in I2. rewrite <- I2 in H15.
              auto. }
          rewrite <- I1. auto. }
        apply H0 with (A := (A \~ [f\[S n\]])); auto. exists (f|[C]).
        split; [idtac | split]; auto.
        -- apply RestrictFun1_1_N. auto.
        -- rewrite H13. auto.
  - right. apply AxiomI. intro z; split; intro H2.
    + rewrite <- H0. auto.
    + exfalso. apply -> AxiomII in H2; simpl in H2. auto.
Qed.

(* 最大值 *)
Definition maxR (A : sR) (r : R) := r ∈ A /\ (∀ x, x ∈ A -> x <= r).
Definition maxN (A : set nat) (n : nat) :=
    n ∈ A /\ (∀ x, x ∈ A -> x <= n)%nat.

(* 非空有限的自然数集有最大值 *)
Theorem finite_maxN : ∀ (A : set nat),
    NotEmptyFinite A -> (∃ n : nat, maxN A n).
Proof.
  intros A H1. unfold NotEmptyFinite in H1. destruct H1 as [n H1].
  generalize dependent H1. generalize dependent A. induction n as [|n H1].
  - intros A H1. destruct H1 as [f [H1 [H2 H3]]].
    assert (H4 : \{ λ x : nat, (x <= 0)%nat \} = [0%nat]).
    { apply AxiomI. intro z; split; intro I1.
      - apply <- AxiomII. apply -> AxiomII in I1. simpl in I1. symmetry.
        apply le_n_0_eq. auto.
      - apply -> AxiomII in I1; simpl in I1. rewrite I1. apply <- AxiomII.
        apply le_n. }
    rewrite H4 in H2. assert (H5 : A = [f\[0%nat\]]).
    { apply AxiomI. intro z; split; intro J1.
      - apply <- AxiomII. rewrite <- H3 in J1.
        apply -> AxiomII in J1; simpl in J1. destruct J1 as [x J1].
        assert (J2 : x ∈ dom[f]).
        { apply <- AxiomII. exists z. auto. }
        rewrite H2 in J2. apply -> AxiomII in J2; simpl in J2.
        rewrite J2 in J1. destruct H1 as [H1 J3]. apply f_x_N in J1; auto.
      - apply -> AxiomII in J1; simpl in J1. rewrite <- H3.
        apply <- AxiomII. exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
        { rewrite H2. apply <- AxiomII. auto. }
        apply -> AxiomII in J2; simpl in J2. destruct J2 as [y J2].
        destruct H1 as [H1 J3]. apply f_x_N in J2 as J4; auto.
        rewrite J1. rewrite J4. auto. }
    exists f\[0%nat\]. unfold maxN. split.
    + rewrite H5. apply <- AxiomII. auto.
    + intros x. intro J1. rewrite H5 in J1.
      apply -> AxiomII in J1; simpl in J1. rewrite <- J1. apply le_n.
  - intros A H2. destruct H2 as [f [H2 [H3 H4]]].
    assert (H5 : ∃ B, B = \{ λ (x : nat), (x <= n)%nat \}).
    { exists \{ λ (x : nat), (x <= n)%nat \}. auto. }
    destruct H5 as [B H5]. apply RestrictFun1_1_N with (x := B) in H2 as H6.
    destruct H2 as [H2 H7]. apply RestrictFun_N with (x := B) in H2 as H8.
    destruct H8 as [H8 [H9 H10]].
    assert (H11 : ∃n : nat, maxN ran[f|[B]] n).
    { apply H1. exists (f|[B]). split; [auto | split]; auto. rewrite H9.
      rewrite H5. rewrite H3. apply AxiomI. intro z; split; intro J1.
      - apply -> AxiomII in J1; simpl in J1. apply J1.
      - apply <- AxiomII. split; auto. apply -> AxiomII in J1; simpl in J1.
        apply <- AxiomII. apply le_S. auto. }
    assert (H12 : ran[f|[B]] ∪ [f\[S n\]] = A).
    { apply AxiomI. intro z; split; intro J1.
      - apply -> AxiomII in J1; simpl in J1. destruct J1 as [J1 | J1].
        + rewrite <- H4. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [x J1]. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [J1 J2]. apply <- AxiomII. exists x. auto.
        + rewrite <- H4. apply -> AxiomII in J1; simpl in J1.
          rewrite J1. apply fx_ran_N; auto. rewrite H3. apply <- AxiomII.
          apply le_n.
      - rewrite <- H4 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
        { apply <- AxiomII. exists z. auto. }
        rewrite H3 in J2. apply -> AxiomII in J2; simpl in J2.
        apply Nat.le_succ_r in J2 as J3. apply <- AxiomII.
        destruct J3 as [J3 | J3].
        + left. apply <- AxiomII. exists x. apply <- AxiomII. split; auto.
          apply <- AxiomII'. split.
          * rewrite H5. apply <- AxiomII. auto.
          * apply <- AxiomII. auto.
        + right. apply <- AxiomII. symmetry. apply f_x_N; auto. rewrite <- J3.
          auto. }
    destruct H11 as [n1 H11].
    destruct (le_gt_dec n1 (f\[S n\])) as [H13 | H13].
    + exists (f\[S n\]). unfold maxN. split.
      * rewrite <- H12. apply <- AxiomII. right. apply <- AxiomII; auto.
      * intros x J1. rewrite <- H12 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11 in J1. apply Nat.le_trans with (m := n1); auto.
        -- apply -> AxiomII in J1; simpl in J1. rewrite <- J1. apply le_n.
    + exists n1. unfold maxN. split.
      * rewrite <- H12. apply <- AxiomII. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> AxiomII in J1; simpl in J1. rewrite J1.
        Search (_<_ -> _<=_)%nat.
          apply Nat.lt_le_incl. auto.
Qed.

(* 非空有限的实数集有最大值 *)
Theorem finite_maxR : ∀ (A : sR), NotEmptyFinite A -> (∃ r : R, maxR A r).
Proof.
  intros A H1. unfold NotEmptyFinite in H1. destruct H1 as [n H1].
  generalize dependent H1. generalize dependent A. induction n as [|n H1].
  - intros A H1. destruct H1 as [f [H1 [H2 H3]]].
    assert (H4 : \{ λ x : nat, (x <= 0)%nat \} = [0%nat]).
    { apply AxiomI. intro z; split; intro I1.
      - apply <- AxiomII. apply -> AxiomII in I1. simpl in I1. symmetry.
        apply le_n_0_eq. auto.
      - apply -> AxiomII in I1; simpl in I1. rewrite I1. apply <- AxiomII.
        apply le_n. }
    rewrite H4 in H2. assert (H5 : A = [f[0%nat]]).
    { apply AxiomI. intro z; split; intro J1.
      - apply <- AxiomII. rewrite <- H3 in J1.
        apply -> AxiomII in J1; simpl in J1. destruct J1 as [x J1].
        assert (J2 : x ∈ dom[f]).
        { apply <- AxiomII. exists z. auto. }
        rewrite H2 in J2. apply -> AxiomII in J2; simpl in J2.
        rewrite J2 in J1. destruct H1 as [H1 J3]. apply f_x in J1; auto.
      - apply -> AxiomII in J1; simpl in J1. rewrite <- H3.
        apply <- AxiomII. exists 0%nat. assert (J2 : 0%nat ∈ dom[f]).
        { rewrite H2. apply <- AxiomII. auto. }
        apply -> AxiomII in J2; simpl in J2. destruct J2 as [y J2].
        destruct H1 as [H1 J3]. apply f_x in J2 as J4; auto.
        rewrite J1. rewrite J4. auto. }
    exists f[0%nat]. unfold max. split.
    + rewrite H5. apply <- AxiomII. auto.
    + intros x. intro J1. rewrite H5 in J1.
      apply -> AxiomII in J1; simpl in J1. rewrite <- J1. right. auto.
  - intros A H2. destruct H2 as [f [H2 [H3 H4]]].
    assert (H5 : ∃ B, B = \{ λ (x : nat), (x <= n)%nat \}).
    { exists \{ λ (x : nat), (x <= n)%nat \}. auto. }
    destruct H5 as [B H5]. apply RestrictFun1_1 with (x := B) in H2 as H6.
    destruct H2 as [H2 H7]. apply RestrictFun with (x := B) in H2 as H8.
    destruct H8 as [H8 [H9 H10]].
    assert (H11 : ∃n : R, maxR ran[f|[B]] n).
    { apply H1. exists (f|[B]). split; [auto | split]; auto. rewrite H9.
      rewrite H5. rewrite H3. apply AxiomI. intro z; split; intro J1.
      - apply -> AxiomII in J1; simpl in J1. apply J1.
      - apply <- AxiomII. split; auto. apply -> AxiomII in J1; simpl in J1.
        apply <- AxiomII. apply le_S. auto. }
    assert (H12 : ran[f|[B]] ∪ [f[S n]] = A).
    { apply AxiomI. intro z; split; intro J1.
      - apply -> AxiomII in J1; simpl in J1. destruct J1 as [J1 | J1].
        + rewrite <- H4. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [x J1]. apply -> AxiomII in J1; simpl in J1.
          destruct J1 as [J1 J2]. apply <- AxiomII. exists x. auto.
        + rewrite <- H4. apply -> AxiomII in J1; simpl in J1.
          rewrite J1. apply fx_ran; auto. rewrite H3. apply <- AxiomII.
          apply le_n.
      - rewrite <- H4 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [x J1]. assert (J2 : x ∈ dom[f]).
        { apply <- AxiomII. exists z. auto. }
        rewrite H3 in J2. apply -> AxiomII in J2; simpl in J2.
        apply Nat.le_succ_r in J2 as J3. apply <- AxiomII.
        destruct J3 as [J3 | J3].
        + left. apply <- AxiomII. exists x. apply <- AxiomII. split; auto.
          apply <- AxiomII'. split.
          * rewrite H5. apply <- AxiomII. auto.
          * apply <- AxiomII. auto.
        + right. apply <- AxiomII. symmetry. apply f_x; auto. rewrite <- J3.
          auto. }
    destruct H11 as [r1 H11].
    destruct (total_order_T r1 (f[S n])) as [[H13 | H13] | H13].
    + exists (f[S n]). unfold maxR. split.
      * rewrite <- H12. apply <- AxiomII. right. apply <- AxiomII; auto.
      * intros x J1. rewrite <- H12 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11 in J1. left. destruct J1 as [J1 | J1].
          ++ apply Rlt_trans with (r2 := r1); auto.
          ++ rewrite J1; auto.
        -- apply -> AxiomII in J1; simpl in J1. rewrite <- J1. right;auto.
    + exists r1. unfold maxR. split.
      * rewrite <- H12. apply <- AxiomII. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> AxiomII in J1; simpl in J1. rewrite J1.
          rewrite <- H13. right; auto.
    + exists r1. unfold maxR. split.
      * rewrite <- H12. apply <- AxiomII. left. apply H11.
      * intros x J1. rewrite <- H12 in J1. apply -> AxiomII in J1; simpl in J1.
        destruct J1 as [J1 | J1].
        -- apply H11. auto.
        -- apply -> AxiomII in J1; simpl in J1. rewrite J1.
          left; auto.
Qed.

End A0.

Export A0.
