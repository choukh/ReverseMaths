(** Coq coding by choukh, July 2022 **)

Require Import ConstructiveEpsilon Setoid.
Require Import Notions Equivalence NatLargeElim.

Reserved Notation "x ?= a" (at level 50).
Reserved Notation "x @ n" (at level 50).
Reserved Notation "x >>= f" (at level 50).
Reserved Notation "A ⇀ B" (at level 10).

Module 模型.

Class 偏函数模型 := {
  偏 : Type → Type where "A ⇀ B" := (A → 偏 B);

  解包关系 {A} : 偏 A → A → Prop where "x ?= a" := (解包关系 x a);
  解包关系单射 {A} : ∀ (x : 偏 A) a b, x ?= a → x ?= b → a = b;

  求值 {A} : 偏 A → ℕ → A? where "x @ n" := (求值 x n);
  求值安定 {A} : ∀ x, 安定 (@求值 A x);
  求值规则 {A} : ∀ (x : 偏 A) a, x ?= a ↔ ∃ n, x @ n = Some a;

  偏μ : (ℕ ⇀ bool) ⇀ ℕ;
  偏μ规则 : ∀ (f : ℕ ⇀ bool) n, 偏μ f ?= n ↔ (f n ?= true ∧ ∀ m, m < n → f m ?= false);

  (* return *)
  有 {A} : A ⇀ A;
  有规则 {A} : ∀ (a : A), 有 a ?= a;

  (* undefined *)
  无 {A} : 偏 A;
  无规则 {A} : ∀ (a : A), ¬ 无 ?= a;

  (* bind *)
  绑定 {A B} : 偏 A → (A ⇀ B) ⇀ B where "x >>= f" := (绑定 x f);
  绑定规则 {A B} : ∀ (x : 偏 A) (f : A ⇀ B) y,
    x >>= f ?= y ↔ ∃ a, x ?= a ∧ f a ?= y;
}.

Notation "x ?= a" := (解包关系 x a) (at level 50).
Notation "x @ n" := (求值 x n) (at level 50).
Notation "x >>= f" := (绑定 x f) (at level 50).
Notation "A ⇀ B" := (A → 偏 B) (at level 10).

Section 某偏函数模型内.
Context {M : 偏函数模型}.

Section 给定类型A.
Context {A : Type}.

Definition 偏类型等词 (x y : 偏 A) := ∀ a, x ?= a ↔ y ?= a.

Instance 偏类型等词为等价关系 : Equivalence 偏类型等词.
Proof. firstorder. Qed.

Global Instance 偏类型外延 : 等价关系 (偏 A) := {| R := 偏类型等词 |}.

Lemma 有值解包_l (a b : A) : 有 a ?= b → a = b.
Proof. intros. eapply 解包关系单射. eapply 有规则. easy. Qed.

Lemma 有值解包_r (a b : A) : a = b → 有 a ?= b.
Proof. intros ->. apply 有规则. Qed.

Lemma 有值解包 (a b : A) : 有 a ?= b ↔ a = b.
Proof. split. apply 有值解包_l. apply 有值解包_r. Qed.

Definition 有值 (x : 偏 A) := ∃ a, x ?= a.

Lemma 有值则可求 (x : 偏 A) : 有值 x → Σ a, x ?= a.
Proof.
  intros Hx.
  assert (H: ∃ n, x @ n ≠ None). {
    destruct Hx as [a [n xn]%求值规则]. exists n. congruence.
  }
  apply constructive_indefinite_ground_description_nat in H as [n H].
  - destruct 求值 as [a|] eqn: E.
    + exists a. apply 求值规则. firstorder.
    + congruence.
  - intros. destruct 求值; firstorder congruence.
Qed.

Definition 解包 {x : 偏 A} (H : 有值 x) : A := projT1 (有值则可求 x H).
Definition 解包规则 (x : 偏 A) (H : 有值 x) : x ?= (解包 H) := projT2 (有值则可求 x H).

End 给定类型A.

Definition μ : (ℕ → bool) ⇀ ℕ := λ f, 偏μ (λ n, 有 (f n)).

Lemma μ规则 (f : ℕ → bool) n : μ f ?= n ↔ (f n = true ∧ ∀ m, m < n → f m = false).
Proof. unfold μ. rewrite 偏μ规则. now repeat setoid_rewrite 有值解包. Qed.

Lemma μ有值 (f : ℕ → bool) n : f n = true → 有值 (μ f).
Proof.
  intros.
  assert (ex : ∃ n, f n = true) by eauto.
  assert (dec : ∀ n, {f n = true} + {¬ f n = true}). {
    intros m. destruct (f m); firstorder.
  }
  destruct (自然数大消除 _ dec ex) as [m fm] eqn: E.
  apply (f_equal (@projT1 _ _)) in E. simpl in E.
  exists m. apply μ规则. split. easy.
  intros k km. subst. apply 自然数大消除_最小性 in km.
  destruct (f k); firstorder.
Qed.

Definition 无' {A} (a : A) := μ (λ _, false) >>= (λ _, 有 a).

Lemma 无规则' {A} (a b : A) : ¬ 无' a ?= b.
Proof.
  intros H. apply 绑定规则 in H as [n [H _]].
  apply μ规则 in H as []. discriminate.
Qed.

End 某偏函数模型内.
End 模型.

Module 实装.

Record 偏 A := {
  求值 : ℕ → A?;
  求值安定 : 安定 求值
}.
Arguments 求值 {_} _ _.
Notation "x @ n" := (求值 x n) (at level 50).

Section 给定类型A.
Context {A : Type}.

Definition 解包关系 (x : 偏 A) (a : A) := ∃ n, x @ n = Some a.
Notation "x ?= a" := (解包关系 x a) (at level 50).

Lemma 解包关系单射 : ∀ (x : 偏 A) a b, x ?= a → x ?= b → a = b.
Proof.
  intros x a b [n Hn] [m Hm].
  eapply 安定平稳. apply 求值安定. eauto. eauto.
Qed.

End 给定类型A.
End 实装.
