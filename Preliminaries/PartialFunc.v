(** Coq coding by choukh, July 2022 **)

Require Import ConstructiveEpsilon Setoid.
Require Import Notions Equivalence NatLargeElim.
Require Nat NatEmbed.

Reserved Notation "x ?= a" (at level 70).
Reserved Notation "x @ n" (at level 50).
Reserved Notation "x >>= f" (at level 50).
Reserved Notation "A ⇀ B" (at level 10).

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

Notation "x ?= a" := (解包关系 x a) (at level 70).
Notation "x @ n" := (求值 x n) (at level 50).
Notation "x >>= f" := (绑定 x f) (at level 50).
Notation "A ⇀ B" := (A → 偏 B) (at level 10).

Section 给定偏函数模型.
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

Lemma 有值求值 (a b : A) n : 有 a @ n = Some b → a = b.
Proof. intros. apply 有值解包, 求值规则. now exists n. Qed.

Definition 有值 (x : 偏 A) := ∃ a, x ?= a.

Lemma 有值则可求 (x : 偏 A) : 有值 x → Σ a, x ?= a.
Proof.
  intros Hx.
  assert (H: ∃ n, x @ n ≠ None). {
    destruct Hx as [a [n xn]%求值规则]. exists n. congruence.
  }
  apply constructive_indefinite_ground_description_nat in H as [n H].
  - destruct 求值 as [a|] eqn:E.
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
  intros. pose proof (自然数布尔大消除 f n H) as [m min].
  exists m. now apply μ规则.
Qed.

Definition 无' {A} (a : A) := μ (λ _, false) >>= (λ _, 有 a).

Lemma 无规则' {A} (a b : A) : ¬ 无' a ?= b.
Proof.
  intros H. apply 绑定规则 in H as [n [H _]].
  apply μ规则 in H as []. discriminate.
Qed.

End 给定偏函数模型.

Module PairView.
Import Nat NatEmbed.
Section 给定偏函数模型.
Context {M : 偏函数模型}.

(* 将偏函数的点枚举为可选配对 *)
Definition F (f : ℕ ⇀ ℕ) : ℕ → (ℕ * ℕ)? :=
  λ' ⟨x, n⟩, if f x @ n is Some y then Some (x, y) else None.

(* 从可选配对的枚举恢复偏函数 *)
Definition G (g : ℕ → (ℕ * ℕ)?) : ℕ ⇀ ℕ := λ x,
  μ (λ n, if g n is Some (x', _) then x =? x' else false) >>=
  (λ n, if g n is Some (_, y) then 有 y else 无).

Definition 函数性配对 (g : ℕ → (ℕ * ℕ)?) := ∀ n m x y z,
  g n = Some (x, y) → g m = Some (x, z) → y = z.

Lemma F规则 f x y : (f x ?= y) ↔ (∃ n, F f n = Some (x, y)).
Proof.
  unfold F. split.
  - intros. apply 求值规则 in H as [n H].
    exists ⟨x, n⟩. now rewrite GF, H.
  - intros [n H]. destruct ⎞n⎛ as [x' m].
    destruct 求值 eqn:E; inv H. apply 求值规则. eauto.
Qed.

Lemma G规则 g x y : (G g x ?= y) → (∃ n, g n = Some (x, y)).
Proof.
  unfold G. intros. apply 绑定规则 in H as [n [H1 H2]].
  apply μ规则 in H1 as [H1 _].
  destruct (g n) as [[x' y']|] eqn:E.
  - apply 有值解包 in H2. subst.
    apply EqNat.beq_nat_true in H1 as ->. eauto.
  - now apply 无规则 in H2.
Qed.

Local Lemma 小消除 (g : ℕ → (ℕ * ℕ)?) x y n : g n = Some (x, y) → 
  let f := (λ n, if g n is Some (x', _) then x =? x' else false) in
  ∃ m, f m = true ∧ ∀ k : ℕ, k < m → f k = false.
Proof.
  intros gn f. assert (fn: f n = true). {
    unfold f. rewrite gn. now erewrite EqNat.beq_nat_refl.
  }
  pose proof (自然数布尔大消除 f n fn) as [m [H1 H2]].
  exists m. split; auto.
Qed.

Lemma G规则_反向 g x y n : 函数性配对 g → g n = Some (x, y) → G g x ?= y.
Proof.
  intros Fun gn. apply 绑定规则.
  pose proof (小消除 g x y n gn) as [m [H1 H2]].
  destruct (g m) eqn:E. 2:discriminate. exists m. split.
  - apply μ规则. split; auto. rewrite E. apply H1.
  - rewrite E. destruct p as [x' y'].
    apply EqNat.beq_nat_true in H1 as <-.
    apply 有值解包. eapply Fun; eauto.
Qed.

Fact G有值 g x : 有值 (G g x) ↔ ∃ n y, g n = Some (x, y).
Proof.
  split.
  - intros [y H]. apply G规则 in H as [n H]. now exists n, y.
  - intros [n [y gn]].
    pose proof (小消除 g x y n gn) as [m [H1 H2]].
    destruct (g m) eqn:E. 2:discriminate.
    destruct p as [x' y']. exists y'. apply 绑定规则. exists m. split.
    + apply μ规则. split; auto. rewrite E. apply H1.
    + rewrite E. now apply 有值解包.
Qed.

End 给定偏函数模型.
End PairView.
