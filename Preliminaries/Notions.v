(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import Compare_dec.

(* 余谓词 *)
Notation "p ⁻" := (λ x, ¬ p x) (format "p ⁻", at level 9).

Definition 安定 {A} (f : ℕ → A?) :=
  ∀ n x, f n = Some x → ∀ m, m ≥ n → f m = Some x.

Definition 平稳 {A} (f : ℕ → A?) :=
  ∀ n m y z, f n = Some y → f m = Some z → y = z.

Lemma 安定平稳 {A} (f : ℕ → A?) : 安定 f → 平稳 f.
Proof.
  intros sat n m y z fn fm.
  destruct (Compare_dec.le_ge_dec n m) as [le|ge].
  - eapply sat in le; eauto. congruence.
  - eapply sat in ge; eauto. congruence.
Qed.

Definition 枚举器 {A} (p : A → Prop) (f : ℕ → A?) :=
  ∀ x, p x ↔ ∃ n, f n = Some x.
Definition 可枚举 {A} (p : A → Prop) :=
  ∃ f : ℕ → A?, 枚举器 p f.

Definition 参数化枚举器 {A B} (p : A → B → Prop) (f : A → ℕ → B?) :=
  ∀ x y, p x y ↔ ∃ n, f x n = Some y.
Definition 参数化可枚举 {A B} (p : A → B → Prop) :=
  ∃ f, 参数化枚举器 p f.

Definition 判定器 {A} (p : A → Prop) (f : A → bool) :=
  ∀ x, p x ↔ f x = true.
Definition 可判定 {A} (p : A → Prop) :=
  ∃ f : A → bool, 判定器 p f.

Definition 半判定器 {A} (p : A → Prop) (f : A → ℕ → bool) :=
  ∀ x, p x ↔ ∃ n, f x n = true.
Definition 半可判定 {A} (p : A → Prop) :=
  ∃ f : A → ℕ → bool, 半判定器 p f.

Definition 余半判定器 {A} (p : A → Prop) (f : A → ℕ → bool) :=
  ∀ x, p x ↔ ∃ n, f x n = false.
Definition 余半可判定 {A} (p : A → Prop) :=
  ∃ f : A → ℕ → bool, 半判定器 p f.

Definition 逻辑可判定 {A} (p : A → Prop) := ∀ x, {p x} + {¬ p x}.

Fact 布尔函数逻辑可判定 (f : ℕ → bool) n : {f n = true} + {f n ≠ true}.
Proof. destruct (f n); firstorder. Qed.

Class 命题可判定 (P : Prop) : Set := 判定 : {P} + {¬ P}.
Arguments 判定 P {命题可判定}.
