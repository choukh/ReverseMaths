(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import Compare_dec.

Definition 安定 {T} (f : ℕ → T?) :=
  ∀ n x, f n = Some x → ∀ m, m ≥ n → f m = Some x.

Definition 平稳 {T} (f : ℕ → T?) :=
  ∀ n m y z, f n = Some y → f m = Some z → y = z.

Lemma 安定平稳 {T} (f : ℕ → T?) : 安定 f → 平稳 f.
Proof.
  intros sat n m y z fn fm.
  destruct (Compare_dec.le_ge_dec n m) as [le|ge].
  - eapply sat in le; eauto. congruence.
  - eapply sat in ge; eauto. congruence.
Qed.

Definition 枚举器 {T} (p : T → Prop) (f : ℕ → T?) :=
  ∀ x, p x ↔ ∃ n, f n = Some x.
Definition 可枚举 {T} (p : T → Prop) :=
  ∃ f : ℕ → T?, 枚举器 p f.

Definition 判定器 {T} (p : T → Prop) (f : T → bool) :=
  ∀ x, p x ↔ f x = true.
Definition 可判定 {T} (p : T → Prop) :=
  ∃ f : T → bool, 判定器 p f.

Definition 半判定器 {T} (p : T → Prop) (f : T → ℕ → bool) :=
  ∀ x, p x ↔ ∃ n, f x n = true.
Definition 半可判定 {T} (p : T → Prop) :=
  ∃ f : T → ℕ → bool, 半判定器 p f.

Definition 余半判定器 {T} (p : T → Prop) (f : T → ℕ → bool) :=
  ∀ x, p x ↔ ∃ n, f x n = false.
Definition 余半可判定 {T} (p : T → Prop) :=
  ∃ f : T → ℕ → bool, 半判定器 p f.

Definition 逻辑可判定 {T} (p : T → Prop) := ∀ x, p x ∨ ¬ p x.
Definition 强逻辑可判定 {T} (p : T → Prop) := ∀ x, {p x} + {¬ p x}.

Fact 布尔函数可判定性 (f : ℕ → bool) n : {f n = true} + {f n ≠ true}.
Proof. destruct (f n); firstorder. Qed.
