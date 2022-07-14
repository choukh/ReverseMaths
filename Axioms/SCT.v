(** Coq coding by choukh, July 2022 **)

Require Import Notions Equivalence NatEmbed PartialFunc CT.
Import PartialFunc.模型.

(* 克莱尼的SMN定理 https://en.wikipedia.org/wiki/Smn_theorem *)
Definition SMN (ϕ : ℕ → ℕ → ℕ → ℕ?) := ∃ S : ℕ → ℕ → ℕ, ∀ c x y,
  ϕ c ⟨x, y⟩ ≡{_} ϕ (S c x) y.

(* 综合式 (Synthetic) 邱奇论题 *)
Definition SCT := Σ ϕ : ℕ → ℕ → ℕ → ℕ?,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → ℕ, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

Definition SCTᴮ := Σ ϕ : ℕ → ℕ → ℕ → bool?,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → bool, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

(* 综合式EPF *)
Definition SEPF `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ ℕ,
  ∀ fᵢ : ℕ → ℕ ⇀ ℕ, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Definition SEPFᴮ `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ bool,
  ∀ fᵢ : ℕ → ℕ ⇀ bool, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Theorem CT_SMN_to_SCT : (Σ ϕ, CT ϕ ∧ SMN ϕ) → SCT.
Proof.
  intros [ϕ H]. exists ϕ.
  destruct H as [[sat com] [S SMN]].
  split; auto. intros f.
  destruct (com (λ' ⟨x, y⟩, f x y)) as [c Hc].
  exists (S c). intros. eapply SMN.
  destruct (Hc ⟨i, x⟩). rewrite GF in H. eauto.
Qed.

Theorem SCT_to_CT : SCT → Σ ϕ, CT ϕ.
Proof.
  intros [ϕ [sat com]]. exists ϕ. split.
  - apply sat.
  - intros f. specialize (com (λ _, f)) as [γ H].
    exists (γ 0). intros. eauto.
Qed.
