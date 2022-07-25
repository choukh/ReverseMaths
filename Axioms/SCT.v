(** Coq coding by choukh, July 2022 **)

Require Import Notions Equivalence NatEmbed PartialFunc CT.
Require Import EnumerabilityFacts.

(* 克莱尼的SMN定理 https://en.wikipedia.org/wiki/Smn_theorem *)
Definition SMN (ϕ : ℕ → ℕ → ℕ → ℕ?) := ∃ S : ℕ → ℕ → ℕ,
  ∀ c x y, ϕ (S c x) y ≡{_} ϕ c ⟨x, y⟩.

Definition SMNᵂ (W : ℕ → ℕ → Prop) := ∃ S : ℕ → ℕ → ℕ,
  ∀ c x y, W (S c x) y ↔ W c ⟨x, y⟩.

(* 综合式 (Synthetic) 邱奇论题 *)
Definition SCT := Σ ϕ : ℕ → ℕ → ℕ → ℕ?,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → ℕ, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

Definition SCTᴮ := Σ ϕ : ℕ → ℕ → ℕ → bool?,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → bool, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

(* 综合式EA *)
Definition SEA := Σ ε : ℕ → ℕ → ℕ?,
  ∀ fᵢ : ℕ → ℕ → ℕ?, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Definition SEAᵖₑ (ε : ℕ → ℕ → ℕ?) :=
  ∀ p : ℕ → ℕ → Prop, 参数化可枚举 p → ∃ cᵢ, 参数化枚举器 p (λ i, ε (cᵢ i)).

Definition SEAᵖₑ_uncurry (ε : ℕ → ℕ → ℕ?) :=
  ∀ p : ℕ → ℕ → Prop, 可枚举 (uncurry p) → ∃ cᵢ, 参数化枚举器 p (λ i, ε (cᵢ i)).

Definition SEAᵖ := Σ ε, SEAᵖₑ ε.

(* 综合式EPF *)
Definition SEPF `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ ℕ,
  ∀ fᵢ : ℕ → ℕ ⇀ ℕ, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Definition SEPFᴮ `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ bool,
  ∀ fᵢ : ℕ → ℕ ⇀ bool, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Theorem CT_SMN_to_SCT : (Σ ϕ, CTᵩ ϕ ∧ SMN ϕ) → SCT.
Proof.
  intros [ϕ H]. exists ϕ.
  destruct H as [[sat def] [S SMN]].
  split; auto. intros f.
  destruct (def (λ' ⟨x, y⟩, f x y)) as [c Hc].
  exists (S c). intros. eapply SMN.
  destruct (Hc ⟨i, x⟩). rewrite GF in H. eauto.
Qed.

Theorem SCT_to_CT : SCT → CT.
Proof.
  intros [ϕ [sat def]]. exists ϕ. split.
  - apply sat.
  - intros f. specialize (def (λ _, f)) as [γ H].
    exists (γ 0). intros. eauto.
Qed.

Lemma SEAᵖₑ_iff_SEAᵖₑ_uncurry (ε : ℕ → ℕ → ℕ?) : SEAᵖₑ ε ↔ SEAᵖₑ_uncurry ε.
Proof.
  split; intros H p Hp.
  - eapply 参数化可枚举反柯里化 in Hp; eauto.
  - apply H. eapply 参数化可枚举反柯里化; eauto.
Qed.

Lemma EAᵖ_SMNᵂ_to_SEAᵖₑ (ea : EAᵖ) : let ε := projT1 ea in SMNᵂ (W ε) → SEAᵖₑ ε.
Proof.
  destruct ea as [ε ea]. simpl.
  intros smn. apply SEAᵖₑ_iff_SEAᵖₑ_uncurry.
  intros p Hp. apply 反柯里化可枚举嵌入 in Hp.
  destruct ((proj1 (ea _)) Hp) as [c Hc].
  destruct smn as [S HS]. exists (λ x, S c x).
  intros x y. unfold 枚举器 in Hc. unfold W in HS.
  now rewrite HS, <- Hc, GF.
Qed.
