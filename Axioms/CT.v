(** Coq coding by choukh, July 2022 **)

Require Import Notions Equivalence NatEmbed.

Notation 解释器 := (ℕ → ℕ → ℕ → ℕ?).

(* 邱奇论题: 任意函数在任意给定的计算模型中可定义 *)
Definition CT (ϕ : 解释器) := 
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ f, ∃ c, ∀ x, ∃ n, ϕ c x n = Some (f x).

Lemma ϕ平稳 {ϕ c x} : CT ϕ → 平稳 (ϕ c x).
Proof. intros ct. apply 安定平稳, ct. Qed.

(* 克莱尼的SMN定理 https://en.wikipedia.org/wiki/Smn_theorem *)
Definition SMN (ϕ : 解释器) := ∃ S : ℕ → ℕ → ℕ, ∀ c x y z,
  (∃ n, ϕ c ⟨x, y⟩ n = Some z) ↔ (∃ n, ϕ (S c x) y n = Some z).

(* 综合式 (Synthetic) 邱奇论题 *)
Definition SCT := Σ (ϕ : 解释器),
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → ℕ, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

(* Bauer的枚举性公理强化版: 强存在枚举函数的枚举 *)
Definition EA := Σ ε : ℕ → (ℕ → ℕ?), ∀ f : ℕ → ℕ?, ∃ c, ε c ≡{_} f.

(* Bauer的枚举性公理原版: 强存在可枚举集的枚举 *)
(* 参考: Andrej Bauer. First steps in synthetic computability theory. Electronic Notes in Theoretical Computer Science, 155:5–31, 2006. *)
Definition EAₒ := Σ ε : ℕ → (ℕ → Prop), ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, ε c ≡{_} p.

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

Theorem EA_to_EAₒ : EA → EAₒ.
Proof.
  intros ea. destruct ea as [ε Hε].
  set (λ c x, ∃ n, ε c n = Some x) as ε'.
  exists ε'. intros p. unfold 可枚举, 枚举器.
  transitivity (∃ c, ∀ x, p x ↔ ∃ n, ε c n = Some x).
  - split.
    + intros [f Hf].
      destruct (Hε f) as [c Hc].
      exists c. intros x. rewrite Hf. cbn in Hc. now rewrite Hc.
    + intros [c Hc]. now exists (ε c).
 - firstorder.
Qed.

Theorem CT_to_EA : ∀ ϕ, CT ϕ → EA.
Proof.
  intros ϕ [sat com].
  set (λ c, λ' ⟨x, n⟩, match ϕ c x n with
    | Some (S m) => Some m
    | _ => None
  end) as ϕ'.
  exists ϕ'. intros f.
  set (λ n, match f n with
    | Some x => S x
    | None => 0
  end) as f'.
  destruct (com f') as [c com'].
  exists c. intros y. unfold ϕ'. split.
  - intros [m T'cm].
    destruct ⎞m⎛ as (x, n).
    destruct (ϕ c x n) as [[|]|] eqn: ϕcxn; inv T'cm.
    exists x. destruct (com' x) as [n' ϕcxn'].
    assert (eq: S y = f' x). eapply ϕ平稳; eauto. split; auto.
    unfold f' in eq. destruct (f x); congruence.
  - intros [x fx].
    destruct (com' x) as [n ϕcxn]. exists ⟨x, n⟩.
    unfold f' in ϕcxn. now rewrite GF, ϕcxn, fx.
Qed.
