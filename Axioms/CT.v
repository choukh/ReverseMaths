(** Coq coding by choukh, July 2022 **)

Require Import Notions Equivalence NatEmbed PartialFunc.
Import PartialFunc.模型.

Notation 解释器 := (ℕ → ℕ → ℕ → ℕ?).

(* 邱奇论题: 任意函数在任意给定的计算模型中可定义 *)
Definition CT (ϕ : 解释器) := 
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ f, ∃ c, ∀ x, ∃ n, ϕ c x n = Some (f x).

(* 克莱尼的SMN定理 https://en.wikipedia.org/wiki/Smn_theorem *)
Definition SMN (ϕ : 解释器) := ∃ S : ℕ → ℕ → ℕ, ∀ c x y,
  ϕ c ⟨x, y⟩ ≡{_} ϕ (S c x) y.

(* 综合式 (Synthetic) 邱奇论题 *)
Definition SCT := Σ ϕ : 解释器,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → ℕ, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

Definition SCTᴮ := Σ ϕ : ℕ → ℕ → ℕ → bool?,
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ fᵢ : ℕ → ℕ → bool, ∃ cᵢ, ∀ i x, ∃ n, ϕ (cᵢ i) x n = Some (fᵢ i x).

(* Richman的偏函数可枚举性公理 *)
(* 参考: Fred Richman. Church’s thesis without tears. The Journal of symbolic logic, 48(3):797–803, 1983. *)
Definition EPF `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ ℕ,
  ∀ fᵢ : ℕ → ℕ ⇀ ℕ, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

Definition EPFᴮ `{偏函数模型} := Σ ε : ℕ → ℕ ⇀ bool,
  ∀ fᵢ : ℕ → ℕ ⇀ bool, ∃ cᵢ, ∀ i, ε (cᵢ i) ≡{_} fᵢ i.

(* Bauer的可枚举性公理原版: 强存在可枚举谓词的枚举 *)
(* 参考: Andrej Bauer. First steps in synthetic computability theory. Electronic Notes in Theoretical Computer Science, 155:5–31, 2006. *)
Definition EAᵒ := Σ ε : ℕ → (ℕ → Prop), ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, ε c ≡{_} p.

(* Bauer的可枚举性公理强化版: 强存在谓词枚举器的枚举 *)
Definition EAᵉ := Σ ε : ℕ → (ℕ → ℕ?), ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, 枚举器 p (ε c).

(* Bauer的可枚举性公理强化版: 强存在枚举函数的枚举 *)
Definition EAᶠ := Σ ε : ℕ → (ℕ → ℕ?), ∀ f : ℕ → ℕ?, ∃ c, ε c ≡{_} f.

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

Theorem CT_to_EAᶠ : ∀ ϕ, CT ϕ → EAᶠ.
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
    assert (eq: S y = f' x). eapply 安定平稳; eauto.
    unfold f' in eq. destruct (f x); congruence.
  - intros [x fx].
    destruct (com' x) as [n ϕcxn]. exists ⟨x, n⟩.
    unfold f' in ϕcxn. now rewrite GF, ϕcxn, fx.
Qed.

Theorem EAᵉ_to_EAᵒ : EAᵉ → EAᵒ.
Proof.
  intros [ε H].
  set (λ c x, ∃ n, ε c n = Some x) as ε'.
  exists ε'. intros p. rewrite H. firstorder.
Qed.

Theorem EAᵉ_iff_EAᶠ : (EAᵉ → EAᶠ) * (EAᶠ → EAᵉ).
Proof.
  split.
  - intros [ε H]. exists ε. intros f.
    set (λ x, ∃ n, f n = Some x) as p.
    assert (He: 可枚举 p) by firstorder.
    apply H in He as [c He]. firstorder.
  - intros [ε H]. exists ε. intros p. split.
    + intros [f He]. specialize H with f as [c H].
      exists c. intros x. rewrite (He x). firstorder.
    + intros [c He]. now exists (ε c).
Qed.

Corollary EAᶠ_to_EAᵒ : EAᶠ → EAᵒ.
Proof. intros ea. apply EAᵉ_to_EAᵒ. now apply EAᵉ_iff_EAᶠ. Qed.
