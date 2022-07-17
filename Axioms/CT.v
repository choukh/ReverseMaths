(** Coq coding by choukh, July 2022 **)

Require Import Nat Notions Equivalence NatEmbed PartialFunc.
Import PartialFunc.PairView.

(* 邱奇论题: 任意函数在任意给定的计算模型中可定义 *)
Definition CT (ϕ : ℕ → ℕ → ℕ → ℕ?) := 
  (∀ c x, 安定 (ϕ c x)) ∧
  ∀ f, ∃ c, ∀ x, ∃ n, ϕ c x n = Some (f x).

(* Bauer的可枚举性公理原版: 强存在可枚举谓词的枚举 *)
(* 参考: Andrej Bauer. First steps in synthetic computability theory. Electronic Notes in Theoretical Computer Science, 155:5–31, 2006. *)
Definition EAₒ := Σ ε : ℕ → ℕ → Prop, ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, ε c ≡{_} p.

(* EAₒ强化版: 强存在枚举函数的枚举 *)
Definition EA := Σ ε : ℕ → ℕ → ℕ?, ∀ f : ℕ → ℕ?, ∃ c, ε c ≡{_} f.

(* EA改版: 强存在谓词枚举器的枚举 *)
Definition EA' := Σ ε : ℕ → ℕ → ℕ?, ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, 枚举器 p (ε c).

Theorem EA_iff_EA' : EA ⇔ EA'.
Proof.
  split.
  - intros [ε H]. exists ε. intros p. split.
    + intros [f He]. specialize H with f as [c H].
      exists c. intros x. rewrite (He x). firstorder.
    + intros [c He]. now exists (ε c).
  - intros [ε H]. exists ε. intros f.
    set (λ x, ∃ n, f n = Some x) as p.
    assert (He: 可枚举 p) by firstorder.
    apply H in He as [c He]. firstorder.
Qed.

Fact EA'_to_EAₒ : EA' → EAₒ.
Proof.
  intros [ε H].
  set (λ c x, ∃ n, ε c n = Some x) as ε'.
  exists ε'. intros p. rewrite H. firstorder.
Qed.

Corollary EA_to_EAₒ : EA → EAₒ.
Proof. intros ea. now apply EA'_to_EAₒ, EA_iff_EA'. Qed.

Lemma CT_to_EA : ∀ ϕ, CT ϕ → EA.
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

Corollary CT_to_EAₒ : ∀ ϕ, CT ϕ → EAₒ.
Proof. intros ϕ ct. now apply EA_to_EAₒ, (CT_to_EA ϕ). Qed.

Section 给定偏函数模型.
Context {M : 偏函数模型}.

(* Richman的偏函数可枚举性公理 *)
(* 参考: Fred Richman. Church’s thesis without tears. The Journal of symbolic logic, 48(3):797–803, 1983. *)
Definition EPF := Σ ε : ℕ → ℕ ⇀ ℕ, ∀ f : ℕ ⇀ ℕ, ∃ c, ε c ≡{_} f.

Definition EPFᴮ := Σ ε : ℕ → ℕ ⇀ bool, ∀ f : ℕ ⇀ bool, ∃ n, ε n ≡{_} f.

Let toB (f : ℕ ⇀ ℕ) : ℕ ⇀ bool := λ x, f x >>= (λ y, if y =? 1 then 有 true else 有 false).
Let toN (f : ℕ ⇀ bool) : ℕ ⇀ ℕ := λ x, f x >>= (λ y, if y then 有 1 else 有 0).

Fact EPF_to_EPFᴮ : EPF → EPFᴮ.
Proof.
  intros [ε H]. exists (λ n, toB (ε n)). intros f.
  destruct (H (toN f)) as [c Hc]. exists c. intros x y.
  simpl in Hc. unfold 偏类型等词 in Hc.
  unfold toB. rewrite 绑定规则. setoid_rewrite Hc. split.
  - intros [n [H1 H2]]; destruct (PeanoNat.Nat.eqb_spec n 1); subst;
    apply 有值解包 in H2; subst; apply 绑定规则 in H1 as [[] [H1 H2]]; auto;
    apply 有值解包 in H2; congruence.
  - intros H1. exists (if y then 1 else 0). split.
    + apply 绑定规则. exists y. split. easy.
      destruct y; apply 有值解包; easy.
    + destruct y; apply 有值解包; easy.
Qed.

Lemma EPF_to_CT : EPF → Σ ϕ, CT ϕ.
Proof.
  intros [ε epf].
  set (λ c x n, ε c x @ n) as ϕ. exists ϕ. split.
  - intros c x n y ϕcxn m ge. eapply 求值安定; eauto.
  - intros f. destruct (epf (λ n, 有 (f n))) as [c H].
    exists c. intros x. specialize (H x (f x)).
    apply 求值规则, H, 有规则.
Qed.

Lemma EPF_to_EA : EPF → EA.
Proof.
  intros [ε epf].
  set (λ c, λ' ⟨x, n⟩, ε c x @ n) as ε'. exists ε'. intros f.
  set (λ n, if f n is Some x then 有 x else 无) as f'.
  destruct (epf f') as [c H]. exists c. intros y. split.
  - intros [n H1]. unfold ε' in H1. destruct ⎞n⎛ as (x, m). exists x.
    assert (H2: f' x ?= y). apply H, 求值规则. now exists m.
    apply 求值规则 in H2 as [k H2]. unfold f' in H2.
    destruct (f x) as [y'|].
    + apply 有值求值 in H2. congruence.
    + exfalso. eapply 无规则. apply 求值规则. exists k. apply H2.
  - intros [x H1]. unfold ε'.
    assert (H2: f' x ?= y). unfold f'. rewrite H1. apply 有规则.
    apply (H x y) in H2. apply 求值规则 in H2 as [m H2].
    exists ⟨x, m⟩. rewrite GF. apply H2.
Qed.

Lemma EA_to_EPF : EA → EPF.
Proof.
  intros [ε ea].
  set (λ c, G (λ x, if ε c x is Some x then Some ⎞x⎛ else None)) as ε'.
  exists ε'. intros f.
  set (λ n, if F f n is Some (x, y) then Some ⟨x, y⟩ else None) as f'.
  destruct (ea f') as [c H]. exists c. intros x y. split.
  - intros.
Admitted.

Theorem EPF_iff_EA : EPF ⇔ EA.
Proof. split. apply EPF_to_EA. apply EA_to_EPF. Qed.

Theorem CT_iff_EPF : (Σ ϕ, CT ϕ) ⇔ EPF.
Proof.
  split.
  - intros [ϕ ct]. eapply EA_to_EPF, CT_to_EA, ct.
  - apply EPF_to_CT.
Qed.

End 给定偏函数模型.

Require Import PartialFuncImpl.

Theorem CT_iff_EA : (Σ ϕ, CT ϕ) ⇔ EA.
Proof.
  split.
  - intros [ϕ ct]. eapply CT_to_EA, ct.
  - intros ea. eapply EPF_to_CT, EA_to_EPF, ea.
Qed.
