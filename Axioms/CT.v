(** Coq coding by choukh, July 2022 **)

Require Import Nat Notions Equivalence NatEmbed PartialFunc.
Import PartialFunc.PairView.

Definition CTᵩ (ϕ : ℕ → ℕ → ℕ → ℕ?) :=
  (* a *) (∀ c x, 安定 (ϕ c x)) ∧
  (* b *) ∀ f, ∃ c, ∀ x, ∃ n, ϕ c x n = Some (f x).

(* 邱奇论题: 强存在计算模型使得任意函数都可定义 *)
Definition CT := Σ ϕ, CTᵩ ϕ.

(* Bauer的可枚举性公理原版: 强存在可枚举谓词的枚举 *)
(* 参考: Andrej Bauer. First steps in synthetic computability theory. Electronic Notes in Theoretical Computer Science, 155:5–31, 2006. *)
Definition EAₒ := Σ ε : ℕ → ℕ → Prop, ∀ p : ℕ → Prop, 可枚举 p ↔ ∃ c, ε c ≡{_} p.

(* EAₒ强化版: 强存在可选值序列的枚举 *)
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

Lemma CT_to_EA : CT → EA.
Proof.
  intros [ϕ [sat def]].
  set (λ c, λ' ⟨x, n⟩, match ϕ c x n with
    | Some (S m) => Some m
    | _ => None
  end) as ε.
  exists ε. intros f.
  set (λ n, match f n with
    | Some m => S m
    | None => 0
  end) as f'.
  destruct (def f') as [c def'].
  exists c. intros y. unfold ε. split.
  - intros [m H].
    destruct ⎞m⎛ as (x, n).
    destruct (ϕ c x n) as [[|]|] eqn: ϕcxn; inv H.
    exists x. destruct (def' x) as [n' ϕcxn'].
    assert (eq: S y = f' x). eapply 安定平稳; eauto.
    unfold f' in eq. destruct (f x); congruence.
  - intros [x fx].
    destruct (def' x) as [n ϕcxn]. exists ⟨x, n⟩.
    unfold f' in ϕcxn. now rewrite GF, ϕcxn, fx.
Qed.

Corollary CT_to_EAₒ : CT → EAₒ.
Proof. intros ct. now apply EA_to_EAₒ, CT_to_EA. Qed.

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

Lemma EPF_to_CT : EPF → CT.
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
    destruct f as [y'|].
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
  set (λ c x, if ε c x is Some xy then Some ⎞xy⎛ else None) as h.
  set (λ c, G (h c)) as ε'. exists ε'. intros f.
  set (λ n, if F f n is Some (x, y) then Some ⟨x, y⟩ else None) as f'.
  destruct (ea f') as [c Hc].
  assert (Fun: 函数性配对 (h c)). {
    intros n m x y z H1 H2. unfold h in H1, H2.
    destruct ε as [xy|] eqn:εcn in H1. 2:discriminate.
    destruct ε as [xz|] eqn:εcm in H2. 2:discriminate.
    inversion H1 as [eq1]. apply G_to_F in eq1. rewrite eq1 in εcn.
    inversion H2 as [eq2]. apply G_to_F in eq2. rewrite eq2 in εcm.
    destruct (proj1 (Hc ⟨x, y⟩)) as [s Hs]; eauto.
    destruct (proj1 (Hc ⟨x, z⟩)) as [t Ht]; eauto. unfold f' in Hs, Ht.
    destruct F eqn:Ffs in Hs. 2:discriminate. destruct p as [x1 y1].
    destruct F eqn:Fft in Ht. 2:discriminate. destruct p as [x2 y2].
    inversion Hs as [eq3]. inversion Ht as [eq4].
    apply F单射 in eq3 as [], eq4 as []; subst.
    assert (f x ?= y). apply F规则; eauto.
    assert (f x ?= z). apply F规则; eauto.
    eapply 解包关系单射; eauto.
  }
  exists c. intros x y. split.
  - intros. apply G规则 in H as [n H1]. unfold h in H1.
    destruct ε as [xy|] eqn:εcn in H1. 2:discriminate.
    destruct (proj1 (Hc xy)) as [m H2]; eauto. unfold f' in H2.
    destruct F as [xy'|] eqn:Ffm in H2. 2:discriminate.
    destruct xy' as [x' y']. inversion H1 as [eq1]. inversion H2 as [eq2].
    apply G_to_F in eq1. rewrite eq1 in eq2.
    apply F单射 in eq2 as []; subst. apply F规则. eauto.
  - intros. apply F规则 in H as [n H1].
    destruct (proj2 (Hc ⟨x, y⟩)) as [m H2]. {
      exists n. unfold f'. now rewrite H1.
    }
    unfold ε'. apply G规则_反向 with m. apply Fun.
    unfold h. now rewrite H2, GF.
Qed.

Theorem EA_iff_EPF : EA ⇔ EPF.
Proof. split. apply EA_to_EPF. apply EPF_to_EA. Qed.

Theorem CT_iff_EPF : CT ⇔ EPF.
Proof.
  split.
  - intros ct. eapply EA_to_EPF, CT_to_EA, ct.
  - apply EPF_to_CT.
Qed.

End 给定偏函数模型.

Require Import PartialFuncImpl.

Theorem CT_iff_EA : CT ⇔ EA.
Proof.
  split.
  - intros ct. eapply CT_to_EA, ct.
  - intros ea. eapply EPF_to_CT, EA_to_EPF, ea.
Qed.
