(** Coq coding by choukh, July 2022 **)

Require Import Notions NatEmbed PartialFunc Discrete Reductions.

Section 可枚举性.
Context {M : 偏函数模型} {A B : Type} {p : A → Prop} {r : A → B → Prop}.

Local Lemma 参数化枚举器_枚举器 f g : 枚举器ᵀ f → 参数化枚举器 r g →
  枚举器 (uncurry r) (λ' ⟨n, m⟩, if f n is Some x then
    if g x m is Some y then Some (x, y) else None else None).
Proof.
  intros Hf Hg. intros (x, y). cbn.
  rewrite (Hg x y). split.
  - intros [m gxm]. destruct (Hf x) as [[n fn] _]. easy.
    exists ⟨n, m⟩. now rewrite GF, fn, gxm.
  - intros [nm H]. destruct ⎞nm⎛ as [n m].
    destruct f as [x'|]. 2:discriminate.
    destruct g as [y'|] eqn:E; inv H. eauto.
Qed.

Local Lemma 枚举器_参数化枚举器 f g :
  判定器 (uncurry (λ x y, x = y)) f → 枚举器 (uncurry r) g →
  参数化枚举器 r (λ x n, if g n is Some (x', y) then
    if f (x, x') then Some y else None else None).
Proof.
  intros Hf Hg. intros x y.
  rewrite (Hg (x, y)). split.
  - intros [n gn]. exists n. rewrite gn.
    now specialize (Hf (x, x)) as [-> _].
  - intros [n H]. destruct g as [(x',y')|] eqn:E. 2:discriminate.
    specialize (Hf (x, x')). destruct f; inv H.
    destruct Hf. rewrite H0 in *; eauto.
Qed.

Lemma 参数化可枚举反柯里化 : 可枚举ᵀ A → 离散 A → 参数化可枚举 r ↔ 可枚举 (uncurry r).
Proof.
  intros [f Hf] [g Hg]. split.
  - intros [h Hh]. eexists. eapply 参数化枚举器_枚举器; eauto.
  - intros [h Hh]. eexists. eapply 枚举器_参数化枚举器; eauto.
Qed.

Lemma 反柯里化可枚举嵌入 (s : ℕ → ℕ → Prop) : 可枚举 (uncurry s) → 可枚举 (λ' ⟨x, y⟩, s x y).
Proof.
  intros. eapply (@可枚举性归约 ℕ (ℕ * ℕ)); eauto. exists G.
  intros xy. destruct ⎞xy⎛ as [x y]. reflexivity.
Qed.

Lemma 可枚举的偏函数表述 : 可枚举 p ↔ ∃ f : ℕ ⇀ A, ∀ x, p x ↔ ∃ n, f n ?= x.
Proof.
  split.
  - intros [f Hf]. exists (λ n, if f n is Some x then 有 x else 无).
    intros x. rewrite (Hf x).
    split; intros [n H]; exists n; destruct (f n).
    + apply 有值解包. congruence.
    + congruence.
    + apply 有值解包 in H. congruence.
    + now apply 无规则 in H.
  - intros [f Hf]. exists (λ' ⟨n, m⟩, 求值 (f n) m).
    intros x. rewrite (Hf x). split.
    + intros [n H]. apply 求值规则 in H as [m H].
      exists ⟨n, m⟩. rewrite GF. easy.
    + intros [nm H]. destruct ⎞nm⎛ as [n m].
      eexists. eapply 求值规则. eauto.
Qed.

End 可枚举性.
