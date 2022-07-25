
(** Coq coding by choukh, July 2022 **)
Require Import Notions NatEmbed PartialFunc Discrete.

Section 可判定性.
Context {M : 偏函数模型} {A : Type} {p : A → Prop}.

Lemma 可判定_余可判定 : 可判定 p → 可判定 p⁻.
Proof.
  intros [f Hf]. exists (λ x, negb (f x)).
  intros x. pose proof (Hf x).
  destruct (f x); simpl; rewrite H; intuition.
Qed.

Lemma 余不可判定_不可判定 : ¬ 可判定 p⁻ → ¬ 可判定 p.
Proof. intros H1 H2. apply H1, 可判定_余可判定, H2. Qed.

Lemma 可判定_半可判定 : 可判定 p → 半可判定 p.
Proof.
  intros [f Hf]. exists (λ x _, f x). intros x.
  unfold 判定器 in Hf. rewrite Hf. firstorder. econstructor.
Qed.

Lemma 半可判定_可枚举 : 可枚举ᵀ A → 半可判定 p → 可枚举 p.
Proof.
  unfold 半可判定, 半判定器. intros [f Hf] [g Hg].
  exists (λ' ⟨n, m⟩, if f n is Some x then
    if g x m then Some x else None
  else None ).
  intros x. rewrite Hg. split.
  - intros [m gxm]. destruct (Hf x) as [[n fn] _]. easy.
    exists ⟨n, m⟩. rewrite GF, fn, gxm. easy.
  - intros [nm hnm]. destruct ⎞nm⎛ as (n, m).
    destruct (f n) as [x'|]. 2:discriminate.
    destruct (g x' m) eqn:E. 2:discriminate.
    inv hnm. eauto.
Qed.

Lemma 可枚举_半可判定 : 离散 A → 可枚举 p → 半可判定 p.
Proof.
  unfold 可枚举, 枚举器. intros [f Hf] [g Hg].
  exists (λ x n, if g n is Some y then f (x, y) else false).
  intros x. rewrite Hg. split.
  - intros [n Hn]. exists n. rewrite Hn. now apply Hf.
  - intros [n Hn]. exists n. destruct (g n).
    apply Hf in Hn. now subst. discriminate.
Qed.

Lemma 可判定_可枚举 : 可枚举ᵀ A → 可判定 p → 可枚举 p.
Proof.
  intros. apply 半可判定_可枚举. easy.
  apply 可判定_半可判定. easy.
Qed.

Lemma 半可判定的偏函数表述 : 半可判定 p ↔ ∃ B (f : A ⇀ B), ∀ x, p x ↔ 有值 (f x).
Proof.
  split.
  - intros [f Hf].
    exists ℕ, (λ x, μ (f x)). intros x.
    rewrite (Hf x). split; intros [n H].
    + eapply μ有值. eauto.
    + eapply μ规则 in H as [H _]. eauto.
  - intros (B & f & Hf).
    exists (λ x n, if 求值 (f x) n is Some _ then true else false).
    intros x. rewrite Hf. split.
    + intros [y H]. apply 求值规则 in H as [n H].
      exists n. rewrite H. easy.
    + intros [n H]. destruct 求值 eqn:E.
      eexists. eapply 求值规则. eauto. discriminate.
Qed.

End 可判定性.

Lemma 自然数_可枚举_iff_半可判定 (p : ℕ → Prop) : 可枚举 p ↔ 半可判定 p.
Proof.
  split. apply 可枚举_半可判定. auto.
  apply 半可判定_可枚举. auto.
Qed.

Lemma 自然数_可判定_可枚举 (p : ℕ → Prop) : 可判定 p → 可枚举 p.
Proof. intros. apply 可判定_可枚举; auto. Qed.
