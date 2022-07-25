(** Coq coding by choukh, July 2022 **)

Require Import Bool Notions NatEmbed.

Definition 枚举器ᵀ {A} (f : ℕ → A?) := 枚举器 (λ _, True) f.
Definition 可枚举ᵀ A := ∃ f : ℕ → A?, 枚举器ᵀ f.

Lemma 自然数可枚举 : 可枚举ᵀ ℕ.
Proof. exists (λ n, Some n). split; eauto. Qed.
Global Hint Resolve 自然数可枚举 : core.

Local Lemma 积类型枚举器 {A B} (f : ℕ → A?) (g : ℕ → B?) : 枚举器ᵀ f → 枚举器ᵀ g →
  枚举器ᵀ (λ' ⟨n, m⟩, if (f n, g m) is (Some x, Some y) then Some (x, y) else None).
Proof.
  intros Hf Hg (a, b). split; auto. intros _.
  destruct (Hf a) as [[n fn] _], (Hg b) as [[m gm] _]; auto.
  exists ⟨n, m⟩. now rewrite GF, fn, gm.
Qed.

Lemma 积类型可枚举 {A B} : 可枚举ᵀ A → 可枚举ᵀ B → 可枚举ᵀ (A * B).
Proof. intros [] []; eexists; now eapply 积类型枚举器. Qed.
Global Hint Resolve 积类型可枚举 : core.

Notation 可识别 A := (∀ x y : A, 命题可判定 (x = y)).

Structure 可识别类型 := {
  ID载体 :> Type;
  ID性质 : 可识别 ID载体
}.

Global Instance 自然数可识别 : 可识别 ℕ.
Proof. unfold 命题可判定. decide equality. Qed.

Global Instance 布尔类型可识别 : 可识别 bool.
Proof. unfold 命题可判定. decide equality. Qed.

Global Instance 可选类型可识别 A : 可识别 A → 可识别 (option A).
Proof. unfold 命题可判定. decide equality. Qed.

Global Instance 积类型可识别 A B : 可识别 A → 可识别 B → 可识别 (A * B).
Proof. unfold 命题可判定. decide equality. Qed.

Lemma 命题可判定_iff_可判定 {A} (p : A → Prop) :
  inhabited (∀ x, 命题可判定 (p x)) ↔ 可判定 p.
Proof.
  split.
  - intros [dec]. exists (λ x, if dec x then true else false).
    intros x. destruct (dec x); firstorder congruence.
  - intros [f H]. constructor. intros x. specialize (H x).
    destruct (f x); firstorder congruence.
Qed.

Definition 离散 A := @可判定 (A * A) (uncurry (λ x y, x = y)).

Lemma 离散_iff_可识别 A : 离散 A ↔ inhabited (可识别 A).
Proof.
  split.
  - intros dec. apply 命题可判定_iff_可判定 in dec as [dec].
    constructor. intros x y. destruct (dec (x, y)); firstorder.
  - intros [dec]. apply 命题可判定_iff_可判定.
    constructor. intros (x, y). apply dec.
Qed.

Lemma 自然数离散 : 离散 ℕ.
Proof. apply 离散_iff_可识别. auto. Qed.
Global Hint Resolve 自然数离散 : core.

Lemma 布尔类型离散 : 离散 bool.
Proof. apply 离散_iff_可识别. auto. Qed.

Lemma 可选类型离散 A : 离散 A → 离散 (option A).
Proof.
  intros [H] % 离散_iff_可识别.
  eapply 离散_iff_可识别. constructor. auto.
Qed.

Lemma 积类型离散 A B : 离散 A → 离散 B → 离散 (A * B).
Proof.
  intros [H1] % 离散_iff_可识别 [H2] % 离散_iff_可识别.
  eapply 离散_iff_可识别. constructor. auto.
Qed.
Global Hint Resolve 积类型离散 : core.
