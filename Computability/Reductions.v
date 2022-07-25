(** Coq coding by choukh, July 2022 **)

Require Import RelationClasses Notions Discrete DecidabilityFacts.

Definition 多一归约器 {A B} (p : A → Prop) (q : B → Prop) (f : A → B) :=
  ∀ x, p x ↔ q (f x).
Definition 多一归约 {A B} (p : A → Prop) (q : B → Prop) :=
  ∃ f, 多一归约器 p q f.

Notation "p ≤ₘ q" := (多一归约 p q) (at level 50).
Notation "p ≡ₘ q" := (p ≤ₘ q ∧ q ≤ₘ p) (at level 50).

Global Instance 多一归约自反 {A} : Reflexive (@多一归约 A A).
Proof. exists (λ x, x). firstorder. Qed.

Lemma 多一归约传递 {A B C} {p : A → Prop} (q : B → Prop) (r : C → Prop) :
  p ≤ₘ q → q ≤ₘ r → p ≤ₘ r.
Proof. intros [f Hf] [g Hg]. exists (λ x, g (f x)). firstorder. Qed.

Section 多一归约.
Context {A B : Type}.
Variable p : A → Prop.
Variable q : B → Prop.

Lemma 余归约 : p ≤ₘ q → p⁻ ≤ₘ q⁻.
Proof. firstorder. Qed.

Lemma 可判定性归约 : p ≤ₘ q → 可判定 q → 可判定 p.
Proof. intros [f Hf] [g Hg]. exists (λ n, g (f n)). firstorder. Qed.

Lemma 半可判定性归约 : p ≤ₘ q → 半可判定 q → 半可判定 p.
Proof. intros [f Hf] [g Hg]. exists (λ n, g (f n)). firstorder. Qed.

Lemma 可枚举性归约 : p ≤ₘ q → 可枚举ᵀ A → 离散 B → 可枚举 q → 可枚举 p.
Proof.
  intros red enumT disc enum.
  apply 半可判定_可枚举. apply enumT.
  apply 半可判定性归约. apply red.
  apply 可枚举_半可判定. apply disc. apply enum.
Qed.

End 多一归约.
