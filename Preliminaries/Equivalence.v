(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import Setoid.

Class 等价关系 (T : Type) := {
  R : T → T → Prop;
  R等价 : Equivalence R
}.

Arguments R _ {_} _ _.
Global Existing Instance R等价.

Notation "a ≡{ T } b" := (@R T _ a b) (format "a  ≡{ T }  b", at level 70).

Global Instance 自然数同一性 : 等价关系 ℕ := {| R := eq |}.

Global Instance 布尔值同一性 : 等价关系 bool := {| R := eq |}.

Global Instance 命题外延 : 等价关系 Prop := {| R := iff |}.

Global Instance 函数外延 {A B} `{等价关系 B} : 等价关系 (A → B).
Proof.
  exists (λ f g : A → B, ∀ x, f x ≡{B} g x). split.
  - intros f x. reflexivity.
  - intros f g fg x. now symmetry.
  - intros f g h fg gh x. now transitivity (g x).
Defined.

Global Instance 共值域 {A B} : 等价关系 (A → B?).
Proof.
  exists (λ f g, ∀ x, (∃ n, f n = Some x) ↔ (∃ n, g n = Some x)). split.
  - intros f x. reflexivity.
  - intros f g fg x. now symmetry.
  - intros f g h fg gh x. now transitivity (∃ n : A, g n = Some x).
Defined.

Notation "f ≡{ran} g" := (@R _ 共值域 f g) (format "f  ≡{ran}  g", at level 80).
