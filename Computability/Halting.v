(** Coq coding by choukh, July 2022 **)

Require Import Nat NatEmbed Notions Discrete Equivalence PartialFunc.
Require Import SCT CT DecidabilityFacts Reductions EnumerabilityFacts.

Section 假设EAᵖ.
Hypothesis ea : EAᵖ.

Notation ε := (projT1 ea).
Notation ea_ε := (projT2 ea).
Notation W := (W ε).

Lemma ea_W (p : ℕ → Prop) : 可枚举 p ↔ ∃ c, ∀ x, p x ↔ W c x.
Proof.
  split.
  - intros H. apply ea_ε in H as [c Hc].
    exists c. intros x. unfold W.
    pose proof (Hc x). firstorder.
  - intros [c Hc]. exists (ε c). firstorder.
Qed.

(* 可输出自身 *)
Definition K c := W c c.

(* 不可枚举不可输出自身的代码 *)
Lemma K余不可枚举 : ¬ 可枚举 K⁻.
Proof. intros H. apply ea_W in H as [c H]. firstorder. Qed.

(* 不可判定不可输出自身的代码 *)
Lemma K余不可判定 : ¬ 可判定 K⁻.
Proof. intros H. now apply K余不可枚举, 自然数_可判定_可枚举. Qed.

(* 不可判定可输出自身的代码 *)
Lemma K不可判定 : ¬ 可判定 K.
Proof. intros H. eapply 余不可判定_不可判定. apply K余不可判定. apply H. Qed.

Lemma K归约W : K ≤ₘ uncurry W.
Proof. exists (λ n, (n, n)). firstorder. Qed.

Corollary K余归约W : K⁻ ≤ₘ (uncurry W)⁻.
Proof. apply 余归约, K归约W. Qed.

Corollary W余不可枚举 : ¬ 可枚举 (uncurry W)⁻.
Proof.
  intros H. eapply K余不可枚举. eapply 可枚举性归约.
  apply K余归约W. auto. auto. apply H.
Qed.

Corollary W余不可判定 : ¬ 可判定 (uncurry W)⁻.
Proof.
  intros H. eapply K余不可判定. eapply 可判定性归约. apply K余归约W. apply H.
Qed.

Corollary W不可判定 : ¬ 可判定 (uncurry W).
Proof.
  intros H. eapply K不可判定. eapply 可判定性归约. apply K归约W. apply H.
Qed.

Lemma W可枚举 : 可枚举 (uncurry W).
Proof.
  exists (λ' ⟨c, n⟩, if ε c n is Some x then Some (c, x) else None).
  intros [c n]. split.
  - intros [m εcm]. exists ⟨c, m⟩. now rewrite GF, εcm.
  - intros [dm fdm]. destruct ⎞dm⎛ as [d m].
    destruct (ε d m) eqn:εdm; inv fdm. now exists m.
Qed.

Corollary W半可判定 : 半可判定 (uncurry W).
Proof. apply 可枚举_半可判定. auto. apply W可枚举. Qed.

(* 可枚举可输出自身的代码 *)
Corollary K可枚举 : 可枚举 K.
Proof. eapply 可枚举性归约. apply K归约W. auto. auto. apply W可枚举. Qed.

Corollary K半可判定 : 半可判定 K.
Proof. apply 自然数_可枚举_iff_半可判定, K可枚举. Qed.

(* 自然数谓词可枚举等价于可归约到停机问题 *)
Lemma 可枚举_iff_可归约到W {p : ℕ → Prop} : 可枚举 p ↔ p ≤ₘ uncurry W.
Proof.
  split.
  - intros H. apply ea_W in H as [c Hc]. now exists (λ x, (c, x)).
  - intros red. eapply 可枚举性归约. apply red. auto. auto. apply W可枚举.
Qed.

(* 自然数谓词半可判定等价于可归约到停机问题 *)
Lemma 半可判定_iff_可归约到W {p : ℕ → Prop} : 半可判定 p ↔ p ≤ₘ uncurry W.
Proof.
  rewrite <- 可枚举_iff_可归约到W. split.
  - apply 半可判定_可枚举. auto.
  - apply 可枚举_半可判定. auto.
Qed.

Section 假设SMN.

Hypothesis smn : SMNᵂ W.
Definition sea_ε : (SEAᵖₑ ε) := EAᵖ_SMNᵂ_to_SEAᵖₑ ea smn.

Lemma 参数化ea_W (pᵢ : ℕ → ℕ → Prop) : 可枚举 (uncurry pᵢ) → ∃ cᵢ, ∀ i, 枚举器 (pᵢ i) (ε (cᵢ i)).
Proof. intros H. apply 参数化可枚举反柯里化, sea_ε in H; auto. Qed.

Lemma W反柯里化嵌入 : uncurry W ≡ₘ λ' ⟨n, m⟩, W n m.
Proof.
  split.
  - exists (λ '(n, m), ⟨n, m⟩). intros [n m]. now rewrite GF.
  - exists (λ' ⟨n, m⟩, (n, m)). intros nm. now destruct ⎞nm⎛ as [n m].
Qed.

Lemma W归约K : uncurry W ≤ₘ K.
Proof.
  eapply 多一归约传递. apply W反柯里化嵌入.
  destruct (参数化ea_W (λ' ⟨x, y⟩, λ _, W x y)) as [cᵢ Hcᵢ].
  - apply 可枚举性归约 with (uncurry W); auto. 2: apply W可枚举.
    exists (λ '(xy, _), (λ' ⟨x, y⟩, (x, y)) xy).
    intros [xy z]. now destruct ⎞xy⎛ as [x y].
  - exists cᵢ. intros xy. unfold K. rewrite <- (Hcᵢ xy (cᵢ xy)).
    now destruct ⎞xy⎛ as [x y].
Qed.

Corollary K等价于W : K ≡ₘ uncurry W.
Proof. split. apply K归约W. apply W归约K. Qed.

Corollary 可枚举_iff_可归约到K {p : ℕ → Prop} : 可枚举 p ↔ p ≤ₘ K.
Proof.
  split.
  - intros enum. eapply 多一归约传递.
    now apply 可枚举_iff_可归约到W. apply W归约K.
  - intros red. eapply 可枚举_iff_可归约到W.
    eapply 多一归约传递. apply red. apply K归约W.
Qed.

Corollary 半可判定_iff_可归约到K {p : ℕ → Prop} : 半可判定 p ↔ p ≤ₘ K.
Proof.
  split.
  - intros enum. eapply 多一归约传递.
    now apply 半可判定_iff_可归约到W. apply W归约K.
  - intros red. eapply 半可判定_iff_可归约到W.
    eapply 多一归约传递. apply red. apply K归约W.
Qed.

End 假设SMN.
End 假设EAᵖ.
