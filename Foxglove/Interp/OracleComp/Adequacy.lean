module

public import Foxglove.Interp.OracleComp.WP

/-! # Adequacy: from Foxglove specifications to VCVio's distributions

A closed program's specification determines its law.  Running the program from the unit
ambient footprint produces one space at which every specification proved for it holds
(`pure_of_wp_of_wp`), and `DIST_INJ` at that space makes the laws two specifications assign to
its result agree.  Since `WP_SAMP` already gives a program the law `lawOf`, any law a
specification gives it is that one (`lawOf_of_wp`), and so, through `lawOf_interp`, VCVio's.

* `evalDist_of_wp`: if `⊢ wp oa ⦃X, X ~ ν⦄`, then VCVio's `𝒟[oa]` puts mass `ν a` on `a`.
  With `wp_of_evalDist` this is `wp_hasDistribution_iff`.
* `exists_evalDist_of_wp`, `exists_prEvent_of_wp`: the same for specifications that only
  describe the law, `⦃X, ∃ μ, ⌜P μ⌝ ∗ X ~ μ⦄`, which is how the worked examples state their
  results.  At the level of coin programs these are `lawPMF_eq_of_wp` and `lawPMF_of_wp`.
-/

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra BI UpperSetBI OURAProp
open Interp Interp.ProbTree

noncomputable section

/-! ## Reading specifications at the unit ambient -/

section Ambient

variable {α : Type} [Inhabited α] {m : Type → Type} [BernoulliInterpretable m] {t : m α}

/-- **A specification holds at a run.**  Run `t` from the unit ambient: `⊢ wp t Q` produces a
witness below the run's space, so owning that space gives `Q` of the run's result. -/
theorem own_run_entails_of_wp {Q : RV α → FProp} (h : ⊢ wp t Q) :
    own (run t (1 : BoundedFootprintPsp)).1.toSpace ⊢ Q (result (run t 1)) := by
  obtain ⟨b, hb₁, -, -, hb₂⟩ := h 1 valid_one (le_refl (1 : BoundedFootprintSpace Bool)) 1 1
    BoundedFootprintPsp.valid_one (mul_one _).le
  rw [mul_one] at hb₁
  exact (own_mono hb₁).trans hb₂

/-- **A closed program's specification is sound for pure facts**: whatever it entails at the
run's result is true. -/
theorem pure_of_wp {Q : RV α → FProp} {φ : Prop} (h : ⊢ wp t Q) (hφ : ∀ X, Q X ⊢ ⌜φ⌝) : φ :=
  (own_run_entails_of_wp h).trans (hφ _) _ (valid_run t 1 BoundedFootprintPsp.valid_one)
    (le_refl (run t (1 : BoundedFootprintPsp)).1.toSpace)

/-- **Two specifications hold together at a run**, so whatever they jointly entail is true. -/
theorem pure_of_wp_of_wp {Q Q' : RV α → FProp} {φ : Prop} (h : ⊢ wp t Q) (h' : ⊢ wp t Q')
    (hφ : ∀ X, iprop(Q X ∧ Q' X) ⊢ ⌜φ⌝) : φ :=
  (and_intro (own_run_entails_of_wp h) (own_run_entails_of_wp h')).trans (hφ _) _
    (valid_run t 1 BoundedFootprintPsp.valid_one)
    (le_refl (run t (1 : BoundedFootprintPsp)).1.toSpace)

/-- **A closed program has at most one law.** -/
theorem law_unique_of_wp {ν ν' : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) (h' : ⊢ wp t ⦃X, X ~ ν'⦄) :
    ν = ν' :=
  pure_of_wp_of_wp h h' fun _ ↦ DIST_INJ

end Ambient

/-- A law satisfying `P`, together with a second law, entails that the second satisfies `P`:
`DIST_INJ` identifies the two. -/
private lemma exists_law_and_law {α : Type} {E : RV α} {P : PMF α → Prop} {ν : PMF α} :
    iprop((∃ μ : PMF α, ⌜P μ⌝ ∗ E ~ μ) ∧ E ~ ν) ⊢ ⌜P ν⌝ :=
  and_exists_right.1.trans <| exists_elim fun μ ↦
    (and_mono sep_and entails_rfl).trans <| and_assoc.1.trans <|
      pure_elim_left fun (hP : P μ) ↦ DIST_INJ.trans (pure_mono fun (h : μ = ν) ↦ h ▸ hP)

/-! ## The law of a closed program -/

section Law

variable {α : Type} [Countable α] [Inhabited α] {m : Type → Type} [BernoulliInterpretable m]
  {t : m α}

/-- **Adequacy of laws.**  If the logic gives a closed program the law `ν`, that is its tape
law. -/
theorem lawPMF_eq_of_wp {ν : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) :
    lawPMF (BernoulliInterpretable.interp t) = ν :=
  law_unique_of_wp (Proofs.WP_SAMP _ _ fun a ↦ (lawPMF_apply _ a).symm) h

/-- `lawPMF_eq_of_wp`, pointwise. -/
theorem lawOf_of_wp {ν : PMF α} (h : ⊢ wp t ⦃X, X ~ ν⦄) (a : α) :
    lawOf (BernoulliInterpretable.interp t) a = ν a := by
  rw [← lawPMF_apply, lawPMF_eq_of_wp h]

/-- **Adequacy of law descriptions.**  If the logic gives a closed program some law satisfying
`P`, its tape law satisfies `P`. -/
theorem lawPMF_of_wp {P : PMF α → Prop} (h : ⊢ wp t ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    P (lawPMF (BernoulliInterpretable.interp t)) := by
  -- `wp t` is `wp` of the coin program `t` compiles to
  have h₀ : ⊢ wp (BernoulliInterpretable.interp t) ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄ := h
  exact pure_of_wp_of_wp h₀ (Proofs.WP_SAMP _ _ fun a ↦ (lawPMF_apply _ a).symm)
    fun _ ↦ exists_law_and_law

/-- **A closed program has law `ν` in Foxglove exactly when its tape law is `ν`.** -/
theorem wp_hasDistribution_iff_lawPMF {ν : PMF α} :
    (⊢ wp t ⦃X, X ~ ν⦄) ↔ lawPMF (BernoulliInterpretable.interp t) = ν :=
  ⟨lawPMF_eq_of_wp, fun h ↦ Proofs.WP_SAMP _ ν fun a ↦ h ▸ (lawPMF_apply _ a).symm⟩

/-- `wp_hasDistribution_iff_lawPMF`, pointwise. -/
theorem wp_hasDistribution_iff_lawOf {ν : PMF α} :
    (⊢ wp t ⦃X, X ~ ν⦄) ↔ ∀ a, lawOf (BernoulliInterpretable.interp t) a = ν a :=
  ⟨lawOf_of_wp, Proofs.WP_SAMP _ ν⟩

end Law

/-! ## VCVio's distributions -/

section OracleComp

variable {ι α : Type} {oSpec : OracleSpec ι} [OracleBernoulliInterpretable oSpec]
  [oSpec.AnswerMeasure] [LawfulOracleBernoulliInterpretable oSpec]
  [Inhabited α] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {oa : OracleComp oSpec α} {ν : PMF α}

/-- **A Foxglove law is VCVio's distribution.**  The converse of `wp_of_evalDist`. -/
theorem evalDist_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) (a : α) : 𝒟[oa] {a} = ν a :=
  (lawOf_interp oa a).symm.trans (lawOf_of_wp h a)

/-- `evalDist_of_wp`, as an equation of measures.  The converse of
`wp_of_evalDist_eq_toMeasure`. -/
theorem evalDist_eq_toMeasure_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) : 𝒟[oa] = ν.toMeasure :=
  MeasureTheory.Measure.ext_of_singleton fun a ↦ by
    rw [evalDist_of_wp h a, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `evalDist_of_wp`, in VCVio's event notation. -/
theorem prEvent_of_wp (h : ⊢ wp oa ⦃X, X ~ ν⦄) (a : α) : Pr{let x ← oa}[x = a] = ν a :=
  (lawOf_interp_eq_prEvent oa a).symm.trans (lawOf_of_wp h a)

/-- **A Foxglove law description holds of VCVio's distribution.** -/
theorem exists_evalDist_of_wp {P : PMF α → Prop} (h : ⊢ wp oa ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    ∃ ν : PMF α, P ν ∧ ∀ a, 𝒟[oa] {a} = ν a :=
  ⟨_, lawPMF_of_wp h, fun a ↦ by rw [lawPMF_apply, interp_oracleComp, lawOf_interp]⟩

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `exists_evalDist_of_wp`, in VCVio's event notation. -/
theorem exists_prEvent_of_wp {P : PMF α → Prop} (h : ⊢ wp oa ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄) :
    ∃ ν : PMF α, P ν ∧ ∀ a, Pr{let x ← oa}[x = a] = ν a :=
  ⟨_, lawPMF_of_wp h, fun a ↦ by rw [lawPMF_apply, interp_oracleComp, lawOf_interp_eq_prEvent]⟩

/-! ### Both directions -/

/-- **A program has law `ν` in Foxglove exactly when VCVio gives it the distribution `ν`.** -/
theorem wp_hasDistribution_iff : (⊢ wp oa ⦃X, X ~ ν⦄) ↔ ∀ a, 𝒟[oa] {a} = ν a :=
  ⟨evalDist_of_wp, wp_of_evalDist⟩

/-- `wp_hasDistribution_iff`, as an equation of measures. -/
theorem wp_hasDistribution_iff_evalDist_eq_toMeasure :
    (⊢ wp oa ⦃X, X ~ ν⦄) ↔ 𝒟[oa] = ν.toMeasure :=
  ⟨evalDist_eq_toMeasure_of_wp, wp_of_evalDist_eq_toMeasure⟩

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `wp_hasDistribution_iff`, in VCVio's event notation. -/
theorem wp_hasDistribution_iff_prEvent :
    (⊢ wp oa ⦃X, X ~ ν⦄) ↔ ∀ a, Pr{let x ← oa}[x = a] = ν a :=
  ⟨prEvent_of_wp, wp_of_prEvent⟩

end OracleComp

end

end Foxglove
