module

public import Foxglove.Interp.OracleComp.Law
public import Foxglove.Rules

/-! # Specifications from VCVio's distributions

`lawOf_interp` identifies Foxglove's law of an `OracleComp` program with VCVio's output measure.
Through `WP_SAMP` (Bluebell, Fig. 10), every distributional fact VCVio proves about a closed
program is then a Foxglove specification: if VCVio's `𝒟[oa]` is the law `ν`, the result of
`oa` has law `ν` in the logic. -/

@[expose] public section
namespace Foxglove

open Interp

noncomputable section

variable {ι α : Type} {oSpec : OracleSpec ι} [OracleBernoulliInterpretable oSpec]
  [oSpec.AnswerMeasure] [LawfulOracleBernoulliInterpretable oSpec]
  [Inhabited α] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {oa : OracleComp oSpec α} {ν : PMF α}

/-- **VCVio's distribution is a Foxglove law.**  If VCVio puts mass `ν a` on each output `a`
of `oa`, the result of `oa` has law `ν`: `WP_SAMP` at the law `lawOf_interp` computes. -/
theorem wp_of_evalDist (h : ∀ a, 𝒟[oa] {a} = ν a) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  Proofs.WP_SAMP (interp oa) ν fun a ↦ (lawOf_interp oa a).trans (h a)

/-- `wp_of_evalDist`, from an equation of measures. -/
theorem wp_of_evalDist_eq_toMeasure (h : 𝒟[oa] = ν.toMeasure) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  wp_of_evalDist fun a ↦ by
    rw [h, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `wp_of_evalDist`, in VCVio's event notation. -/
theorem wp_of_prEvent (h : ∀ a, Pr{let x ← oa}[x = a] = ν a) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  Proofs.WP_SAMP (interp oa) ν fun a ↦ (lawOf_interp_eq_prEvent oa a).trans (h a)

end

end Foxglove
