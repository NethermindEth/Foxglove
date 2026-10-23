module

public import Foxglove.Interp.OracleComp.Adequacy
public import VCVio.ProgramLogic.Unary.WP.Measure

/-! # Expectations: Foxglove laws in Lean's `Std.WP`

VCVio's expectation reading of Lean core's weakest precondition, `Std.WP.wp mx post ⊥` under
`ExpectationWP.Lower`, is the expectation of `post` under the output measure `𝒟[mx]`; it is the
`ℝ≥0∞`-valued carrier of VCVio's program logic and of core `vcgen` on it.  Through the agreement
of semantics it reads Foxglove's laws:

* `wp_eq_tsum_lawOf`: on a coin program, the expectation is the sum against `lawOf`;
* `wp_eq_tsum_of_wp`: a Foxglove law `⊢ wp oa ⦃X, X ~ ν⦄` computes the expectation of every
  postcondition, `∑' a, ν a * post a`.
-/

@[expose] public section
namespace Foxglove.Expectation

open Interp
open scoped ENNReal ExpectationWP.Lower

noncomputable section

variable {α : Type} [Countable α]

/-- **The expectation reading of a coin program is its expectation under `lawOf`.** -/
theorem wp_eq_tsum_lawOf (t : BernoulliM α) (post : α → ℝ≥0∞) :
    Std.WP.wp t post Lean.Order.bot = ∑' a, ProbTree.lawOf t a * post a := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.Lower.wp_eq_lintegral t post Measurable.of_discrete,
    MeasureTheory.lintegral_countable']
  exact tsum_congr fun a ↦ by rw [lawOf_eq_evalDist, mul_comm]

variable {ι : Type} {oSpec : OracleSpec ι} [OracleBernoulliInterpretable oSpec]
  [oSpec.AnswerMeasure] [LawfulOracleBernoulliInterpretable oSpec]

/-- **A Foxglove law computes `Std.WP` expectations.**  If the logic gives the result of `oa`
the law `ν`, the expectation reading of `oa`'s core weakest precondition for `post` is `ν`'s
expectation of `post`. -/
theorem wp_eq_tsum_of_wp [Inhabited α] {oa : OracleComp oSpec α} {ν : PMF α}
    (h : ⊢ Foxglove.wp oa ⦃X, X ~ ν⦄) (post : α → ℝ≥0∞) :
    Std.WP.wp oa post Lean.Order.bot = ∑' a, ν a * post a := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.Lower.wp_eq_lintegral oa post Measurable.of_discrete,
    MeasureTheory.lintegral_countable']
  exact tsum_congr fun a ↦ by rw [evalDist_of_wp h a, mul_comm]

end

end Foxglove.Expectation
