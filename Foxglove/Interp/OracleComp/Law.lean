module

public import Foxglove.Interp.Bernoulli.Helper
public import Foxglove.Interp.OracleComp.Basic
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.SimSemantics.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-! # Agreement with VCVio's semantics

Foxglove gives an `OracleComp` program a meaning of its own: `interp` compiles it to coin flips,
and `lawOf` reads off the law of the result from the tape semantics.  VCVio gives the same program
its output measure `𝒟[oa]`.  This file proves that the two agree.

The proof factors through the observation that `BernoulliM` is itself a free monad of VCVio's
kind -- an `OracleComp` whose only oracle is a biased coin -- and that `interp` is VCVio's
`simulateQ` with the coin-flip implementation `interp_op`.

* `lawOf_eq_evalDist`: on coin programs, the tape law is VCVio's output measure, once each flip
  is given the law `bernoulliWeights` (the instance below).  So the tape law is a `PMF`,
  `lawPMF`.
* `LawfulOracleBernoulliInterpretable`: an oracle implementation is lawful when each query's
  coin-flip implementation has the answer measure VCVio assigns to that query.  `unifSpec` is
  lawful: rejection sampling `split` is uniform (`lawOf_split`); sums of lawful implementations
  are lawful.
* `lawOf_interp`: for a lawful implementation, the law of every `OracleComp` program agrees with
  VCVio's, `lawOf (interp oa) a = 𝒟[oa] {a} = Pr{let x ← oa}[x = a]`.
-/

@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace MeasureTheory ProbabilityTheory unitInterval OracleSpec OracleComp Helper
open scoped ENNReal

noncomputable section

/-! ## Coin programs -/

/-- **A flip is a Bernoulli trial.**  The answer measure of the coin oracle `Flip r`: `true`
with probability `r`.  With it, VCVio's measure semantics `𝒟[·]` applies to `BernoulliM`, which,
like VCVio's `OracleComp`, is a `PFunctor.FreeM`. -/
instance : PFunctor.AnswerMeasure BernoulliPFunctor where
  toMeasure | .Flip r => (bernoulliWeights r).toMeasure
  isProbabilityMeasure | .Flip _ => inferInstance

@[simp]
lemma toMeasure_flip (r : I) :
    PFunctor.AnswerMeasure.toMeasure (P := BernoulliPFunctor) (.Flip r) =
      (bernoulliWeights r).toMeasure :=
  rfl

/-- **A flip is distributed as `bernoulliWeights`** under VCVio's measure semantics, as under
the tape semantics (`WP_FLIP`). -/
@[simp]
lemma evalDist_flip (r : I) : 𝒟[flip r] = (bernoulliWeights r).toMeasure :=
  PFunctor.FreeM.evalDist_lift (P := BernoulliPFunctor) (.Flip r)

/-- **Tape agreement.**  The law a coin program's tape run puts on `a` is the mass VCVio's
measure semantics puts on `a`: both fold the program, flip by flip, with the same weights. -/
theorem lawOf_eq_evalDist {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (t : BernoulliM α) (a : α) : ProbTree.lawOf t a = 𝒟[t] {a} := by
  induction t with
  | pure x =>
    rw [ProbTree.lawOf_pure]
    split_ifs with h <;> simp [h, Ne.symm]
  | liftBind op cont ih =>
    -- one flip: both sides weigh the two continuations by the flip's law
    rcases op with ⟨r⟩
    rw [ProbTree.lawOf_liftBind,
      PFunctor.FreeM.evalDist_liftBind _ cont Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (measurableSet_singleton a) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool]
    simp [ih, ProbTree.flipWeight_eq_bernoulliWeights, mul_comm]

/-- **The law of a coin program**, as a `PMF`: the masses `lawOf t a`, which sum to one because
they are VCVio's output measure of `t`. -/
def lawPMF {α : Type} [Countable α] (t : BernoulliM α) : PMF α :=
  letI : MeasurableSpace α := ⊤
  𝒟[t].toPMF

@[simp]
lemma lawPMF_apply {α : Type} [Countable α] (t : BernoulliM α) (a : α) :
    lawPMF t a = ProbTree.lawOf t a := by
  let : MeasurableSpace α := ⊤
  rw [lawPMF, Measure.toPMF_apply, lawOf_eq_evalDist]

/-- The tape law, as a measure, is VCVio's output measure. -/
theorem toMeasure_lawPMF {α : Type} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (t : BernoulliM α) : (lawPMF t).toMeasure = 𝒟[t] :=
  Measure.ext_of_singleton fun a ↦ by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), lawPMF_apply,
      lawOf_eq_evalDist]

/-! ## `interp` is `simulateQ` -/

/-- `interp` is the interpretation of `OracleComp` in the sense of `BernoulliInterpretable`, which
is how `wp` and `run` see an `OracleComp` program. -/
@[simp]
lemma interp_oracleComp {α ι : Type} {oSpec : OracleSpec ι} [OracleBernoulliInterpretable oSpec]
    (oa : OracleComp oSpec α) : BernoulliInterpretable.interp oa = interp oa :=
  rfl

/-- **Compiling to coins is VCVio's simulation.**  `interp` substitutes `interp_op t` for each
query `t`, which is exactly what VCVio's `simulateQ` does with the implementation `interp_op`. -/
theorem interp_eq_simulateQ {α ι : Type} {oSpec : OracleSpec ι}
    [OracleBernoulliInterpretable oSpec] (oa : OracleComp oSpec α) :
    interp oa =
      simulateQ (OracleBernoulliInterpretable.interp_op : QueryImpl oSpec BernoulliM) oa := by
  induction oa with
  | pure a => rfl
  | queryBind t k ih => exact congrArg _ (funext ih)

/-! ## Lawful oracle implementations -/

/-- **An oracle implementation is lawful** when each query's coin-flip implementation has the
answer measure VCVio assigns to that query.  This is a law about distributions, relative to the
chosen `OracleSpec.AnswerMeasure`, not the monad-morphism law of `LawfulBernoulliInterpretable`
(which `interp` satisfies for every implementation).  Answers carry the discrete σ-algebra `⊤`,
as in `OracleSpec.AnswerMeasure`. -/
class LawfulOracleBernoulliInterpretable {ι : Type} (oSpec : OracleSpec ι)
    [OracleBernoulliInterpretable oSpec] [oSpec.AnswerMeasure] : Prop where
  evalDist_interp_op (t : oSpec.Domain) :
    @evalDist BernoulliM _ (oSpec.Range t) ⊤ (OracleBernoulliInterpretable.interp_op t) =
      AnswerMeasure.toMeasure t

/-- **Sums of lawful implementations are lawful**: VCVio's answer measure on a sum of
specifications is the summands' (`OracleSpec.AnswerMeasure.add`), and so is Foxglove's
implementation. -/
instance {ι₁ ι₂ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
    [OracleBernoulliInterpretable oSpec₁] [OracleBernoulliInterpretable oSpec₂]
    [oSpec₁.AnswerMeasure] [oSpec₂.AnswerMeasure]
    [LawfulOracleBernoulliInterpretable oSpec₁] [LawfulOracleBernoulliInterpretable oSpec₂] :
    LawfulOracleBernoulliInterpretable (oSpec₁ + oSpec₂) where
  evalDist_interp_op
    | .inl t => LawfulOracleBernoulliInterpretable.evalDist_interp_op (oSpec := oSpec₁) t
    | .inr t => LawfulOracleBernoulliInterpretable.evalDist_interp_op (oSpec := oSpec₂) t

section Agreement

variable {ι α : Type} {oSpec : OracleSpec ι} [OracleBernoulliInterpretable oSpec]
  [oSpec.AnswerMeasure] [LawfulOracleBernoulliInterpretable oSpec]

/-- **Compiling to coins preserves the output measure** of every program. -/
@[simp]
theorem evalDist_interp [MeasurableSpace α] (oa : OracleComp oSpec α) :
    𝒟[interp oa] = 𝒟[oa] := by
  rw [interp_eq_simulateQ]
  exact OracleComp.evalDist_simulateQ_eq_of_forall _
    LawfulOracleBernoulliInterpretable.evalDist_interp_op oa

/-- **Foxglove's law of a program is VCVio's.** -/
theorem lawOf_interp [MeasurableSpace α] [MeasurableSingletonClass α] (oa : OracleComp oSpec α)
    (a : α) : ProbTree.lawOf (interp oa) a = 𝒟[oa] {a} := by
  rw [lawOf_eq_evalDist, evalDist_interp]

/-- `lawOf_interp` in VCVio's event notation. -/
theorem lawOf_interp_eq_prEvent (oa : OracleComp oSpec α) (a : α) :
    ProbTree.lawOf (interp oa) a = Pr{let x ← oa}[x = a] := by
  let : MeasurableSpace α := ⊤
  rw [lawOf_interp, prEvent_eq_evalDist_singleton]

end Agreement

/-! ## The uniform oracle -/

/-- **Rejection sampling from `m` upwards is uniform on `{m, …, n-1}`**, as a law. -/
lemma lawOf_split' {n : ℕ} (m i : Fin n) :
    ProbTree.lawOf (split' m) i = if m ≤ i then ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  have hi := i.isLt
  induction m using split'.induct with
  | case1 m h₁ =>
    -- the last outcome: no flip left, report `m`
    have hsplit : split' m = (PFunctor.FreeM.pure m : BernoulliM (Fin n)) := by
      rw [split', dite_eq_left h₁]
      rfl
    rw [hsplit, ProbTree.lawOf_pure]
    by_cases hmi : i = m
    · subst hmi; simp [show n - i.1 = 1 by omega]
    · rw [ite_eq_right hmi, ite_eq_right (by rw [Fin.le_def]; omega)]
  | case2 m h₁ ih =>
    -- flip: report `m` with probability `1/(n - m)`, else recurse from `m + 1`
    have hm'lt : m.1 + 1 < n := by omega
    set P : I := ⟨(↑(mkRat 1 (n - m.1)) : ℝ), mkRat_mem_I (by omega)⟩
    have hP : (unitInterval.toNNReal P : ℝ≥0∞) = ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ :=
      toNNReal_mkRat (n - m.1) (by omega) _
    have hsplit : split' m = PFunctor.FreeM.liftBind (BernoulliOps.Flip P)
        (fun b ↦ if b then (PFunctor.FreeM.pure m : BernoulliM (Fin n))
                 else split' ⟨m.1 + 1, hm'lt⟩) := by
      rw [split', dite_eq_right h₁]
      rfl
    rw [hsplit, ProbTree.lawOf_liftBind]
    simp only [ite_true, Bool.false_eq_true, ite_false, ProbTree.lawOf_pure, ih,
      ProbTree.flipWeight, hP, Fin.le_def, Fin.ext_iff]
    rcases lt_trichotomy i.1 m.1 with hlt | heq | hgt
    · simp [hlt.ne, hlt.not_ge, show ¬ m.1 + 1 ≤ i.1 by omega]
    · simp [heq]
    · -- having failed with probability `1 - 1/(n - m)`, the rest is uniform on `n - m - 1`
      rw [ite_eq_right hgt.ne', ite_eq_left (by omega), ite_eq_left hgt.le, mul_zero, zero_add,
        show n - (m.1 + 1) = (n - m.1) - 1 by omega]
      exact mix_step (n - m.1) (by omega)

/-- **`split n` is uniform on `Fin (n + 1)`**, as a law. -/
lemma lawOf_split (n : ℕ) (i : Fin (n + 1)) :
    ProbTree.lawOf (split n) i = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [split, lawOf_split']

/-- **`split n` has VCVio's uniform measure.** -/
lemma evalDist_split (n : ℕ) : 𝒟[split n] = uniformOn (Set.univ : Set (Fin (n + 1))) :=
  Measure.ext_of_singleton fun i ↦ by simp [← lawOf_eq_evalDist, lawOf_split, uniformOn_univ]

/-- **The uniform oracle is lawfully implemented** by rejection sampling. -/
instance : LawfulOracleBernoulliInterpretable unifSpec :=
  ⟨fun n ↦ (evalDist_split n).trans (AnswerMeasure.toMeasure_eq_uniformOn n).symm⟩

end

end Interp

end Foxglove
