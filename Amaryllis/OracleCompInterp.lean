
-- import VCVio.Prelude.Core
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform

import VCVio.OracleComp.Support
import VCVio.EvalDist.Defs.Support.Failure
import ToMathlib.Control.OptionT
import Batteries.Control.OptionT
import Init.Data.Rat.Basic

import Amaryllis.MeasureOnSpace
import Amaryllis.Model
import Amaryllis.OURA

namespace Amaryllis

namespace BernoulliInterpretable

open unitInterval

inductive BernoulliOps
| Flip : I → BernoulliOps

@[expose]
def BernoulliPFunctor : PFunctor where
  A := BernoulliOps
  B _ := Bool

abbrev BernoulliM := PFunctor.FreeM BernoulliPFunctor

class BernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliPFunctor.FreeM (oSpec.toPFunctor.B op)

def flip (r : I) : BernoulliM Bool :=
  PFunctor.FreeM.liftBind (BernoulliOps.Flip r) PFunctor.FreeM.pure

def split' {n : ℕ} (m : Fin n) : BernoulliM (Fin n) := do
  if h₁ : n = m.1 + 1
    then pure m
    else
      let b ← flip
        ⟨
          (mkRat 1 (n - m.1) : ℝ),
          by
            simp only [Set.mem_Icc, Rat.cast_nonneg, zero_le_one, Rat.mkRat_nonneg, true_and]
            norm_cast
            refine Rat.num_le_denom_iff.mp ?_
            unfold mkRat
            split_ifs with h
            · simp
            · simp only [Rat.num_normalize, isUnit_one, Int.natAbs_of_isUnit, Fin.is_le',
              isUnit_iff_eq_one, IsUnit.dvd, Nat.gcd_sub_left_right_of_dvd, Nat.gcd_one_left,
              Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
              Rat.den_normalize, Nat.div_one, Nat.cast_sub]
              omega⟩
      if b
        then pure m
        else split' (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

def split (n : ℕ) : BernoulliM (Fin (n + 1)) :=
  split' (0 : Fin (n + 1))

instance : BernoulliInterpretable unifSpec where
  interp_op := split

open BernoulliInterpretable in
instance {α β} {oSpec₁ : OracleSpec α} {oSpec₂ : OracleSpec β} [BernoulliInterpretable oSpec₁]
    [BernoulliInterpretable oSpec₂]
  : BernoulliInterpretable (oSpec₁ + oSpec₂) where
  interp_op op := match op with
                    | .inl a => interp_op a
                    | .inr a => interp_op a

open BernoulliInterpretable in
def interp {α β} {oSpec : OracleSpec β} [BernoulliInterpretable oSpec] (p : OracleComp oSpec α)
      : PFunctor.FreeM (BernoulliPFunctor) α :=
  match p with
   | PFunctor.FreeM.pure a => pure a
   | PFunctor.FreeM.liftBind op f => bind (interp_op op) (fun x => interp (f x))

section BernoulliSpace

open MeasureTheory
open scoped ENNReal

end BernoulliSpace

/-- The `ℝ≥0` value of a point of the unit interval is at most `1`. -/
lemma toNNReal_le_one (r : I) : unitInterval.toNNReal r ≤ 1 :=
  NNReal.coe_le_coe.mp
    (show ((unitInterval.toNNReal r : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) by simpa using r.2.2)

/-- An unbiased coin. -/
def half : I := ⟨0.5, by simp; apply And.intro <;> linarith⟩

def consFlip (b : Bool) (ω : Ω) : Ω := fun n => if n = 0 then b else ω (n - 1)

@[simp]
lemma consFlip_zero (b : Bool) (ω : Ω) : consFlip b ω 0 = b := rfl

@[simp]
lemma consFlip_succ (b : Bool) (ω : Ω) (n : ℕ) : consFlip b ω (n + 1) = ω n := rfl

@[simp]
lemma shift_consCoin (b : Bool) (ω : Ω) : (fun n => consFlip b ω (n + 1)) = ω := rfl

noncomputable def interp_psp {α : Type} (m : BernoulliM α) : PSp Ω × RV α :=
  match m with
  | PFunctor.FreeM.pure a => (1, fun _ ↦ a)
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
    let (p₀, rv₀) := interp_psp (f false)
    let (p₁, rv₁) := interp_psp (f true)
    let rv' (ω : Ω) : α :=
      if ω 0
      then rv₁ (fun n ↦ ω (n + 1))
      else rv₀ (fun n ↦ ω (n + 1))
    ( PSp.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
        (PSp.map (consFlip false) p₀) (PSp.map (consFlip true) p₁)
    , rv' )

noncomputable def outputPSp {α : Type} (out : PSp Ω × RV α) : PSp α := PSp.map out.2 out.1

/-! ## The `PSpace`-level interpretation

`interp_psp` never produces `↯`, so its space can be given at the `PSpace` level
(`interpSpace`); the output of a program is then `outSpace`, and `outputPSp_eq` relates
the two levels. -/

/-- `interp_psp` never yields `↯`; this is the same space at the `PSpace` level. -/
noncomputable def interpSpace {α : Type} (m : BernoulliM α) : PSpace Ω :=
  match m with
  | PFunctor.FreeM.pure _ => 1
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
      PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
        (PSpace.map (consFlip false) (interpSpace (f false)))
        (PSpace.map (consFlip true) (interpSpace (f true)))

lemma interp_psp_fst {α : Type} (m : BernoulliM α) :
    (interp_psp m).1 = .some (interpSpace m) := by
  induction m with
  | pure a => rfl
  | liftBind op f ih =>
      cases op with
      | Flip r =>
          show PSp.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
                 (PSp.map (consFlip false) (interp_psp (f false)).1)
                 (PSp.map (consFlip true) (interp_psp (f true)).1)
             = .some (PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
                 (PSpace.map (consFlip false) (interpSpace (f false)))
                 (PSpace.map (consFlip true) (interpSpace (f true))))
          rw [ih false, ih true]
          rfl

/-- The output space of an interpreted program. -/
noncomputable def outSpace {α : Type} (m : BernoulliM α) : PSpace α :=
  PSpace.map (interp_psp m).2 (interpSpace m)

lemma outputPSp_eq {α : Type} (m : BernoulliM α) :
    outputPSp (interp_psp m) = .some (outSpace m) := by
  show PSp.map (interp_psp m).2 (interp_psp m).1 = _
  rw [interp_psp_fst]
  rfl

section Arithmetic

open scoped ENNReal NNReal

/-! ## Arithmetic

Everything here is bookkeeping in `ℝ≥0∞` with no probabilistic content, kept `private` so
it does not leak into the namespace. -/

private lemma halfNN_coe : (unitInterval.toNNReal half : ℝ≥0∞) = 2⁻¹ := by
  have h : unitInterval.toNNReal half = 2⁻¹ := by
    ext; rw [unitInterval.coe_toNNReal]; show (0.5 : ℝ) = _; norm_num
  rw [h]; simp

private lemma ennreal_one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by norm_num

private lemma ennreal_two_mul_inv_two : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- The mixing identity behind "`xor` of two fair bits is a fair bit". -/
private lemma mix_half (x y : ℝ≥0∞) :
    2⁻¹ * (2⁻¹ * x + 2⁻¹ * y) + 2⁻¹ * (2⁻¹ * y + 2⁻¹ * x) = 2⁻¹ * x + 2⁻¹ * y := by
  rw [add_comm (2⁻¹ * y) (2⁻¹ * x), ← two_mul, ← mul_assoc, ennreal_two_mul_inv_two, one_mul]

/-- Reassociating a product of two independent branch weights: this is why flips commute. -/
private lemma commute_mix (A A' B B' p00 p01 p10 p11 : ℝ≥0∞) :
    A' * (B' * p00 + B * p01) + A * (B' * p10 + B * p11)
      = B' * (A' * p00 + A * p10) + B * (A' * p01 + A * p11) := by ring

private lemma toNNReal_mkRat (K : ℕ) (hK : K ≠ 0)
    (h : (↑(mkRat 1 K) : ℝ) ∈ Set.Icc (0:ℝ) 1) :
    (unitInterval.toNNReal ⟨(↑(mkRat 1 K) : ℝ), h⟩ : ℝ≥0∞) = (K : ℝ≥0∞)⁻¹ := by
  have hq : (mkRat 1 K : ℚ) = 1 / (K : ℚ) := by
    rw [Rat.mkRat_eq_div]; norm_num
  have hr : ((mkRat 1 K : ℚ) : ℝ) = 1 / (K : ℝ) := by rw [hq]; push_cast; ring
  have hnn : unitInterval.toNNReal ⟨(↑(mkRat 1 K) : ℝ), h⟩ = (K : NNReal)⁻¹ := by
    ext
    rw [unitInterval.coe_toNNReal]
    show ((mkRat 1 K : ℚ) : ℝ) = _
    rw [hr]
    simp
  rw [hnn, ENNReal.coe_inv (by simpa using hK)]
  simp

/-- The rejection-sampling step: having failed with probability `1 - 1/K`, a uniform draw
from the remaining `K - 1` outcomes is again uniform over `K`. -/
private lemma mix_step (K : ℕ) (hK : 2 ≤ K) :
    (1 - (K : ℝ≥0∞)⁻¹) * ((K - 1 : ℕ) : ℝ≥0∞)⁻¹ = (K : ℝ≥0∞)⁻¹ := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hKt : (K : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.natCast_ne_top K
  have hcast : ((K - 1 : ℕ) : ℝ≥0∞) = (K : ℝ≥0∞) - 1 := by
    have : K - 1 + 1 = K := by omega
    rw [← this]
    push_cast
    rw [ENNReal.add_sub_cancel_right (by simp)]
  have hm0 : ((K : ℝ≥0∞) - 1) ≠ 0 := by
    rw [← hcast]
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hmt : ((K : ℝ≥0∞) - 1) ≠ (⊤ : ℝ≥0∞) := by
    rw [← hcast]; exact ENNReal.natCast_ne_top _
  have h1 : (1 : ℝ≥0∞) - (K : ℝ≥0∞)⁻¹ = ((K : ℝ≥0∞) - 1) * (K : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr hK0),
        ENNReal.mul_inv_cancel hK0 hKt, one_mul]
  rw [h1, hcast, mul_comm ((K : ℝ≥0∞) - 1) _, mul_assoc,
      ENNReal.mul_inv_cancel hm0 hmt, mul_one]

end Arithmetic

section Interpretation

open MeasureTheory
open scoped ENNReal NNReal Classical

/-! ## Evaluating an interpreted program

The two laws that matter are `outSpace_pure_apply` and `outSpace_liftBind_apply`: the
output of `pure a` is the point mass at `a`, and the output of a flip is the *mixture* of
the two branch outputs.  Together they let any program be evaluated by structural
recursion, and `outSpace_ms` says the result is always discrete. -/

variable {α : Type}

lemma interpSpace_liftBind (r : I) (f : Bool → BernoulliM α) :
    interpSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)
      = PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
          (PSpace.map (consFlip false) (interpSpace (f false)))
          (PSpace.map (consFlip true) (interpSpace (f true))) := rfl

lemma rv_liftBind (r : I) (f : Bool → BernoulliM α) :
    (interp_psp (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).2
      = fun ω : Ω => if ω 0 = true then (interp_psp (f true)).2 (fun n => ω (n + 1))
                     else (interp_psp (f false)).2 (fun n => ω (n + 1)) := rfl

/-- Prepending the bit `c` makes the outer random variable agree with branch `c`'s. -/
lemma preimage_consFlip_rv (r : I) (f : Bool → BernoulliM α)
    (c : Bool) (S : Set α) :
    consFlip c ⁻¹' ((interp_psp (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).2 ⁻¹' S)
      = (interp_psp (f c)).2 ⁻¹' S := by
  ext ω; cases c <;> simp [Set.mem_preimage, rv_liftBind]

/-! ### `pure` -/

lemma outSpace_pure (a : α) : outSpace (PFunctor.FreeM.pure a) = PSpace.map (fun _ : Ω => a) 1 :=
  rfl

@[simp] lemma outSpace_pure_ms (a : α) :
    (outSpace (PFunctor.FreeM.pure a)).ms = (⊤ : MeasurableSpace α) :=
  MeasurableSpace.map_const a

lemma measurableSet_outSpace_pure (a : α) (S : Set α) :
    MeasurableSet[(outSpace (PFunctor.FreeM.pure a)).ms] S := by
  rw [outSpace_pure_ms]; trivial

lemma outSpace_pure_apply (a : α) (S : Set α) :
    (outSpace (PFunctor.FreeM.pure a)).μ S = if a ∈ S then 1 else 0 := by
  rw [outSpace, PSpace.map_apply _ _ (measurableSet_outSpace_pure a S)]
  show (1 : PSpace Ω).μ ((fun _ : Ω => a) ⁻¹' S) = _
  by_cases h : a ∈ S
  · have he : (fun _ : Ω => a) ⁻¹' S = Set.univ := by ext ω; simp [h]
    rw [he]; simp [h]
  · have he : (fun _ : Ω => a) ⁻¹' S = ∅ := by ext ω; simp [h]
    rw [he]; simp [h]

/-! ### `flip` -/

lemma measurableSet_outSpace_liftBind (r : I) (f : Bool → BernoulliM α)
    {S : Set α}
    (h₀ : MeasurableSet[(outSpace (f false)).ms] S)
    (h₁ : MeasurableSet[(outSpace (f true)).ms] S) :
    MeasurableSet[(outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).ms] S := by
  rw [outSpace, PSpace.measurableSet_map, interpSpace_liftBind]
  refine PSpace.measurableSet_wsum₂ ?_ ?_ <;>
    rw [PSpace.measurableSet_map, preimage_consFlip_rv]
  · exact h₀
  · exact h₁

/-- The output measure of a flip is the mixture of the branch output measures. -/
lemma outSpace_liftBind_apply (r : I) (f : Bool → BernoulliM α)
    {S : Set α}
    (h₀ : MeasurableSet[(outSpace (f false)).ms] S)
    (h₁ : MeasurableSet[(outSpace (f true)).ms] S) :
    (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).μ S
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞)) * (outSpace (f false)).μ S
        + (unitInterval.toNNReal r : ℝ≥0∞) * (outSpace (f true)).μ S := by
  rw [outSpace, PSpace.map_apply _ _ (by
        rw [← outSpace]; exact measurableSet_outSpace_liftBind r f h₀ h₁),
      interpSpace_liftBind,
      PSpace.wsum₂_map_apply _ _ (consFlip false) (consFlip true) _ _
        (by rw [← interpSpace_liftBind, ← PSpace.measurableSet_map, ← outSpace]
            exact measurableSet_outSpace_liftBind r f h₀ h₁),
      preimage_consFlip_rv, preimage_consFlip_rv,
      ← PSpace.map_apply _ _ h₀, ← PSpace.map_apply _ _ h₁]
  rfl

/-- The output space of *any* interpreted program is discrete: a program only ever
produces finitely many values, through finitely many coin flips. -/
lemma outSpace_ms (m : BernoulliM α) :
    (outSpace m).ms = (⊤ : MeasurableSpace α) := by
  induction m with
  | pure a => exact outSpace_pure_ms a
  | liftBind op f ih =>
      cases op with
      | Flip r =>
          show (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).ms = _
          refine PSpace.ms_eq_top_of_all (fun S =>
            measurableSet_outSpace_liftBind r f ?_ ?_)
          · rw [ih false]; trivial
          · rw [ih true]; trivial

lemma measurableSet_outSpace (m : BernoulliM α) (S : Set α) :
    MeasurableSet[(outSpace m).ms] S := by rw [outSpace_ms]; trivial

/-- `outSpace_liftBind_apply` with its side conditions discharged by `outSpace_ms`.  This
is the workhorse: it evaluates a program one flip at a time. -/
lemma outSpace_liftBind_μ (r : I) (f : Bool → BernoulliM α)
    (S : Set α) :
    (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).μ S
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞)) * (outSpace (f false)).μ S
        + (unitInterval.toNNReal r : ℝ≥0∞) * (outSpace (f true)).μ S :=
  outSpace_liftBind_apply r f (measurableSet_outSpace _ S) (measurableSet_outSpace _ S)

end Interpretation


section Example

open MeasureTheory
open scoped ENNReal NNReal Classical

def xorTest : BernoulliM Bool := do
  let b₀ ← flip half
  let b₁ ← flip half
  pure (Bool.xor b₀ b₁)

def flipTest1 (a b : I) : BernoulliM (Bool × Bool) := do
  let o₀ ← flip a
  let o₁ ← flip b
  pure (o₀, o₁)

def flipTest2 (a b : I) : BernoulliM (Bool × Bool) := do
  let o₁ ← flip b
  let o₀ ← flip a
  pure (o₀, o₁)

section Flip

/-- A single flip is the Bernoulli distribution with that bias. -/
lemma flip_distr' {p : I} : outSpace (flip p) = PSpace.bernoulli p := by
  refine PSpace.eq_of_singletons (outSpace_ms _) (PSpace.bernoulli_ms _) (fun b => ?_)
  rw [show flip p = PFunctor.FreeM.liftBind (BernoulliOps.Flip p)
        (PFunctor.FreeM.pure : Bool → BernoulliM Bool) from rfl]
  simp only [outSpace_liftBind_μ, outSpace_pure_apply]
  cases b
  · rw [PSpace.bernoulli_μ_false]; simp
  · rw [PSpace.bernoulli_μ_true]; simp

lemma flip_dist {p : I} : outputPSp (interp_psp (flip p)) = PSp.bernoulli p := by
  rw [outputPSp_eq, flip_distr']; rfl

end Flip

section XorTest

-- combine (xor) unbiased coinflips

/-- The `xor` of two independent fair flips is a fair flip. -/
lemma xorTest_distr' : outSpace xorTest = PSpace.bernoulli half := by
  refine PSpace.eq_of_singletons (outSpace_ms _) (PSpace.bernoulli_ms _) (fun b => ?_)
  rw [show xorTest = PFunctor.FreeM.liftBind (BernoulliOps.Flip half)
        (fun b₀ : Bool => PFunctor.FreeM.liftBind (BernoulliOps.Flip half)
          (fun b₁ : Bool => PFunctor.FreeM.pure (Bool.xor b₀ b₁))) from rfl]
  simp only [outSpace_liftBind_μ, outSpace_pure_apply, halfNN_coe, ennreal_one_sub_inv_two]
  cases b
  · rw [PSpace.bernoulli_μ_false, halfNN_coe, ennreal_one_sub_inv_two]
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Set.mem_singleton_iff, Bool.true_eq_false, if_false, if_true]
    exact (mix_half 1 0).trans (by simp)
  · rw [PSpace.bernoulli_μ_true, halfNN_coe]
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Set.mem_singleton_iff, Bool.false_eq_true, if_false, if_true]
    exact (mix_half 0 1).trans (by simp)

lemma xorTest_distr : outputPSp (interp_psp xorTest) = PSp.bernoulli half := by
  rw [outputPSp_eq, xorTest_distr']; rfl

/-- `xorTest` is therefore indistinguishable from a single fair flip. -/
lemma xorTest_eq_flip : outputPSp (interp_psp xorTest) = outputPSp (interp_psp (flip half)) := by
  rw [xorTest_distr, flip_dist]

end XorTest

section FlipCommuteTest

-- flips commute

/-- Two independent flips commute: the joint distribution does not depend on the order. -/
lemma flip_comm_distr' (a b : I) : outSpace (flipTest1 a b) = outSpace (flipTest2 a b) := by
  refine PSpace.eq_of_singletons (outSpace_ms _) (outSpace_ms _) (fun s => ?_)
  rw [show flipTest1 a b = PFunctor.FreeM.liftBind (BernoulliOps.Flip a)
        (fun o₀ : Bool => PFunctor.FreeM.liftBind (BernoulliOps.Flip b)
          (fun o₁ : Bool => PFunctor.FreeM.pure (o₀, o₁))) from rfl,
      show flipTest2 a b = PFunctor.FreeM.liftBind (BernoulliOps.Flip b)
        (fun o₁ : Bool => PFunctor.FreeM.liftBind (BernoulliOps.Flip a)
          (fun o₀ : Bool => PFunctor.FreeM.pure (o₀, o₁))) from rfl]
  simp only [outSpace_liftBind_μ, outSpace_pure_apply]
  exact commute_mix _ _ _ _ _ _ _ _

lemma flip_comm_distr (a b : I) :
    outputPSp (interp_psp (flipTest1 a b)) = outputPSp (interp_psp (flipTest2 a b)) := by
  rw [outputPSp_eq, outputPSp_eq, flip_comm_distr']

end FlipCommuteTest

section SplitExample

/-- One rejection-sampling step: if the continuation is uniform on `{i | m' ≤ i}` and the
coin lands `true` with probability `1/K`, the whole thing is uniform on `{i | m ≤ i}`. -/
lemma split'_step {n : ℕ} (m m' : Fin n) (r : I) (K : ℕ)
    (f : Bool → BernoulliM (Fin n))
    (hf0 : f false = split' m') (hf1 : f true = PFunctor.FreeM.pure m)
    (hK : K = n - m.1) (hK2 : 2 ≤ K) (hm' : m'.1 = m.1 + 1)
    (hr : (unitInterval.toNNReal r : ℝ≥0∞) = (K : ℝ≥0∞)⁻¹)
    (ihms : (outSpace (split' m')).ms = (⊤ : MeasurableSpace (Fin n)))
    (ihμ : ∀ i : Fin n, (outSpace (split' m')).μ {i}
             = if m'.1 ≤ i.1 then ((n - m'.1 : ℕ) : ℝ≥0∞)⁻¹ else 0) :
    (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).ms
      = (⊤ : MeasurableSpace (Fin n))
    ∧ ∀ i : Fin n, (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).μ {i}
        = if m.1 ≤ i.1 then (K : ℝ≥0∞)⁻¹ else 0 := by
  have hmeas0 : ∀ S : Set (Fin n), MeasurableSet[(outSpace (f false)).ms] S := by
    intro S; rw [hf0, ihms]; trivial
  have hmeas1 : ∀ S : Set (Fin n), MeasurableSet[(outSpace (f true)).ms] S := by
    intro S; rw [hf1]; exact measurableSet_outSpace_pure m S
  refine ⟨PSpace.ms_eq_top_of_all (fun S => measurableSet_outSpace_liftBind r f (hmeas0 S) (hmeas1 S)),
          fun i => ?_⟩
  rw [outSpace_liftBind_apply r f (hmeas0 {i}) (hmeas1 {i}), hr, hf0, hf1,
      ihμ i, outSpace_pure_apply]
  have hnm' : n - m'.1 = K - 1 := by omega
  rw [hnm']
  by_cases hmi : m.1 ≤ i.1
  · by_cases hlt : m.1 < i.1
    · have h1 : m'.1 ≤ i.1 := by omega
      have h2 : m ∉ ({i} : Set (Fin n)) := by
        simp only [Set.mem_singleton_iff]; intro hh; omega
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left hmi, mul_zero, add_zero]
      exact mix_step K hK2
    · have hieq : i = m := Fin.ext (by omega)
      have h1 : ¬ (m'.1 ≤ i.1) := by omega
      have h2 : m ∈ ({i} : Set (Fin n)) := by simp [hieq]
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left hmi, mul_zero, zero_add, mul_one]
  · have h1 : ¬ (m'.1 ≤ i.1) := by omega
    have h2 : m ∉ ({i} : Set (Fin n)) := by
      simp only [Set.mem_singleton_iff]; intro hh; omega
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hmi, mul_zero, mul_zero, add_zero]

/-- `split' m` is uniform on the suffix `{i | m ≤ i}` of `Fin n`. -/
lemma split'_spec {n : ℕ} (m : Fin n) :
    (outSpace (split' m)).ms = (⊤ : MeasurableSpace (Fin n))
    ∧ ∀ i : Fin n, (outSpace (split' m)).μ {i}
        = if m.1 ≤ i.1 then ((n - m.1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  have hmn : m.1 < n := m.isLt
  by_cases hlast : n = m.1 + 1
  · rw [split'.eq_def, dite_eq_left hlast, ← PFunctor.FreeM.pure_eq_pure]
    refine ⟨outSpace_pure_ms m, fun i => ?_⟩
    rw [outSpace_pure_apply]
    have hK : n - m.1 = 1 := by omega
    rw [hK]
    by_cases hi : m.1 ≤ i.1
    · have hieq : i = m := Fin.ext (by omega)
      rw [ite_eq_left hi]; simp [hieq]
    · rw [ite_eq_right hi]
      have hns : m ∉ ({i} : Set (Fin n)) := by
        simp only [Set.mem_singleton_iff]; intro hh; omega
      simp [hns]
  · rw [split'.eq_def, dite_eq_right hlast]
    have hstep := split'_spec (⟨m.1 + 1, by omega⟩ : Fin n)
    refine split'_step m ⟨m.1 + 1, by omega⟩ _ (n - m.1)
      (fun b => if b = true then PFunctor.FreeM.pure m else split' ⟨m.1 + 1, by omega⟩)
      rfl rfl rfl (by omega) rfl ?_ hstep.1 hstep.2
    exact toNNReal_mkRat (n - m.1) (by omega) _
termination_by n - m.1
decreasing_by have := m.isLt; omega

/-- `split` is a uniform draw from `Fin (n + 1)`. -/
lemma split_distr' {n : ℕ} : outSpace (split n) = PSpace.uniform n := by
  refine PSpace.eq_uniform (outSpace_ms _) (fun i => ?_)
  have h := (split'_spec (0 : Fin (n + 1))).2 i
  rw [show split n = split' (0 : Fin (n + 1)) from rfl, h]
  simp

lemma split_distr {n : ℕ} : outputPSp (interp_psp (split n)) = PSp.uniform n := by
  rw [outputPSp_eq, split_distr']; rfl

end SplitExample

end Example

end BernoulliInterpretable

end Amaryllis
