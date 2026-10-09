
-- import VCVio.Prelude.Core
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.GiryMonad

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

class BernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliPFunctor.FreeM (oSpec.toPFunctor.B op)

def flip (r : I) : PFunctor.FreeM BernoulliPFunctor Bool :=
  PFunctor.FreeM.liftBind (BernoulliOps.Flip r) PFunctor.FreeM.pure

def split {n : ℕ} (m : Fin n) : PFunctor.FreeM BernoulliPFunctor (Fin n) := do
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
        else split (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

instance : BernoulliInterpretable unifSpec where
  interp_op op := split (0 : (Fin (op + 1)))

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

lemma toNNReal_le_one (r : I) : unitInterval.toNNReal r ≤ 1 :=
  NNReal.coe_le_coe.mp
    (show ((unitInterval.toNNReal r : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) by simpa using r.2.2)

def consFlip (b : Bool) (ω : Ω) : Ω := fun n => if n = 0 then b else ω (n - 1)

@[simp]
lemma consFlip_zero (b : Bool) (ω : Ω) : consFlip b ω 0 = b := rfl

@[simp]
lemma consFlip_succ (b : Bool) (ω : Ω) (n : ℕ) : consFlip b ω (n + 1) = ω n := rfl

@[simp]
lemma shift_consCoin (b : Bool) (ω : Ω) : (fun n => consFlip b ω (n + 1)) = ω := rfl

noncomputable def interp_psp {α : Type} (m : PFunctor.FreeM BernoulliPFunctor α) : PSp Ω × RV α :=
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

section Example

-- combine (xor) unbiased coinflips

def half : I := ⟨0.5, by simp; apply And.intro <;> linarith⟩

def xorTest : PFunctor.FreeM BernoulliPFunctor Bool := do
  let b₀ ← flip half
  let b₁ ← flip half
  pure (Bool.xor b₀ b₁)

section Reasoning

open MeasureTheory
open scoped ENNReal NNReal Classical

/-! ## Computing the output of an interpreted program

`interp_psp` reduces definitionally, so for a one- or two-flip program both the space and
the random variable are available by `rfl` (see `out_flip`, `out_xor`, `out_test1`,
`out_test2` below).  The lemmas in this section compute the σ-algebra and the measure of
such a space, after which each example is arithmetic in `ℝ≥0∞`.

The driving observation is that prepending a bit with `consFlip` turns a *two-coin*
random variable `fun ω => k (ω 0) (ω 1)` into a *first-coin* one `fun ω => k c (ω 0)`, and
a first-coin variable into a constant.  So every preimage that shows up is either `univ`
or `∅` at the bottom, and the weighted sums unfold into products of branch weights. -/

variable {β : Type}

/-- The space of a single flip with bias `r`: `(interp_psp (flip r)).1 = .some (flipSpace r)`. -/
noncomputable def flipSpace (r : I) : PSpace Ω :=
  PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
    (PSpace.map (consFlip false) 1) (PSpace.map (consFlip true) 1)

/-- The space of a flip with bias `r` followed by a program with space `q`, with `q`
reindexed onto the identifiers the continuation owns. -/
noncomputable def consSpace (r : I) (q : PSpace Ω) : PSpace Ω :=
  PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
    (PSpace.map (consFlip false) q) (PSpace.map (consFlip true) q)

lemma one_ms : (1 : PSpace Ω).ms = ⊥ := rfl

@[simp] lemma one_measure_univ : (1 : PSpace Ω).μ Set.univ = 1 := (1 : PSpace Ω).2.measure_univ

@[simp] lemma one_measure_empty : (1 : PSpace Ω).μ (∅ : Set Ω) = 0 := measure_empty

/-! ### First-coin random variables -/

lemma preimage_consFlip_firstCoin (c : Bool) (k : Bool → β) (S : Set β) :
    consFlip c ⁻¹' ((fun ω : Ω => k (ω 0)) ⁻¹' S) = if k c ∈ S then Set.univ else ∅ := by
  ext ω; by_cases hk : k c ∈ S <;> simp [hk]

lemma measurableSet_flipSpace_firstCoin (r : I) (k : Bool → β) (S : Set β) :
    MeasurableSet[(flipSpace r).ms] ((fun ω : Ω => k (ω 0)) ⁻¹' S) := by
  refine PSpace.measurableSet_wsum₂ ?_ ?_ <;>
  · rw [PSpace.measurableSet_map, preimage_consFlip_firstCoin, one_ms]
    split <;> simp

/-- A single flip weights the two outcomes of a first-coin variable by `1 - r` and `r`. -/
lemma flipSpace_apply_firstCoin (r : I) (k : Bool → β) (S : Set β) :
    (flipSpace r).μ ((fun ω : Ω => k (ω 0)) ⁻¹' S)
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞)) * (if k false ∈ S then 1 else 0)
        + (unitInterval.toNNReal r : ℝ≥0∞) * (if k true ∈ S then 1 else 0) := by
  rw [flipSpace, PSpace.wsum₂_map_apply _ _ (consFlip false) (consFlip true) 1 1
        (measurableSet_flipSpace_firstCoin r k S),
      preimage_consFlip_firstCoin, preimage_consFlip_firstCoin]
  split <;> split <;> simp

/-! ### Two-coin random variables -/

lemma preimage_consFlip_twoCoin (c : Bool) (k : Bool → Bool → β) (S : Set β) :
    consFlip c ⁻¹' ((fun ω : Ω => k (ω 0) (ω 1)) ⁻¹' S) = (fun ω : Ω => k c (ω 0)) ⁻¹' S := by
  ext ω; simp [consFlip]

lemma measurableSet_consSpace_twoCoin (r s : I) (k : Bool → Bool → β) (S : Set β) :
    MeasurableSet[(consSpace r (flipSpace s)).ms] ((fun ω : Ω => k (ω 0) (ω 1)) ⁻¹' S) := by
  refine PSpace.measurableSet_wsum₂ ?_ ?_ <;>
  · rw [PSpace.measurableSet_map, preimage_consFlip_twoCoin]
    exact measurableSet_flipSpace_firstCoin s _ S

/-- Two successive flips weight the four outcomes of a two-coin variable by the products
of the branch weights. -/
lemma consSpace_apply_twoCoin (r s : I) (k : Bool → Bool → β) (S : Set β) :
    (consSpace r (flipSpace s)).μ ((fun ω : Ω => k (ω 0) (ω 1)) ⁻¹' S)
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞))
          * ((1 - (unitInterval.toNNReal s : ℝ≥0∞)) * (if k false false ∈ S then 1 else 0)
             + (unitInterval.toNNReal s : ℝ≥0∞) * (if k false true ∈ S then 1 else 0))
        + (unitInterval.toNNReal r : ℝ≥0∞)
          * ((1 - (unitInterval.toNNReal s : ℝ≥0∞)) * (if k true false ∈ S then 1 else 0)
             + (unitInterval.toNNReal s : ℝ≥0∞) * (if k true true ∈ S then 1 else 0)) := by
  rw [consSpace, PSpace.wsum₂_map_apply _ _ (consFlip false) (consFlip true) _ _
        (measurableSet_consSpace_twoCoin r s k S),
      preimage_consFlip_twoCoin, preimage_consFlip_twoCoin,
      flipSpace_apply_firstCoin, flipSpace_apply_firstCoin]

/-! ### Arithmetic -/

lemma halfNN_coe : (unitInterval.toNNReal half : ℝ≥0∞) = 2⁻¹ := by
  have h : unitInterval.toNNReal half = 2⁻¹ := by
    ext; rw [unitInterval.coe_toNNReal]; show (0.5 : ℝ) = _; norm_num
  rw [h]; simp

lemma ennreal_one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by norm_num

lemma ennreal_two_mul_inv_two : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- The mixing identity behind "`xor` of two fair bits is a fair bit". -/
lemma mix_half (x y : ℝ≥0∞) :
    2⁻¹ * (2⁻¹ * x + 2⁻¹ * y) + 2⁻¹ * (2⁻¹ * y + 2⁻¹ * x) = 2⁻¹ * x + 2⁻¹ * y := by
  rw [add_comm (2⁻¹ * y) (2⁻¹ * x), ← two_mul, ← mul_assoc, ennreal_two_mul_inv_two, one_mul]

/-- Reassociating a product of two independent branch weights: this is why flips commute. -/
lemma commute_mix (A A' B B' p00 p01 p10 p11 : ℝ≥0∞) :
    A' * (B' * p00 + B * p01) + A * (B' * p10 + B * p11)
      = B' * (A' * p00 + A * p10) + B * (A' * p01 + A * p11) := by ring

/-! ### `xor` of two fair flips is a fair flip -/

lemma rv_flip_eq : (fun ω : Ω => if ω 0 = true then true else false) = (fun ω : Ω => ω 0) := by
  funext ω; cases h : ω 0 <;> simp

lemma rv_xor_eq : (fun ω : Ω => if ω 0 = true then (if ω 1 = true then false else true)
                                else (if ω 1 = true then true else false))
               = (fun ω : Ω => Bool.xor (ω 0) (ω 1)) := by
  funext ω; cases h0 : ω 0 <;> cases h1 : ω 1 <;> simp

lemma out_flip : outputPSp (interp_psp (flip half))
    = .some (PSpace.map (fun ω : Ω => ω 0) (flipSpace half)) := by
  have h : outputPSp (interp_psp (flip half))
      = .some (PSpace.map (fun ω : Ω => if ω 0 = true then true else false)
          (flipSpace half)) := rfl
  rw [h, rv_flip_eq]

lemma out_xor : outputPSp (interp_psp xorTest)
    = .some (PSpace.map (fun ω : Ω => Bool.xor (ω 0) (ω 1))
        (consSpace half (flipSpace half))) := by
  have h : outputPSp (interp_psp xorTest)
      = .some (PSpace.map (fun ω : Ω => if ω 0 = true then (if ω 1 = true then false else true)
                                        else (if ω 1 = true then true else false))
          (consSpace half (flipSpace half))) := rfl
  rw [h, rv_xor_eq]

example : outputPSp (interp_psp xorTest) = outputPSp (interp_psp (flip half)) := by
  rw [out_xor, out_flip]
  congr 1
  refine PSpace.ext_ms ?_ ?_
  · -- both output σ-algebras are discrete on `Bool`
    show (PSpace.map (fun ω : Ω => Bool.xor (ω 0) (ω 1)) (consSpace half (flipSpace half))).ms
       = (PSpace.map (fun ω : Ω => ω 0) (flipSpace half)).ms
    rw [show (PSpace.map (fun ω : Ω => Bool.xor (ω 0) (ω 1))
               (consSpace half (flipSpace half))).ms = (⊤ : MeasurableSpace Bool) from
          PSpace.map_ms_eq_top
            (fun S => measurableSet_consSpace_twoCoin half half (fun c d => Bool.xor c d) S),
        show (PSpace.map (fun ω : Ω => ω 0) (flipSpace half)).ms
               = (⊤ : MeasurableSpace Bool) from
          PSpace.map_ms_eq_top
            (fun S => measurableSet_flipSpace_firstCoin half (fun b => b) S)]
  · -- and both output measures are uniform
    intro E hE
    show (PSpace.map (fun ω : Ω => Bool.xor (ω 0) (ω 1)) (consSpace half (flipSpace half))).μ E
       = (PSpace.map (fun ω : Ω => ω 0) (flipSpace half)).μ E
    rw [PSpace.map_apply _ _ hE,
        consSpace_apply_twoCoin half half (fun c d => Bool.xor c d) E,
        PSpace.map_apply _ _ (measurableSet_flipSpace_firstCoin half (fun b => b) E),
        flipSpace_apply_firstCoin half (fun b => b) E,
        halfNN_coe, ennreal_one_sub_inv_two]
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true]
    exact mix_half _ _

end Reasoning

section FlipCommuteTest
-- flips commute

def flipTest1 (a b : I) : PFunctor.FreeM BernoulliPFunctor (Bool × Bool) := do
  let o₀ ← flip a
  let o₁ ← flip b
  pure (o₀, o₁)

def flipTest2 (a b : I) : PFunctor.FreeM BernoulliPFunctor (Bool × Bool) := do
  let o₁ ← flip b
  let o₀ ← flip a
  pure (o₀, o₁)

section Reasoning

open MeasureTheory
open scoped ENNReal NNReal Classical

lemma rv_test1_eq :
    (fun ω : Ω => if ω 0 = true then (if ω 1 = true then (true, true) else (true, false))
                  else (if ω 1 = true then (false, true) else (false, false)))
  = (fun ω : Ω => ((ω 0), (ω 1))) := by
  funext ω; cases h0 : ω 0 <;> cases h1 : ω 1 <;> simp

lemma rv_test2_eq :
    (fun ω : Ω => if ω 0 = true then (if ω 1 = true then (true, true) else (false, true))
                  else (if ω 1 = true then (true, false) else (false, false)))
  = (fun ω : Ω => ((ω 1), (ω 0))) := by
  funext ω; cases h0 : ω 0 <;> cases h1 : ω 1 <;> simp

lemma out_test1 (a b : I) : outputPSp (interp_psp (flipTest1 a b))
    = .some (PSpace.map (fun ω : Ω => ((ω 0), (ω 1))) (consSpace a (flipSpace b))) := by
  have h : outputPSp (interp_psp (flipTest1 a b))
      = .some (PSpace.map
          (fun ω : Ω => if ω 0 = true then (if ω 1 = true then (true, true) else (true, false))
                        else (if ω 1 = true then (false, true) else (false, false)))
          (consSpace a (flipSpace b))) := rfl
  rw [h, rv_test1_eq]

lemma out_test2 (a b : I) : outputPSp (interp_psp (flipTest2 a b))
    = .some (PSpace.map (fun ω : Ω => ((ω 1), (ω 0))) (consSpace b (flipSpace a))) := by
  have h : outputPSp (interp_psp (flipTest2 a b))
      = .some (PSpace.map
          (fun ω : Ω => if ω 0 = true then (if ω 1 = true then (true, true) else (false, true))
                        else (if ω 1 = true then (true, false) else (false, false)))
          (consSpace b (flipSpace a))) := rfl
  rw [h, rv_test2_eq]

example : ∀ a b : I, outputPSp (interp_psp (flipTest1 a b))
    = outputPSp (interp_psp (flipTest2 a b)) := by
  intro a b
  rw [out_test1, out_test2]
  congr 1
  refine PSpace.ext_ms ?_ ?_
  · -- both output σ-algebras are discrete on `Bool × Bool`
    show (PSpace.map (fun ω : Ω => ((ω 0), (ω 1))) (consSpace a (flipSpace b))).ms
       = (PSpace.map (fun ω : Ω => ((ω 1), (ω 0))) (consSpace b (flipSpace a))).ms
    rw [show (PSpace.map (fun ω : Ω => ((ω 0), (ω 1))) (consSpace a (flipSpace b))).ms
           = (⊤ : MeasurableSpace (Bool × Bool)) from
         PSpace.map_ms_eq_top
           (fun S => measurableSet_consSpace_twoCoin a b (fun c d => (c, d)) S),
       show (PSpace.map (fun ω : Ω => ((ω 1), (ω 0))) (consSpace b (flipSpace a))).ms
           = (⊤ : MeasurableSpace (Bool × Bool)) from
         PSpace.map_ms_eq_top
           (fun S => measurableSet_consSpace_twoCoin b a (fun c d => (d, c)) S)]
  · -- and both output measures assign the same product weights
    intro E hE
    show (PSpace.map (fun ω : Ω => ((ω 0), (ω 1))) (consSpace a (flipSpace b))).μ E
       = (PSpace.map (fun ω : Ω => ((ω 1), (ω 0))) (consSpace b (flipSpace a))).μ E
    calc (PSpace.map (fun ω : Ω => ((ω 0), (ω 1))) (consSpace a (flipSpace b))).μ E
        = (consSpace a (flipSpace b)).μ ((fun ω : Ω => ((ω 0), (ω 1))) ⁻¹' E) :=
          PSpace.map_apply _ _ hE
      _ = _ := consSpace_apply_twoCoin a b (fun c d => (c, d)) E
      _ = _ := commute_mix _ _ _ _ _ _ _ _
      _ = (consSpace b (flipSpace a)).μ ((fun ω : Ω => ((ω 1), (ω 0))) ⁻¹' E) :=
          (consSpace_apply_twoCoin b a (fun c d => (d, c)) E).symm
      _ = (PSpace.map (fun ω : Ω => ((ω 1), (ω 0))) (consSpace b (flipSpace a))).μ E :=
          (PSpace.map_apply _ _
            (measurableSet_consSpace_twoCoin b a (fun c d => (d, c)) E)).symm

end Reasoning

end FlipCommuteTest

end Example

end BernoulliInterpretable

end Amaryllis
