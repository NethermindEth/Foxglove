
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
    ( PSp.wsum₂ (unitInterval.toNNReal r)
        (NNReal.coe_le_coe.mp
          (show ((unitInterval.toNNReal r : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) by
            simpa using r.2.2))
        (PSp.map (consFlip false) p₀) (PSp.map (consFlip true) p₁)
    , rv' )


-- Example:
-- combine (xor) Bernoulli samples
-- flips commute
-- prove spec for flip

end BernoulliInterpretable

end Amaryllis
