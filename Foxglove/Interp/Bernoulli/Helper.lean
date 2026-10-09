module

public import Foxglove.Interp.Bernoulli.Basic


@[expose] public section
namespace Foxglove

namespace Interp

namespace Helper

open unitInterval
open scoped ENNReal NNReal

/-! ## Arithmetic helpers

Everything here is bookkeeping in `ℝ≥0∞` with no probabilistic content.  It lives in its own
`Helper` namespace so that it does not leak into `Foxglove.Interp`; `open Helper` to use it. -/

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

lemma toNNReal_mkRat (K : ℕ) (hK : K ≠ 0)
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
lemma mix_step (K : ℕ) (hK : 2 ≤ K) :
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

end Helper

end Interp

end Foxglove
