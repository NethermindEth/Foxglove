module

public import Foxglove.Interp.Bernoulli.Helper


@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace

open unitInterval
open Helper

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
      Set.mem_singleton_iff, Bool.true_eq_false, ite_false, ite_true]
    exact (mix_half 1 0).trans (by simp)
  · rw [PSpace.bernoulli_μ_true, halfNN_coe]
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Set.mem_singleton_iff, Bool.false_eq_true, ite_false, ite_true]
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

end Interp

end Foxglove
