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

lemma flip_dist {p : I} : outputPSp (interp_psp (flip p)) = PSp.bernoulli p := by
  sorry

end Flip

section XorTest

lemma xorTest_distr : outputPSp (interp_psp xorTest) = PSp.bernoulli half := by
  sorry

/-- `xorTest` is therefore indistinguishable from a single fair flip. -/
lemma xorTest_eq_flip : outputPSp (interp_psp xorTest) = outputPSp (interp_psp (flip half)) := by
  rw [xorTest_distr, flip_dist]

end XorTest

section FlipCommuteTest

-- flips commute

lemma flip_comm_distr (a b : I) :
    outputPSp (interp_psp (flipTest1 a b)) = outputPSp (interp_psp (flipTest2 a b)) := by
  sorry

end FlipCommuteTest

section SplitExample

lemma split_distr {n : ℕ} : outputPSp (interp_psp (split n)) = PSp.uniform n := by
  sorry

end SplitExample

end Example

end Interp

end Foxglove
