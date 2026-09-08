module

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

import Iris

namespace Model

-- _𝒫_ = Probability Space
-- Ω = outcome space
-- ℱ = set of all events (aka subsets of Ω whose probabilities can be measured)
-- μ, the distribution μ gives a probability to every event in ℱ
structure _𝒫_ where
  Ω : Type*
  -- ℱ : (Ω → Prop /- This `Prop` means "is in this subset of Ω" -/)
  --           → Prop /- This `Prop` means "is measurable" -/
  ℱ : Set (Set Ω)
  -- The σ-algebra contains Ω
  hℱ₁ : ℱ (λ _outcome ↦ True)
  -- ℱ is closed under countable unions
  hℱ₂ : ∀ {f₁ f₂}, f₁.Countable → f₂.Countable → ℱ f₁ → ℱ f₂ → ℱ (f₁ ∪ f₂)
   -- ℱ is closed under intersections
  hℱ₃ : ∀ {f₁ f₂}, ℱ f₁ → ℱ f₂ → ℱ (f₁ ∩ f₂)
  -- ℱ is closed under complements
  hℱ₄ : ∀ {f}, (hf : ℱ f) → ℱ fᶜ
  -- μ assigns a probability to each measurable subset of Ω
  μ : (f : Set Ω) → ℱ f → (Set.Icc (0 : ℝ) 1)
  -- μ(Ω) = 1
  hμ₁ : μ (λ _outcome ↦ True) hℱ₁ = ⟨(1 : ℝ), (by simp)⟩
  -- μ is countably additive (i.e. the probability of a countable union of pairwise dijoint events is the sum of the events' probabilities)
  hμ₂ : ∀ f₁ f₂ (hC₁ : f₁.Countable) (hC₂ : f₂.Countable) (hf₁ : ℱ f₁) (hf₂ : ℱ f₂),
          f₁ ∩ f₂ = ∅ → (μ (f₁ ∪ f₂) (hℱ₂ hC₁ hC₂ hf₁ hf₂)).1 = (μ f₁ hf₁).1 + (μ f₂ hf₂).1

