module

import Mathlib.Data.Real.Basic

import Iris

namespace Model

def todo (note : String) : Prop := sorry

-- _𝒫_ = Probability Space
-- Ω = outcome space
-- ℱ = set of all events (aka subsets of Ω whose probabilities can be measured)
-- μ, the distribution μ gives a probability to every event in ℱ
structure _𝒫_ where
  Ω : Type*
  ℱ : Set (Set Ω)
  -- aka:
  -- ℱ : (Ω → Prop /- This `Prop` means "is in this subset of Ω" -/)
  --           → Prop /- This `Prop` means "is measurable" -/
  hℱ₁ : ℱ (λ _outcome ↦ True) -- The σ-algebra contains Ω
  hℱ₂ : todo "ℱ is closed under countable unions, intersections and complements"
  μ : (Set Ω) → Option (Set.Icc (0 : ℝ) 1) -- μ might assign a probability to a subset of Ω
  hμ₁ : ∀ potentialEvent : (Set Ω),
          ℱ potentialEvent ↔ (μ potentialEvent).isSome
            -- a subset of Ω is measurable ⇔ μ assigns a probability to it
  hμ₂ : todo "μ is countably additive"
