import Mathlib.Data.Real.Basic
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
  hℱ₂ : ∀ {f₁ f₂}, ℱ f₁ → ℱ f₂ → ℱ (f₁ ∪ f₂)
   -- ℱ is closed under countable intersections
  hℱ₃ : ∀ {f₁ f₂}, ℱ f₁ → ℱ f₂ → ℱ (f₁ ∩ f₂)
  -- ℱ is closed under complements
  hℱ₄ : ∀ {f}, ℱ f → ℱ fᶜ
  -- μ assigns a probability to each measurable subset of Ω
  μ : (f : Set Ω) → ℱ f → (Set.Icc (0 : ℝ) 1)
  -- μ(Ω) = 1
  hμ₁ : μ (λ _outcome ↦ True) hℱ₁ = ⟨(1 : ℝ), (by simp)⟩
  -- μ is countably additive (i.e. the probability of a countable union of pairwise dijoint events is the sum of the events' probabilities)
  hμ₂ : ∀ f₁ f₂ (hf₁ : ℱ f₁) (hf₂ : ℱ f₂),
          f₁ ∩ f₂ = ∅ → (μ (f₁ ∪ f₂) (hℱ₂ hf₁ hf₂)).1 = (μ f₁ hf₁).1 + (μ f₂ hf₂).1

-- The full Ω, we will call `Omega`
def Omega := Nat → Bool

-- First we will define 𝒫_R

section 𝒫_R

variable {n : Nat}
variable (hn : n ≥ 1)

-- Ω for 𝒫_R. Note that this is only the finite part of `Omega`.
def Ω := Fin n → Bool

-- ℱ for 𝒫_R
variable (ℱ : Set (Set Ω))
variable (hℱ₁ : ℱ (λ _outcome ↦ True))
variable (hℱ₂ : ∀ {f₁ f₂}, Set.Countable f₁ → Set.Countable f₂ → ℱ f₁ → ℱ f₂ → ℱ (f₁ ∪ f₂))
variable (hℱ₃ : ∀ {f₁ f₂}, ℱ f₁ → ℱ f₂ → ℱ (f₁ ∩ f₂))
variable (hℱ₄ : ∀ {f}, (hf : ℱ f) → ℱ fᶜ)

-- μ for 𝒫_R
variable (μ : (f : Set Ω) → ℱ f → (Set.Icc (0 : ℝ) 1))
variable (hμ₁ : μ (λ _outcome ↦ True) hℱ₁ = ⟨(1 : ℝ), (by simp)⟩)
variable (hμ₂ : ∀ f₁ f₂ (hC₁ : f₁.Countable) (hC₂ : f₂.Countable) (hf₁ : ℱ f₁) (hf₂ : ℱ f₂),
          f₁ ∩ f₂ = ∅ → (μ (f₁ ∪ f₂) (hℱ₂ hC₁ hC₂ hf₁ hf₂)).1 = (μ f₁ hf₁).1 + (μ f₂ hf₂).1)

def _𝒫_R_ : _𝒫_ := {
  Ω := @Ω n
  ℱ := ℱ
  hℱ₁ := hℱ₁
  hℱ₂ := hℱ₂
  hℱ₃ := hℱ₃
  hℱ₄ := hℱ₄
  μ := μ
  hμ₁ := hμ₁
  hμ₂ := hμ₂
}

noncomputable def _𝒫_trivial_ : _𝒫_ := {
  Ω := {x : Nat | x ≥ n} → Bool
  -- ℱ = {Ω, ∅}
  ℱ := λ f ↦ (f = (λ _outcome ↦ True) ∨ f = (λ _outcome ↦ False))
  hℱ₁ := (by simp)
  hℱ₂ := (by sorry)
  hℱ₃ := (by sorry)
  hℱ₄ := (by sorry)
  μ f hf := if f = ∅ then ⟨0, (by simp)⟩ else ⟨1, (by simp)⟩ 
  hμ₁ := (by sorry)
  hμ₂ := (by sorry)
}

-- TODO: define `independentProduct`
def independentProduct (p₁ p₂ : _𝒫_) : Option _𝒫_ := sorry

infix:20 "⊗" => independentProduct -- TODO: figure out what the precedence level should be

noncomputable def _𝒫_Amaryllis_ := (@_𝒫_R_ n ℱ hℱ₁ hℱ₂ hℱ₃ hℱ₄ μ hμ₁ hμ₂) ⊗ (@_𝒫_trivial_ n)

lemma OmegaLemma₁ :
  match ((@_𝒫_R_ n ℱ hℱ₁ hℱ₂ hℱ₃ hℱ₄ μ hμ₁ hμ₂) ⊗ (@_𝒫_trivial_ n)) with
  | .some PSp => PSp.Ω = Omega
  | .none => True
  := by
    sorry
