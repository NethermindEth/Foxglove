import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

import Iris

namespace Model

-- _𝒫_ = Probability Space
-- Ω = outcome space
-- ℱ = set of all events (aka subsets of Ω whose probabilities can be measured)
-- μ, the distribution μ gives a probability to every event in ℱ
structure _𝒫_ (Ω : Type*) where
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

-- Ω for 𝒫_R. Note that this is only the finite part of `Omega`.
def _𝒫_R_ (n : Nat) := _𝒫_ (Set (Set (Fin n → Bool)))

noncomputable def _𝒫_trivial_ (n : Nat) : _𝒫_ ({x : Nat | x ≥ n} → Bool) := {
  -- ℱ = {Ω, ∅}
  ℱ := λ f ↦ (f = (λ _outcome ↦ True) ∨ f = (λ _outcome ↦ False))
  hℱ₁ := (by simp)
  hℱ₂ := (by sorry)
  hℱ₃ := (by sorry)
  hℱ₄ := (by sorry)
  μ f hf := if f (λ _ ↦ False) = True then ⟨1, (by simp)⟩ else ⟨0, (by simp)⟩
  hμ₁ := (by sorry)
  hμ₂ := (by sorry)
}

def product.{u} {Ω₁ Ω₂ : Type u} (p₁ : _𝒫_ Ω₁) (p₂ : _𝒫_ Ω₂) : _𝒫_ (Ω₁ × Ω₂) := {
  -- ℱ : (Ω → Prop /- This `Prop` means "is in this subset of Ω" -/)
  --           → Prop /- This `Prop` means "is measurable" -/
  -- ℱ := λ x ↦    p₁.ℱ {x₁ : p₁.Ω | ∃ x₂, (x₁, x₂) ∈ x} 
  --            ∧ (p₂.ℱ {x₂ : p₂.Ω | ∃ x₁, (x₁, x₂) ∈ x})
  ℱ := λ x ↦ p₁.ℱ (Prod.fst <$> x) ∧ p₂.ℱ (Prod.snd <$> x)
  hℱ₁ := sorry
  hℱ₂ := sorry
  hℱ₃ := sorry
  hℱ₄ := sorry
  μ := λ x hx ↦ ⟨(p₁.μ (Prod.fst <$> x) (by aesop)).1 * (p₂.μ (Prod.snd <$> x) (by aesop)).1, sorry⟩
  hμ₁ := sorry
  hμ₂ := sorry
}

infix:20 "⊗" => product -- TODO: figure out what the precedence level should be

noncomputable def _𝒫_Amaryllis_ {n : Nat} (pR : _𝒫_R_ n) := pR ⊗ _𝒫_trivial_ n
  
-- -- This `lemma` is not provable, but I thought it was meant to be.
-- lemma OmegaLemma₁ {n : Nat} :
--   ((_𝒫_R_ n) ⊗ (@_𝒫_trivial_ n)).Ω = Omega
--   := by
--     unfold product _𝒫_R_ _𝒫_trivial_ Omega
--     simp
--     sorry
