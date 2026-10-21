module

public import Foxglove.RuleProofs

@[expose] public section
namespace Foxglove

open ProbSpace Iris UpperSetBI

noncomputable section

/-! # The rules of Foxglove

The unary rules of Bluebell (arXiv 2402.18708; Fig. 9, 10 and 11), together with the bind
rule of Amaryllis (arXiv 2605.13765, Fig. 2) adapted to the monadic `wp`.  Not included: the
rules with index side conditions (`and-to-star`, `c-and`, `wp-conj`), the relational rules,
and the rules for imperative programs. -/

variable
  {P Q : FProp}
  {α β : Type}
  {v v' v₀ : α}
  {E E₁ : RV α}
  {E₂ : RV β}
  {μ μ' μ₁ : PMF α}
  {μ₂ : PMF β}
  {K K₁ K₂ : α → FProp}

section DistributionOwnership

/-
Bluebell, Fig. 9
-/

theorem DIST_INJ : E ~ μ ∧ E ~ μ' ⊢ ⌜μ = μ'⌝ :=
  Proofs.DIST_INJ

variable {E₁ E₂ : RV Prop} in
theorem SURE_MERGE : ⌈E₁⌉ ∗ ⌈E₂⌉ ⊣⊢ ⌈E₁ ∧ E₂⌉ :=
  Proofs.SURE_MERGE

variable {a : Ω → Prop} in
theorem SURE_AND_STAR : ⌈a⌉ ∧ P ⊢ ⌈a⌉ ∗ P :=
  Proofs.SURE_AND_STAR

theorem PROD_SPLIT :
  (E₁ ×ᵣ E₂) ~ (μ₁ ⊗ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ :=
  Proofs.PROD_SPLIT

end DistributionOwnership

section JointConditioning

/-
Bluebell, Fig. 9
-/

theorem C_TRUE : ⊢ 𝒞⟨μ⟩ _v; ftrue :=
  Proofs.C_TRUE

theorem C_FALSE : 𝒞⟨μ⟩ _v; ffalse ⊢ ffalse :=
  Proofs.C_FALSE

theorem C_CONS (h : ∀ v, K₁ v ⊢ K₂ v) : 𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v :=
  Proofs.C_CONS h

theorem C_FRAME : P ∗ 𝒞⟨μ⟩ v; K v ⊢ 𝒞⟨μ⟩ v; (P ∗ K v) :=
  Proofs.C_FRAME

theorem C_UNIT_L : 𝒞⟨δ v₀⟩ v; K v ⊣⊢ K v₀ :=
  Proofs.C_UNIT_L

theorem C_UNIT_R : E ~ μ ⊣⊢ 𝒞⟨μ⟩ v; ⌈E = v⌉ :=
  Proofs.C_UNIT_R

variable {μ₀ : PMF (α × β)} {κ : α → PMF β} {K : (α × β) → FProp} in
theorem C_ASSOC (h : μ₀ = (PMF.bind μ fun v ↦ PMF.bind (κ v) fun w ↦ PMF.pure (v, w))) :
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K (v, w) ⊢ 𝒞⟨μ₀⟩ (v, w); K (v, w) :=
  Proofs.C_ASSOC h

variable {κ : α → PMF β} {K : β → FProp} in
theorem C_UNASSOC :
  𝒞⟨PMF.bind μ κ⟩ w; K w ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w :=
  Proofs.C_UNASSOC

theorem C_SKOLEM {Q : (α × β) → FProp} :
  𝒞⟨μ⟩ v; (∃ x : β, Q (v, x)) ⊢ ∃ (f : α → β), 𝒞⟨μ⟩ v; Q (v, f v) :=
  Proofs.C_SKOLEM

variable {f : β → α} in
theorem C_TRANSF
  (h₁ : Set.BijOn f μ₂.support μ₁.support)
  (h₂ : ∀ b ∈ μ₂.support, μ₂ b = μ₁ (f b)) :
  𝒞⟨μ₁⟩ a; K a ⊢ 𝒞⟨μ₂⟩ b; K (f b) :=
  Proofs.C_TRANSF h₁ h₂

variable {K : α → FProp} {E : RV Prop} in
theorem SURE_STR_CONVEX :
  𝒞⟨μ⟩ v; (K v ∗ ⌈E⌉) ⊢ ⌈E⌉ ∗ 𝒞⟨μ⟩ v; K v :=
  Proofs.SURE_STR_CONVEX

variable {Q : α × β → FProp} in
theorem C_FOR_ALL :
  𝒞⟨μ⟩ v; (∀ (x : β), Q (v, x)) ⊢ ∀ (x : β), 𝒞⟨μ⟩ v; Q (v, x) :=
  Proofs.C_FOR_ALL

theorem C_PURE {X : Set α} :
    ⌜μ.toMeasureWithMs ⊤ X = 1⌝ ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜v ∈ X⌝ ∗ K v) :=
  Proofs.C_PURE

end JointConditioning

section JointConditioningDerived

/-
Bluebell, Fig. 11
-/

variable {κ : α → PMF β} {K : (α × β) → FProp} in
theorem C_FUSE :
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; (K (v, w)) ⊣⊢ 𝒞⟨μ -< κ⟩ (v, w) ; K (v, w) :=
  Proofs.C_FUSE

variable {K : (α × β) → FProp} in
theorem C_SWAP :
  𝒞⟨μ₁⟩ v₁; 𝒞⟨μ₂⟩ v₂; K (v₁, v₂) ⊢ 𝒞⟨μ₂⟩ v₂; 𝒞⟨μ₁⟩ v₁; K (v₁, v₂) :=
  Proofs.C_SWAP

variable {E : RV Prop} in
theorem SURE_CONVEX : 𝒞⟨μ⟩ _v; ⌈E⌉ ⊢ ⌈E⌉ :=
  Proofs.SURE_CONVEX

variable {γ : Type} {μ : PMF γ} in
theorem DIST_CONVEX : 𝒞⟨μ⟩ _v; E ~ μ' ⊢ E ~ μ' :=
  Proofs.DIST_CONVEX

variable {μ : PMF (α × β)} {E : α → Ω → Prop} in
theorem C_SURE_PROJ :
  𝒞⟨μ⟩ (v, _w); ⌈E v⌉ ⊣⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ v; ⌈E v⌉ :=
  Proofs.C_SURE_PROJ

variable {ι γ B : Type} {x : ι → RV γ} {μ : PMF ((ι → γ) × B)} in
theorem C_SURE_PROJ_MANY :
  𝒞⟨μ⟩ (v, _w); ⌈x = v⌉ ⊣⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ v; ⌈x = v⌉ :=
  Proofs.C_SURE_PROJ_MANY

theorem C_EXTRACT :
  𝒞⟨μ₁⟩ v₁; (⌈E₁ = v₁⌉ ∗ E₂ ~ μ₂) ⊢ E₁ ~ μ₁ ∗ E₂ ~ μ₂ :=
  Proofs.C_EXTRACT

variable {α β γ : Type} {μ₁ : PMF (α × β)} {μ₂ : α → PMF γ} {E : α → RV γ} in
theorem C_DIST_PROJ :
  𝒞⟨μ₁⟩ (x, _y); E x ~ μ₂ x ⊢ 𝒞⟨μ₁ ∘ π₁⁻¹⟩ x; E x ~ μ₂ x :=
  Proofs.C_DIST_PROJ

/-
Amaryllis, Fig. 1
-/

variable {κ : α → PMF β} {X : RV β} in
theorem C_BIND : 𝒞⟨μ⟩ v; X ~ κ v ⊢ X ~ μ.bind κ :=
  Proofs.C_BIND

/-
Derived, not in either paper
-/

variable {μ : PMF (α × β)} in
theorem C_PROJ_OF_CONVEX (hK : ∀ a, Convex (K a)) : 𝒞⟨μ⟩ p; K p.1 ⊢ 𝒞⟨μ ∘ π₁⁻¹⟩ a; K a :=
  Proofs.C_PROJ_OF_CONVEX hK

end JointConditioningDerived

section OwnershipAndDistributions

/-
Bluebell, Fig. 11
-/

theorem SURE_DIRAC : E ~ δ v ⊣⊢ ⌈E = v⌉ :=
  Proofs.SURE_DIRAC

theorem SURE_EQ_INJ : ⌈E = v⌉ ∗ ⌈E = v'⌉ ⊢ ⌜v = v'⌝ :=
  Proofs.SURE_EQ_INJ

variable {f : α → β} in
theorem SURE_SUB : E₁ ~ μ ∗ ⌈E₂ = f ∘ E₁⌉ ⊢ E₂ ~ μ ∘ f⁻¹ :=
  Proofs.SURE_SUB

variable {f : α → β} in
theorem DIST_FUN : E ~ μ ⊢ (f ∘ E) ~ μ ∘ f⁻¹ :=
  Proofs.DIST_FUN

theorem DIRAC_DUP : E ~ δ v ⊢ E ~ δ v ∗ E ~ δ v :=
  Proofs.DIRAC_DUP

theorem DIST_SUPP : E ~ μ ⊢ E ~ μ ∗ ⌈E ∈ μ.support⌉ :=
  Proofs.DIST_SUPP

theorem PROD_UNSPLIT : E₁ ~ μ₁ ∗ E₂ ~ μ₂ ⊢ (E₁ ×ᵣ E₂) ~ (μ₁ ⊗ μ₂) :=
  Proofs.PROD_UNSPLIT

/-
Amaryllis, Fig. 1
-/

variable {X Y : RV α} in
theorem DISTR_SUBST : X ~ μ ∗ ⌈X = Y⌉ ⊢ Y ~ μ :=
  Proofs.DISTR_SUBST

theorem DISTR_DIRAC : ⊢ (fun _ : Ω ↦ v) ~ δ v :=
  Proofs.DISTR_DIRAC

end OwnershipAndDistributions

open Interp Interp.ProbTree unitInterval

section StructuralWpRules

/-
Bluebell, Fig. 10
-/

variable {α β : Type} [Inhabited α]
         {m : Type → Type} [Monad m]
         [Interp.LawfulBernoulliInterpretable m]
         {Q Q' : RV α → FProp}
         {t : m α} 
         {C : m α}

theorem WP_CONS (h : Q ⊢ Q') : wp t Q ⊢ wp t Q' :=
  Proofs.WP_CONS h

theorem WP_FRAME : P ∗ wp t Q ⊢ wp t ⦃v, P ∗ Q v⦄ :=
  Proofs.WP_FRAME

variable {μ : PMF β} {Q : β → RV α → FProp}
theorem C_WP_SWAP (hQ : ∀ v, AEProper (Q v)) :
  𝒞⟨μ⟩ v; wp C (Q v) ⊢ wp C ⦃x, 𝒞⟨μ⟩ v; Q v x⦄ :=
  Proofs.C_WP_SWAP hQ

end StructuralWpRules

section ProgramWpRules

variable {α : Type} [Inhabited α]
         {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]

variable [Countable α] {t : BernoulliM α} {ν : PMF α} in
theorem WP_SAMP (hν : ∀ a : α, lawOf t a = ν a) :
  ⊢ wp t ⦃X, X ~ ν⦄ :=
  Proofs.WP_SAMP t ν hν

theorem WP_FLIP {p : I} :
  ⊢ wp (Interp.flip p) ⦃X, X ~ bernoulliWeights (toNNReal p) (Interp.toNNReal_le_one p)⦄ :=
  Proofs.WP_FLIP

end ProgramWpRules

section WeakestPreconditionModality

variable {α β : Type} [Inhabited α] [Inhabited β] {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]

/-
Amaryllis, Fig. 2
-/

variable {Q : RV α → FProp} {x : α} in
theorem WP_PURE : Q (fun _ ↦ x) ⊢ wp (pure x : m α) Q :=
  Proofs.WP_PURE

section WP_BIND

variable {C : m α} {F : α → m β} {ν : PMF α} {Q : α → RV β → FProp} in
theorem WP_BIND_COND (hQ : ∀ v, AEProper (Q v)) :
  wp C ⦃X, 𝒞⟨ν⟩ v; (⌈X = v⌉ ∗ wp (F v) (Q v))⦄ ⊢ wp (C >>= F) ⦃Y, 𝒞⟨ν⟩ v; Q v Y⦄ :=
  Proofs.WP_BIND_COND hQ

variable {C : m α} {F : α → m β} {Q : α → RV β → FProp} in
theorem WP_BIND_C (hQ : ∀ v, AEProper (Q v)) :
  wp C ⦃X, valuePost X (fun v ↦ wp (F v) (Q v))⦄ ⊢ wp (C >>= F) ⦃Y, ∃ ν : PMF α, 𝒞⟨ν⟩ v; Q v Y⦄ :=
  Proofs.WP_BIND_C hQ

end WP_BIND

/-
Derived, not in either paper
-/

variable {C : m α} {F : α → m β} {Q : RV β → FProp} in
theorem WP_BIND (hQ : AEProper Q) (hC : ∀ X : RV β, Convex (Q X)) :
  wp C ⦃X, valuePost X (fun v ↦ wp (F v) Q)⦄ ⊢ wp (C >>= F) Q :=
  Proofs.WP_BIND hQ hC

variable [Countable β] {t : BernoulliM α} {f : α → BernoulliM β} {ν : PMF α} {κ : α → PMF β}
theorem WP_BIND_DIST (hν : ∀ a, lawOf t a = ν a) (hκ : ∀ a b, lawOf (f a) b = κ a b) :
  ⊢ wp (t >>= f) ⦃X, X ~ ν.bind κ⦄ :=
  Proofs.WP_BIND_DIST t f ν κ hν hκ

end WeakestPreconditionModality

end

end Foxglove
