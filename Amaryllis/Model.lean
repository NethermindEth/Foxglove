import Mathlib.Data.Finmap
import Mathlib.Data.Nat.Basic

import Mathlib.Probability.ProbabilityMassFunction.Basic

import Iris.Algebra.UPred
import Iris.Instances.UPred

import Amaryllis.MeasureOnSpace

namespace Amaryllis

abbrev RId : Type := ℕ

abbrev Ω : Type := RId → Bool

abbrev PSpΩ := PSp Ω

abbrev ValidPSpΩ : Type := {psp : PSpΩ // ✓psp}

@[grind =]
lemma valid_def {psp : PSpΩ} : ✓psp ↔ psp ≠ (⊤ : PSpΩ) := by rfl

@[grind norm]
lemma top_def : (⊤ : PSpΩ) = .none := rfl

namespace ValidPSpΩ

def toPSpace (vpsp : ValidPSpΩ) : PSpace Ω :=
  vpsp.1.get (by rcases vpsp with ⟨val, h⟩
                 have : val ≠ .none := by grind
                 erw [Option.ne_none_iff_isSome] at this
                 exact this)

end ValidPSpΩ

abbrev RV (α : Type) := Ω → α

abbrev ABprop := Iris.UPred PSpΩ

section

variable {M : Type} [OrderedUnitalResourceAlgebra M]

def BTrue : UpperSet M := {
  carrier := {x | True}
  upper' := by aesop
}

def BFalse : UpperSet M := {
  carrier := {x | False}
  upper' := by aesop
}

def lift (φ : Prop) : UpperSet M := {
  carrier := {x | φ}
  upper' := by aesop
}

def own (b : M) : UpperSet M := {
  carrier := {a | b ≤ a}
  upper' := by
    intro x y h₁ h₂
    have : b ≤ x := by aesop
    have : b ≤ y := by grind
    aesop
}

def and (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | a ∈ P ∧ a ∈ Q}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def or (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | a ∈ P ∨ a ∈ Q}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def sep (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∃ (b₁ b₂ : M), (b₁ * b₂) ≤ a ∧ b₁ ∈ P ∧ b₂ ∈ Q}
  upper' := by
    intro a b h₁ h₂
    grind
}

def bexists {A : Type*} (K : A → UpperSet M) : UpperSet M := {
  carrier := {a | ∃ x : A, a ∈ K x}
  upper' := by
    intro a b h₁ h₂
    have h₃ : ∃ x : A, a ∈ K x := by aesop
    obtain ⟨x, h₃⟩ := h₃
    have := (K x).upper'
    use x
    aesop
}

def bforall {A : Type*} (K : A → UpperSet M) : UpperSet M := {
  carrier := {a | ∀ x : A, a ∈ K x}
  upper' := by
    intro a b h₁ h₂ x
    have h₃ : ∀ x : A, a ∈ K x := by aesop
    have := (K x).upper'
    aesop
}

def entail (P Q : UpperSet M) : Prop :=
  ∀ m, ✓m → m ∈ P → m ∈ Q

def bientail (P Q : UpperSet M) : Prop :=
  entail P Q ∧ entail Q P

@[simp, grind .]
lemma entail_refl {x : UpperSet M} : entail x x := by simp [entail]

@[simp, grind .]
lemma entail_trans {x y z : UpperSet M} :
  entail x y → entail y z → entail x z := by grind [entail]

@[simp, grind .]
lemma bientail_refl {x : UpperSet M} : bientail x x := by simp [bientail]

@[simp, grind .]
lemma bientail_symm {x y : UpperSet M} :
  bientail x y → bientail y x := by grind [bientail]

@[simp, grind .]
lemma bientail_trans {x y z : UpperSet M} :
  bientail x y → bientail y z → bientail x z := by grind [bientail]


def sForallA (Ψ : UpperSet M → Prop) : UpperSet M := {
  carrier := {a | ∀ p, Ψ p → a ∈ p}
  upper' := by
    intro a b hle ha p hΨ
    exact p.upper' hle (ha p hΨ)
}

def sExistsA (Ψ : UpperSet M → Prop) : UpperSet M := {
  carrier := {a | ∃ p, Ψ p ∧ a ∈ p}
  upper' := by
    intro a b hle ⟨p, hΨ, hpa⟩
    exact ⟨p, hΨ, p.upper' hle hpa⟩
}

def bpersistently (P : UpperSet M) : UpperSet M := {
  carrier := {_a | 1 ∈ P}
  upper' := by intro _ _ _ h; exact h
}

@[simp]
def wand (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∀ b, ✓ (a * b) → b ∈ P → (a * b) ∈ Q}
  upper' := by
    intro a c hac ha b hvcb hPb
    have hab : a * b ≤ c * b := mul_left_mono hac
    have hvab : ✓ (a * b) := valid_mono hab hvcb
    exact Q.upper' hab (ha b hvab hPb)
}

@[simp]
def bimp (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∀ b, a ≤ b → ✓ b → b ∈ P → b ∈ Q}
  upper' := by
    intro a c hac ha b hcb hvb hPb
    exact ha b (le_trans hac hcb) hvb hPb
}

@[simp]
def bident : UpperSet M := {
  carrier := {a | 1 ≤ a}
  upper' := by
    intro a b hle ha
    simp at *
    apply le_trans <;> aesop
}

instance BientailSetoid : Setoid (UpperSet M) where
  r := bientail
  iseqv :=
  {
    refl {_} := bientail_refl
    symm := bientail_symm
    trans := bientail_trans
  }

def UpToBientail (M : Type) [OrderedUnitalResourceAlgebra M] := Quotient (BientailSetoid (M := M))

namespace UpToBientail

def lift (f : UpperSet M → UpperSet M)
         (hf : ∀ {P Q}, bientail P Q → bientail (f P) (f Q)) : UpToBientail M → UpToBientail M :=
  Quotient.map f fun _ _ h ↦ hf h

def lift₂ (f : UpperSet M → UpperSet M → UpperSet M)
          (hf : ∀ {P P₁ Q Q₁}, bientail P P₁ → bientail Q Q₁ → bientail (f P Q) (f P₁ Q₁)) :
    UpToBientail M → UpToBientail M → UpToBientail M :=
  Quotient.map₂ f fun _ _ h₁ _ _ h₂ ↦ hf h₁ h₂

instance : Iris.OFE (UpToBientail M) :=
  {
    Dist _ := (·=·)
    dist_eqv := fun {_} ↦ eq_equivalence
    eq_dist' := by simp
    dist_lt := by grind
  }

instance : Iris.COFE (UpToBientail M) :=
  {
    compl := fun h => h 0
    conv_compl := fun {n c} => by
      
      unfold Iris.OFE.Dist instOFE
      dsimp at *
      rcases c with ⟨chain, cauchy⟩
      simp
      unfold Iris.OFE.Dist instOFE at cauchy
      simp at cauchy
      specialize @cauchy 0 n (by simp)
      exact cauchy.symm
  }    

instance : Iris.BI.BIBase (UpToBientail M) where
  Entails := Quotient.lift₂ Amaryllis.entail sorry
  emp := Quotient.mk _ BTrue
  pure P := Quotient.mk _ (Amaryllis.lift P)
  and := lift₂ Amaryllis.and sorry
  or := lift₂ Amaryllis.or sorry
  imp := lift₂ bimp sorry
  sForall P := Quotient.mk _ (sForallA fun p ↦ P (Quotient.mk _ p))
  sExists P := Quotient.mk _ (sExistsA fun p ↦ P (Quotient.mk _ p))
  sep := lift₂ Amaryllis.sep sorry
  wand := lift₂ wand sorry
  persistently := lift bpersistently sorry
  later := id

instance : Iris.BI (UpToBientail M) where
  entails_refl := by
    sorry
  entails_trans := by
    sorry
  equiv_iff := by
    sorry
  and_ne := by
    sorry
  or_ne := by
    sorry
  imp_ne := by
    sorry
  sForall_ne := by
    sorry
  sExists_ne := by
    sorry
  sep_ne := by 
    sorry
  wand_ne := by
    sorry
  persistently_ne := by
    sorry
  later_ne := by
    sorry
  pure_intro := by
    sorry
  pure_elim' := by
    sorry
  and_elim_l := by
    sorry
  and_elim_r := by
    sorry
  and_intro := by
    sorry
  or_intro_l := by
    sorry
  or_intro_r := by
    sorry
  or_elim := by
    sorry
  imp_intro := by
    sorry
  imp_elim := by
    sorry
  sForall_intro := by
    sorry
  sForall_elim := by
    sorry
  sExists_intro := by
    sorry
  sExists_elim := by
    sorry
  sep_mono := by
    sorry
  emp_sep := by
    sorry
  sep_symm := by
    sorry
  sep_assoc_l := by
    sorry
  wand_intro := by
    sorry
  wand_elim:= by
    sorry
  persistently_mono := by
    sorry
  persistently_idem_2 := by
    sorry
  persistently_emp_2 := by
    sorry
  persistently_and_2 := by
    sorry
  persistently_and_l := by
    sorry
  persistently_absorb_l := by
    sorry
  later_mono := id
  later_intro := by
    sorry
  later_sForall_2 := by
    sorry
  later_sExists_false := by
    sorry
  later_sep := by
    sorry
  later_persistently := by
    sorry
  later_false_em := by
    sorry

end UpToBientail

end

end Amaryllis
