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

/-! ### Basic algebraic helpers -/

lemma valid_mul_l {a b : M} (h : ✓ (a * b)) : ✓ a := valid_mul h

lemma valid_mul_r {a b : M} (h : ✓ (a * b)) : ✓ b := by
  rw [mul_comm] at h
  exact valid_mul h

lemma mul_le_mul_right_le {a b : M} (h : a ≤ b) (c : M) : a * c ≤ b * c :=
  mul_left_mono (a := c) h

lemma mul_le_mul_left_le {a b : M} (h : a ≤ b) (c : M) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_left_mono (a := c) h

/-! ### The BI laws, stated on representatives -/

lemma entail_pure_intro {φ : Prop} {P : UpperSet M} (h : φ) : entail P (Amaryllis.lift φ) :=
  fun _ _ _ ↦ h

lemma entail_pure_elim' {φ : Prop} {P : UpperSet M}
    (h : φ → entail (Amaryllis.lift True) P) : entail (Amaryllis.lift φ) P :=
  fun m hm hφ ↦ h hφ m hm trivial

lemma entail_and_elim_l {P Q : UpperSet M} : entail (Amaryllis.and P Q) P :=
  fun _ _ h ↦ h.1

lemma entail_and_elim_r {P Q : UpperSet M} : entail (Amaryllis.and P Q) Q :=
  fun _ _ h ↦ h.2

lemma entail_and_intro {P Q R : UpperSet M} (h₁ : entail P Q) (h₂ : entail P R) :
    entail P (Amaryllis.and Q R) :=
  fun m hm h ↦ ⟨h₁ m hm h, h₂ m hm h⟩

lemma entail_or_intro_l {P Q : UpperSet M} : entail P (Amaryllis.or P Q) :=
  fun _ _ h ↦ Or.inl h

lemma entail_or_intro_r {P Q : UpperSet M} : entail Q (Amaryllis.or P Q) :=
  fun _ _ h ↦ Or.inr h

lemma entail_or_elim {P Q R : UpperSet M} (h₁ : entail P R) (h₂ : entail Q R) :
    entail (Amaryllis.or P Q) R :=
  fun m hm h ↦ h.elim (h₁ m hm) (h₂ m hm)

lemma entail_imp_intro {P Q R : UpperSet M} (h : entail (Amaryllis.and P Q) R) :
    entail P (bimp Q R) :=
  fun _ _ hP b hle hv hQ ↦ h b hv ⟨P.upper' hle hP, hQ⟩

lemma entail_imp_elim {P Q R : UpperSet M} (h : entail P (bimp Q R)) :
    entail (Amaryllis.and P Q) R :=
  fun m hm hPQ ↦ h m hm hPQ.1 m (le_refl m) hm hPQ.2

lemma entail_sep_mono {P P' Q Q' : UpperSet M} (h : entail P Q) (h' : entail P' Q') :
    entail (Amaryllis.sep P P') (Amaryllis.sep Q Q') := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have hv : ✓ (b₁ * b₂) := valid_mono hle hm
  exact ⟨b₁, b₂, hle, h b₁ (valid_mul_l hv) hb₁, h' b₂ (valid_mul_r hv) hb₂⟩

lemma entail_emp_sep_l {P : UpperSet M} : entail (Amaryllis.sep bident P) P := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have h₁ : b₂ ≤ b₁ * b₂ := by simpa using mul_le_mul_right_le hb₁ b₂
  exact P.upper' (le_trans h₁ hle) hb₂

lemma entail_emp_sep_r {P : UpperSet M} : entail P (Amaryllis.sep bident P) :=
  fun m _ hP ↦ ⟨1, m, le_of_eq (one_mul m), le_refl 1, hP⟩

lemma entail_sep_symm {P Q : UpperSet M} :
    entail (Amaryllis.sep P Q) (Amaryllis.sep Q P) := by
  rintro m _ ⟨b₁, b₂, hle, hb₁, hb₂⟩
  exact ⟨b₂, b₁, by rwa [mul_comm], hb₂, hb₁⟩

lemma entail_sep_assoc_l {P Q R : UpperSet M} :
    entail (Amaryllis.sep (Amaryllis.sep P Q) R) (Amaryllis.sep P (Amaryllis.sep Q R)) := by
  rintro m _ ⟨c₁, c₂, hle, ⟨b₁, b₂, hle', hb₁, hb₂⟩, hc₂⟩
  refine ⟨b₁, b₂ * c₂, ?_, hb₁, ⟨b₂, c₂, le_refl _, hb₂, hc₂⟩⟩
  calc b₁ * (b₂ * c₂) = b₁ * b₂ * c₂ := by rw [mul_assoc]
    _ ≤ c₁ * c₂ := mul_le_mul_right_le hle' c₂
    _ ≤ m := hle

lemma entail_wand_intro {P Q R : UpperSet M} (h : entail (Amaryllis.sep P Q) R) :
    entail P (wand Q R) :=
  fun m _ hP b hv hQ ↦ h (m * b) hv ⟨m, b, le_refl _, hP, hQ⟩

lemma entail_wand_elim {P Q R : UpperSet M} (h : entail P (wand Q R)) :
    entail (Amaryllis.sep P Q) R := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have hv : ✓ (b₁ * b₂) := valid_mono hle hm
  exact R.upper' hle (h b₁ (valid_mul_l hv) hb₁ b₂ hv hb₂)

lemma entail_persistently_mono {P Q : UpperSet M} (h : entail P Q) :
    entail (bpersistently P) (bpersistently Q) :=
  fun _ _ hP ↦ h 1 valid_one hP

lemma entail_persistently_idem_2 {P : UpperSet M} :
    entail (bpersistently P) (bpersistently (bpersistently P)) :=
  fun _ _ hP ↦ hP

lemma entail_persistently_emp_2 : entail (bident : UpperSet M) (bpersistently bident) :=
  fun _ _ _ ↦ le_refl 1

lemma entail_persistently_and_2 {P Q : UpperSet M} :
    entail (Amaryllis.and (bpersistently P) (bpersistently Q))
      (bpersistently (Amaryllis.and P Q)) :=
  fun _ _ h ↦ h

lemma entail_persistently_absorb_l {P Q : UpperSet M} :
    entail (Amaryllis.sep (bpersistently P) Q) (bpersistently P) := by
  rintro m _ ⟨_, _, _, hb₁, _⟩
  exact hb₁

lemma entail_persistently_and_l {P Q : UpperSet M} :
    entail (Amaryllis.and (bpersistently P) Q) (Amaryllis.sep P Q) :=
  fun m _ h ↦ ⟨1, m, le_of_eq (one_mul m), h.1, h.2⟩

/-! ### Congruence of the connectives with respect to bi-entailment -/

lemma entail_eq_of_bientail {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : entail P Q = entail P₁ Q₁ := by
  refine propext ⟨fun h m hm hm' ↦ ?_, fun h m hm hm' ↦ ?_⟩
  · exact hQ.1 m hm (h m hm (hP.2 m hm hm'))
  · exact hQ.2 m hm (h m hm (hP.1 m hm hm'))

lemma bientail_and {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (Amaryllis.and P Q) (Amaryllis.and P₁ Q₁) :=
  ⟨fun m hm h ↦ ⟨hP.1 m hm h.1, hQ.1 m hm h.2⟩,
   fun m hm h ↦ ⟨hP.2 m hm h.1, hQ.2 m hm h.2⟩⟩

lemma bientail_or {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (Amaryllis.or P Q) (Amaryllis.or P₁ Q₁) :=
  ⟨fun m hm h ↦ h.elim (fun h ↦ Or.inl (hP.1 m hm h)) (fun h ↦ Or.inr (hQ.1 m hm h)),
   fun m hm h ↦ h.elim (fun h ↦ Or.inl (hP.2 m hm h)) (fun h ↦ Or.inr (hQ.2 m hm h))⟩

lemma bientail_bimp {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : bientail (bimp P Q) (bimp P₁ Q₁) :=
  ⟨fun _ _ h b hle hv hb ↦ hQ.1 b hv (h b hle hv (hP.2 b hv hb)),
   fun _ _ h b hle hv hb ↦ hQ.2 b hv (h b hle hv (hP.1 b hv hb))⟩

lemma bientail_sep {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (Amaryllis.sep P Q) (Amaryllis.sep P₁ Q₁) :=
  ⟨entail_sep_mono hP.1 hQ.1, entail_sep_mono hP.2 hQ.2⟩

lemma bientail_wand {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : bientail (wand P Q) (wand P₁ Q₁) :=
  ⟨fun _ _ h b hv hb ↦ hQ.1 _ hv (h b hv (hP.2 b (valid_mul_r hv) hb)),
   fun _ _ h b hv hb ↦ hQ.2 _ hv (h b hv (hP.1 b (valid_mul_r hv) hb))⟩

lemma bientail_bpersistently {P Q : UpperSet M} (h : bientail P Q) :
    bientail (bpersistently P) (bpersistently Q) :=
  ⟨entail_persistently_mono h.1, entail_persistently_mono h.2⟩

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
  Entails := Quotient.lift₂ Amaryllis.entail fun _ _ _ _ h₁ h₂ ↦ entail_eq_of_bientail h₁ h₂
  emp := Quotient.mk _ bident
  pure P := Quotient.mk _ (Amaryllis.lift P)
  and := lift₂ Amaryllis.and fun h₁ h₂ ↦ bientail_and h₁ h₂
  or := lift₂ Amaryllis.or fun h₁ h₂ ↦ bientail_or h₁ h₂
  imp := lift₂ bimp fun h₁ h₂ ↦ bientail_bimp h₁ h₂
  sForall P := Quotient.mk _ (sForallA fun p ↦ P (Quotient.mk _ p))
  sExists P := Quotient.mk _ (sExistsA fun p ↦ P (Quotient.mk _ p))
  sep := lift₂ Amaryllis.sep fun h₁ h₂ ↦ bientail_sep h₁ h₂
  wand := lift₂ wand fun h₁ h₂ ↦ bientail_wand h₁ h₂
  persistently := lift bpersistently fun h ↦ bientail_bpersistently h
  later := id

/-- On the quotient, `n`-equivalence is plain equality. -/
theorem dist_iff_eq {n : ℕ} {x y : UpToBientail M} : Iris.OFE.Dist n x y ↔ x = y := Iff.rfl

theorem nonExpansive_of_dist_eq {f : UpToBientail M → UpToBientail M} :
    Iris.OFE.NonExpansive f :=
  ⟨fun _ _ _ h ↦ dist_iff_eq.2 (by rw [dist_iff_eq.1 h])⟩

theorem nonExpansive₂_of_dist_eq {f : UpToBientail M → UpToBientail M → UpToBientail M} :
    Iris.OFE.NonExpansive₂ f :=
  ⟨fun _ _ _ h₁ _ _ h₂ ↦ dist_iff_eq.2 (by rw [dist_iff_eq.1 h₁, dist_iff_eq.1 h₂])⟩

/-- Entailment on the quotient is reflexive. -/
theorem entails_rfl {P : UpToBientail M} : Iris.BI.BIBase.Entails P P := by
  induction P using Quotient.ind
  exact entail_refl

instance : Iris.BI (UpToBientail M) where
  entails_refl := entails_rfl
  entails_trans := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact entail_trans
  equiv_iff := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    refine ⟨fun h ↦ ⟨(Quotient.exact h).1, (Quotient.exact h).2⟩, fun h ↦ ?_⟩
    exact Quotient.sound ⟨h.1, h.2⟩
  and_ne := nonExpansive₂_of_dist_eq
  or_ne := nonExpansive₂_of_dist_eq
  imp_ne := nonExpansive₂_of_dist_eq
  sForall_ne := by
    intro n P₁ P₂ h
    have h' : P₁ = P₂ := Iris.liftRel_eq.mp h
    rw [h']
    exact dist_iff_eq.2 rfl
  sExists_ne := by
    intro n P₁ P₂ h
    have h' : P₁ = P₂ := Iris.liftRel_eq.mp h
    rw [h']
    exact dist_iff_eq.2 rfl
  sep_ne := nonExpansive₂_of_dist_eq
  wand_ne := nonExpansive₂_of_dist_eq
  persistently_ne := nonExpansive_of_dist_eq
  later_ne := nonExpansive_of_dist_eq
  pure_intro := by
    intro φ P h
    induction P using Quotient.ind
    exact entail_pure_intro h
  pure_elim' := by
    intro φ P
    induction P using Quotient.ind
    exact fun h ↦ entail_pure_elim' h
  and_elim_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_and_elim_l
  and_elim_r := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_and_elim_r
  and_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h₁ h₂ ↦ entail_and_intro h₁ h₂
  or_intro_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_or_intro_l
  or_intro_r := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_or_intro_r
  or_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h₁ h₂ ↦ entail_or_elim h₁ h₂
  imp_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_imp_intro h
  imp_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_imp_elim h
  sForall_intro := by
    intro P Ψ
    induction P using Quotient.ind with
    | _ P => exact fun h m hm hP p hΨ ↦ h (Quotient.mk _ p) hΨ m hm hP
  sForall_elim := by
    intro Ψ p
    induction p using Quotient.ind with
    | _ p => exact fun hΨ _ _ hm ↦ hm p hΨ
  sExists_intro := by
    intro Ψ p
    induction p using Quotient.ind with
    | _ p => exact fun hΨ m _ hp ↦ ⟨p, hΨ, hp⟩
  sExists_elim := by
    intro Φ Q
    induction Q using Quotient.ind with
    | _ Q =>
      rintro h m hm ⟨q, hΦ, hq⟩
      exact h (Quotient.mk _ q) hΦ m hm hq
  sep_mono := by
    intro P P' Q Q'
    induction P using Quotient.ind
    induction P' using Quotient.ind
    induction Q using Quotient.ind
    induction Q' using Quotient.ind
    exact fun h h' ↦ entail_sep_mono h h'
  emp_sep := by
    intro P
    induction P using Quotient.ind
    exact ⟨entail_emp_sep_l, entail_emp_sep_r⟩
  sep_symm := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_sep_symm
  sep_assoc_l := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact entail_sep_assoc_l
  wand_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_wand_intro h
  wand_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_wand_elim h
  persistently_mono := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact fun h ↦ entail_persistently_mono h
  persistently_idem_2 := by
    intro P
    induction P using Quotient.ind
    exact entail_persistently_idem_2
  persistently_emp_2 := entail_persistently_emp_2
  persistently_and_2 := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_and_2
  persistently_and_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_and_l
  persistently_absorb_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_absorb_l
  later_mono := id
  later_intro := entails_rfl
  later_sForall_2 := by
    intro Φ m hm h r hΦ
    exact h (bimp (Amaryllis.lift (Φ (Quotient.mk _ r))) r)
      ⟨Quotient.mk _ r, rfl⟩ m (le_refl m) hm hΦ
  later_sExists_false := by
    rintro Φ m _ ⟨r, hΦ, hr⟩
    exact Or.inr ⟨Amaryllis.and (Amaryllis.lift (Φ (Quotient.mk _ r))) r,
      ⟨Quotient.mk _ r, rfl⟩, hΦ, hr⟩
  later_sep := fun {_ _} ↦ ⟨entails_rfl, entails_rfl⟩
  later_persistently := fun {_} ↦ ⟨entails_rfl, entails_rfl⟩
  later_false_em := by
    intro P
    induction P using Quotient.ind
    exact fun _ _ hP ↦ Or.inr fun _ _ _ hb ↦ hb.elim

end UpToBientail

end

end Amaryllis
