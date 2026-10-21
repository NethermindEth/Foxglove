module

public import Foxglove.Rules
public import Foxglove.Rules.WP.Post
public import Foxglove.Interp.OracleComp.Basic
public import Foxglove.Interp.Bernoulli.Helper

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

variable {P Q R : FProp}

noncomputable section

/-! # Worked examples

Standard BI facts, true in any affine BI, kept as worked examples of the proof mode at
`FProp`. -/

@[simp, grind .]
theorem and_ident : P ∧ ftrue ⊣⊢ P := by grind

@[simp, grind .]
theorem and_comm : P ∧ Q ⊣⊢ Q ∧ P := by grind

@[simp, grind .]
theorem and_entails_of_entails_l (h : P ⊢ R) : P ∧ Q ⊢ R := by
  have : P ∧ Q ⊢ P := by grind
  grind

@[simp, grind .]
theorem and_entails_of_entails_r (h : Q ⊢ R) : P ∧ Q ⊢ R := by
  have : P ∧ Q ⊢ Q := by grind
  grind

@[simp, grind .]
theorem and_assoc : (P ∧ Q) ∧ R ⊣⊢ P ∧ (Q ∧ R) := by
  grind

@[simp, grind .]
theorem or_ident : P ∨ ffalse ⊣⊢ P := by
  grind

@[simp, grind .]
theorem or_comm : P ∨ Q ⊣⊢ Q ∨ P := by
  grind

theorem or_assoc : (P ∨ Q) ∨ R ⊣⊢ P ∨ (Q ∨ R) := Iris.BI.or_assoc

theorem sep_ident : P ∗ ftrue ⊣⊢ P := by
  refine ⟨?_, ?_⟩
  · iintro ⟨h, _⟩
    iexact h
  · iintro h
    isplitl [h]
    · iexact h
    · exact entails_ftrue

theorem sep_comm : P ∗ Q ⊣⊢ Q ∗ P := by
  refine ⟨?_, ?_⟩
  · iintro ⟨h₁, h₂⟩
    isplitl [h₂]
    · iexact h₂
    · iexact h₁
  · iintro ⟨h₁, h₂⟩
    isplitl [h₂]
    · iexact h₂
    · iexact h₁

theorem sep_assoc : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) := by
  refine ⟨?_, ?_⟩
  · iintro ⟨⟨h₁, h₂⟩, h₃⟩
    isplitl [h₁]
    · iexact h₁
    · isplitl [h₂]
      · iexact h₂
      · iexact h₃
  · iintro ⟨h₁, h₂, h₃⟩
    isplitl [h₁ h₂]
    · isplitl [h₁]
      · iexact h₁
      · iexact h₂
    · iexact h₃

theorem wand_ftrue : ⊢ P -∗ ftrue := entails_wand entails_ftrue

theorem sep_affine : P ∗ Q ⊢ P := by
  iintro ⟨h₁, _⟩
  iexact h₁

theorem true_subst_star (h : Q ⊣⊢ ftrue) : P ⊢ P ∗ Q := by
  iintro h₁
  isplitl [h₁]
  · iexact h₁
  · exact entails_trans entails_ftrue h.2


/-! ### Sure facts as laws -/

/-- A sure fact is a Dirac law at `True`: `SURE_DIRAC` at `v := True`, with the sure fact
`E = True` weakened to `E` and back. -/
theorem very_sure {E : Ω → Prop} : E ~ δ True ⊣⊢ ⌈E⌉ := by
  constructor
  · iintro H
    iapply (liftPred_mono fun _ h ↦ of_eq_true h)
    iapply SURE_DIRAC.1
    iexact H
  · iintro H
    iapply SURE_DIRAC.2
    iapply (liftPred_mono fun _ h ↦ eq_true h)
    iexact H

/-! ### Sampling in `OracleComp unifSpec`

The uniform selection oracle of `unifSpec` (VCVio's `$[0..n]`), implemented by rejection
sampling on coin flips (`Interp.split`). -/

section Sampling

open Interp Interp.Helper
open scoped ENNReal

/-- Rejection sampling from `m` upwards is uniform on `{m, …, N}`: `WP_FLIP` for the coin,
`WP_BIND_COND` to sequence it with the two continuations, `C_BIND` to mix their laws, by
induction on the number of values left. -/
theorem wp_split' {N : ℕ} :
    ∀ (k : ℕ) (m : Fin (N + 1)), N + 1 - m.1 ≤ k →
      ⊢ wp (split' m)
          ⦃X, X ~ PMF.uniformOfFinset (Finset.Ici m) Finset.nonempty_Ici⦄ := by
  intro k
  induction k with
  | zero => intro m hk; exact absurd m.isLt (by omega)
  | succ k ih =>
    intro m hk
    have hU : ∀ i : Fin (N + 1),
        PMF.uniformOfFinset (Finset.Ici m) Finset.nonempty_Ici i
          = if m ≤ i then ((N + 1 - m.1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := fun i ↦ by
      simp only [PMF.uniformOfFinset_apply, Finset.mem_Ici, Fin.card_Ici]
    by_cases h₁ : N + 1 = m.1 + 1
    · -- nothing above `m`: the program returns `m`, and the uniform law is `δ m`
      have hsplit : split' m = (pure m : BernoulliM (Fin (N + 1))) := by
        rw [split', dite_eq_left h₁]
      have hlaw : PMF.uniformOfFinset (Finset.Ici m) Finset.nonempty_Ici = δ m := by
        refine PMF.ext fun i ↦ ?_
        rw [hU, PMF.pure_apply]
        have hi := i.isLt
        by_cases hi' : i = m
        · rw [ite_eq_left (le_of_eq hi'.symm), ite_eq_left hi', show N + 1 - m.1 = 1 by omega]
          simp
        · rw [ite_eq_right fun (h : m ≤ i) ↦ hi' (Fin.ext (le_antisymm (by omega) h)),
            ite_eq_right hi']
      rw [hsplit, hlaw]
      iapply (WP_PURE (Q := fun Y ↦ Y ~ δ m))
      exact DISTR_DIRAC
    · -- flip a coin: report `m` with probability `1 / (N + 1 - m)`, otherwise recurse
      have hm'lt : m.1 + 1 < N + 1 := by have := m.isLt; omega
      have hK1 : 1 ≤ N + 1 - m.1 := by have := m.isLt; omega
      have hK2 : 2 ≤ N + 1 - m.1 := by have := m.isLt; omega
      set pr : unitInterval := ⟨((mkRat 1 (N + 1 - m.1) : ℚ) : ℝ), mkRat_mem_I hK1⟩ with hpr
      set m' : Fin (N + 1) := ⟨m.1 + 1, hm'lt⟩ with hm'
      set Ber : PMF Bool :=
        bernoulliWeights (unitInterval.toNNReal pr) (toNNReal_le_one pr) with hBer
      set κ : Bool → PMF (Fin (N + 1)) := fun b ↦
        if b then δ m else PMF.uniformOfFinset (Finset.Ici m') Finset.nonempty_Ici
        with hκ
      have hsplit : split' m = Interp.flip pr >>= fun b ↦
          if b then (pure m : BernoulliM (Fin (N + 1))) else split' m' := by
        rw [split', dite_eq_right h₁]
      have hp : (unitInterval.toNNReal pr : ℝ≥0∞) = ((N + 1 - m.1 : ℕ) : ℝ≥0∞)⁻¹ :=
        toNNReal_mkRat (N + 1 - m.1) (by omega) _
      -- the two branches' laws mix to the uniform law
      have hmix : Ber.bind κ
          = PMF.uniformOfFinset (Finset.Ici m) Finset.nonempty_Ici := by
        refine PMF.ext fun i ↦ ?_
        rw [PMF.bind_apply, tsum_bool, hU i]
        simp only [hBer, hκ, hm', bernoulliWeights_apply, Bool.cond_false, Bool.cond_true,
          Bool.false_eq_true, ↓reduceIte, PMF.pure_apply, PMF.uniformOfFinset_apply,
          Finset.mem_Ici, Fin.card_Ici, ENNReal.coe_sub, ENNReal.coe_one, hp]
        have hi := i.isLt
        rcases lt_trichotomy i.1 m.1 with hlt | heq | hgt
        · have h1 : ¬ i = m := fun h ↦ by rw [h] at hlt; exact lt_irrefl _ hlt
          have h2 : ¬ m ≤ i := by rw [Fin.le_def]; omega
          have h3 : ¬ (⟨m.1 + 1, hm'lt⟩ : Fin (N + 1)) ≤ i := by
            rw [Fin.le_def]; show ¬ m.1 + 1 ≤ i.1; omega
          simp only [eq_false h1, eq_false h2, eq_false h3, ↓reduceIte, mul_zero, add_zero]
        · have h1 : i = m := Fin.ext heq
          have h2 : m ≤ i := le_of_eq h1.symm
          have h3 : ¬ (⟨m.1 + 1, hm'lt⟩ : Fin (N + 1)) ≤ i := by
            rw [Fin.le_def]; show ¬ m.1 + 1 ≤ i.1; omega
          simp only [eq_true h1, eq_true h2, eq_false h3, ↓reduceIte, mul_zero, mul_one,
            zero_add]
        · have h1 : ¬ i = m := fun h ↦ by rw [h] at hgt; exact lt_irrefl _ hgt
          have h2 : m ≤ i := by rw [Fin.le_def]; omega
          have h3 : (⟨m.1 + 1, hm'lt⟩ : Fin (N + 1)) ≤ i := by
            rw [Fin.le_def]; show m.1 + 1 ≤ i.1; omega
          simp only [eq_false h1, eq_true h2, eq_true h3, ↓reduceIte, mul_zero, add_zero]
          rw [show N + 1 - (m.1 + 1) = N + 1 - m.1 - 1 by omega]
          exact mix_step (N + 1 - m.1) hK2
      -- each continuation has its law: `pure m` by `WP_PURE`, the recursive call by induction
      have hcont : ∀ v : Bool,
          ⊢ wp (if v then (pure m : BernoulliM (Fin (N + 1))) else split' m')
              ⦃Y, Y ~ κ v⦄ := by
        intro v
        cases v
        · exact ih m' (by show N + 1 - (m.1 + 1) ≤ k; omega)
        · show ⊢ wp (pure m : BernoulliM (Fin (N + 1))) ⦃Y, Y ~ δ m⦄
          iapply (WP_PURE (Q := fun Y ↦ Y ~ δ m))
          exact DISTR_DIRAC
      have hfib : ∀ (X : RV Bool) (v : Bool), (⌈X = v⌉ : FProp) ⊢
          ⌈X = v⌉ ∗ wp (if v then (pure m : BernoulliM (Fin (N + 1))) else split' m')
            ⦃Y, Y ~ κ v⦄ := by
        intro X v
        iintro H
        isplitl [H]
        · iexact H
        · exact hcont v
      rw [hsplit, ← hmix]
      iapply (WP_CONS fun Y ↦ C_BIND (μ := Ber) (κ := κ) (X := Y))
      iapply (WP_BIND_COND (ν := Ber) fun v ↦ aeProper_hasDistribution (κ v))
      iapply (WP_CONS fun X ↦ entails_trans (C_UNIT_R (E := X) (μ := Ber)).1 (C_CONS (hfib X)))
      exact WP_FLIP

/-- **Uniform sampling.**  The query `unifSpec.query n` reports a value uniformly distributed
on `Fin (n + 1)`: it interprets to `split n`, rejection sampling from `0` (`wp_split'`). -/
theorem wp_unifSpec_query (n : ℕ) :
    ⊢ wp (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
        ⦃X, X ~ PMF.uniformOfFintype (Fin (n + 1))⦄ := by
  have hq : BernoulliInterpretable.interp (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      = split n := by
    show (split n >>= fun x ↦ pure x) = split n
    exact bind_pure _
  have hlaw : PMF.uniformOfFintype (Fin (n + 1))
      = PMF.uniformOfFinset (Finset.Ici (0 : Fin (n + 1))) Finset.nonempty_Ici := by
    refine PMF.ext fun i ↦ ?_
    simp [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply]
  show ⊢ wp (BernoulliInterpretable.interp (unifSpec.query n : OracleComp unifSpec (Fin (n + 1))))
    ⦃X, X ~ PMF.uniformOfFintype (Fin (n + 1))⦄
  rw [hq, hlaw]
  exact wp_split' (n + 1) 0 (by simp)

end Sampling

end

end Foxglove
