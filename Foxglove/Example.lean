module

public import Foxglove.Rules
public import Foxglove.Rules.WP.Post
public import Foxglove.Interp.OracleComp.Basic
public import Foxglove.Interp.Bernoulli.Helper
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots

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
      set Ber : PMF Bool := bernoulliWeights pr with hBer
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
          Finset.mem_Ici, Fin.card_Ici, hp]
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

/-- **Sequencing with a deterministic continuation.**  A sampler followed by a pure function
reports the push-forward of the sampler's law: `WP_BIND_COND` at that law, `WP_PURE` and
`DISTR_DIRAC` in every fibre, `C_BIND` to recollect the fibres. -/
theorem wp_bind_pure {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m]
    {α β : Type} [Inhabited α] [Inhabited β] {C : m α} {ν : PMF α} (g : α → β)
    (hC : ⊢ wp C ⦃X, X ~ ν⦄) :
    ⊢ wp (C >>= fun x ↦ pure (g x)) ⦃Y, Y ~ PMF.map g ν⦄ := by
  have hcont : ∀ v : α, ⊢ wp (pure (g v) : m β) ⦃Y, Y ~ δ (g v)⦄ := fun v ↦ by
    iapply (WP_PURE (Q := fun Y ↦ Y ~ δ (g v)))
    exact DISTR_DIRAC
  have hfib : ∀ (X : RV α) (v : α), (⌈X = v⌉ : FProp) ⊢
      ⌈X = v⌉ ∗ wp (pure (g v) : m β) ⦃Y, Y ~ δ (g v)⦄ := by
    intro X v
    iintro H
    isplitl [H]
    · iexact H
    · exact hcont v
  have hmix : ν.bind (fun v ↦ δ (g v)) = PMF.map g ν := PMF.bind_pure_comp g ν
  rw [← hmix]
  iapply (WP_CONS fun Y ↦ C_BIND (μ := ν) (κ := fun v ↦ δ (g v)) (X := Y))
  iapply (WP_BIND_COND (ν := ν) fun v ↦ aeProper_hasDistribution (δ (g v)))
  iapply (WP_CONS fun X ↦ entails_trans (C_UNIT_R (E := X) (μ := ν)).1 (C_CONS (hfib X)))
  exact hC

/-! ### Polynomial identity testing -/

section RootTest

variable {p : ℕ} [Fact p.Prime]

/-- **Root test.**  Draw `x` uniformly from `ZMod p` (`unifSpec.query`, on `Fin (p - 1 + 1)`
recast) and report whether `f x = 0`. -/
def rootTest (f : Polynomial (ZMod p)) : OracleComp unifSpec Bool := do
  let x ← (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1)))
  pure (decide (f.eval (x.val : ZMod p) = 0))

/-- A bijection carries the uniform law to the uniform law. -/
lemma uniformOfFintype_map_of_bijective {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] {e : α → β} (he : Function.Bijective e) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  refine PMF.ext fun b ↦ ?_
  obtain ⟨a, rfl⟩ := he.2 b
  rw [PMF.map_apply, tsum_eq_single a (fun a' ha' ↦ ite_eq_right fun h ↦ ha' (he.1 h.symm)),
    ite_eq_left rfl, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    Fintype.card_of_bijective he]

/-- The recast `Fin (p - 1 + 1) → ZMod p`, `x ↦ x.val`, is a bijection. -/
lemma fin_val_cast_bijective :
    Function.Bijective fun x : Fin (p - 1 + 1) ↦ (x.val : ZMod p) := by
  have hp : p - 1 + 1 = p := Nat.sub_one_add_one (NeZero.ne p)
  refine ⟨fun x y hxy ↦ Fin.ext ?_,
    fun b ↦ ⟨⟨b.val, b.val_lt.trans_eq hp.symm⟩, ZMod.natCast_zmod_val b⟩⟩
  have hxy' : (x.val : ZMod p) = (y.val : ZMod p) := hxy
  rw [← ZMod.val_cast_of_lt (x.isLt.trans_eq hp), hxy', ZMod.val_cast_of_lt (y.isLt.trans_eq hp)]

/-- The law of the report: `true` with the probability that a uniform point is a root. -/
def rootLaw (f : Polynomial (ZMod p)) : PMF Bool :=
  PMF.map (fun x ↦ decide (f.eval x = 0)) (PMF.uniformOfFintype (ZMod p))

/-- A nonzero `f` is reported as having a root with probability `|roots f| / p`. -/
lemma rootLaw_true (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    rootLaw f (true : Bool) = (f.roots.toFinset.card : ℝ≥0∞) / p := by
  have hs : (Finset.univ.filter fun x : ZMod p ↦ (true : Bool) = decide (f.eval x = 0))
      = f.roots.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hf, Polynomial.IsRoot.def]
    exact ⟨fun h ↦ of_decide_eq_true h.symm, fun h ↦ (decide_eq_true h).symm⟩
  simp only [rootLaw, PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, ZMod.card,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv, hs]

/-- A nonzero `f` has at most `deg f` roots. -/
lemma rootLaw_true_le (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    rootLaw f (true : Bool) ≤ (f.natDegree : ℝ≥0∞) / p := by
  rw [rootLaw_true f hf]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)) _

/-- **Schwartz–Zippel**, one variable: for a nonzero `f`, the report of `rootTest f` has a law
`μ` with `μ true ≤ deg f / p`.  The point is uniform (`wp_unifSpec_query`, recast along
`fin_val_cast_bijective`), the test is a deterministic continuation (`wp_bind_pure`), and the
law so obtained is `rootLaw f` (`rootLaw_true_le`). -/
theorem wp_rootTest (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    ⊢ wp (rootTest f)
        ⦃B, ∃ μ : PMF Bool, ⌜μ (true : Bool) ≤ (f.natDegree : ℝ≥0∞) / p⌝ ∗ B ~ μ⦄ := by
  -- the law of the report
  have hlaw : ⊢ wp (rootTest f) ⦃B, B ~ rootLaw f⦄ := by
    have hmap : PMF.map (fun x : Fin (p - 1 + 1) ↦ (x.val : ZMod p))
        (PMF.uniformOfFintype (Fin (p - 1 + 1))) = PMF.uniformOfFintype (ZMod p) :=
      uniformOfFintype_map_of_bijective fin_val_cast_bijective
    rw [rootLaw, ← hmap, PMF.map_comp]
    exact wp_bind_pure (C := (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1))))
      (fun x ↦ decide (f.eval (x.val : ZMod p) = 0)) (wp_unifSpec_query (p - 1))
  -- it witnesses the bound
  refine entails_trans hlaw (WP_CONS fun B ↦ ?_)
  iintro H
  iexists rootLaw f
  isplitl []
  · ipureintro
    exact rootLaw_true_le f hf
  · iexact H

end RootTest

end Sampling

end

end Foxglove
