module

public import Foxglove.Rules
public import Foxglove.Rules.WP.Post
public import Foxglove.Interp.OracleComp.Basic
public import Foxglove.Interp.Bernoulli.Helper
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

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

/-- **Sequencing two samplers.**  The law of `C >>= F` is the law of `C` bound with the laws
of the continuations: `WP_BIND_COND` at the law of `C`, `C_BIND` to recollect the fibres. -/
theorem wp_bind_law {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m]
    {α β : Type} [Inhabited α] [Inhabited β] {C : m α} {F : α → m β} {ν : PMF α}
    {κ : α → PMF β} (hC : ⊢ wp C ⦃X, X ~ ν⦄) (hF : ∀ v, ⊢ wp (F v) ⦃Y, Y ~ κ v⦄) :
    ⊢ wp (C >>= F) ⦃Y, Y ~ ν.bind κ⦄ := by
  have hfib : ∀ (X : RV α) (v : α), (⌈X = v⌉ : FProp) ⊢
      ⌈X = v⌉ ∗ wp (F v) ⦃Y, Y ~ κ v⦄ := by
    intro X v
    iintro H
    isplitl [H]
    · iexact H
    · exact hF v
  iapply (WP_CONS fun Y ↦ C_BIND (μ := ν) (κ := κ) (X := Y))
  iapply (WP_BIND_COND (ν := ν) fun v ↦ aeProper_hasDistribution (κ v))
  iapply (WP_CONS fun X ↦ entails_trans (C_UNIT_R (E := X) (μ := ν)).1 (C_CONS (hfib X)))
  exact hC

/-- **Sequencing with a deterministic continuation.**  A sampler followed by a pure function
reports the push-forward of the sampler's law: `wp_bind_law`, with `WP_PURE` and
`DISTR_DIRAC` in every fibre. -/
theorem wp_bind_pure {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m]
    {α β : Type} [Inhabited α] [Inhabited β] {C : m α} {ν : PMF α} (g : α → β)
    (hC : ⊢ wp C ⦃X, X ~ ν⦄) :
    ⊢ wp (C >>= fun x ↦ pure (g x)) ⦃Y, Y ~ PMF.map g ν⦄ := by
  have hmix : ν.bind (fun v ↦ δ (g v)) = PMF.map g ν := PMF.bind_pure_comp g ν
  rw [← hmix]
  exact wp_bind_law hC fun v ↦ by
    iapply (WP_PURE (Q := fun Y ↦ Y ~ δ (g v)))
    exact DISTR_DIRAC

/-! ### Uniform laws -/

/-- A bijection carries the uniform law to the uniform law. -/
lemma uniformOfFintype_map_of_bijective {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] {e : α → β} (he : Function.Bijective e) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  refine PMF.ext fun b ↦ ?_
  obtain ⟨a, rfl⟩ := he.2 b
  rw [PMF.map_apply, tsum_eq_single a (fun a' ha' ↦ ite_eq_right fun h ↦ ha' (he.1 h.symm)),
    ite_eq_left rfl, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    Fintype.card_of_bijective he]

/-- Two independent uniform points make a uniform pair. -/
lemma uniformOfFintype_bind_map_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a ↦ PMF.map (Prod.mk a) (PMF.uniformOfFintype β))
      = PMF.uniformOfFintype (α × β) := by
  refine PMF.ext fun ⟨a, b⟩ ↦ ?_
  -- the inner law puts mass `1 / |β|` on `(a, b)` from the fibre `a` and none from the others
  have hb_eq : PMF.map (Prod.mk a) (PMF.uniformOfFintype β) (a, b)
      = (Fintype.card β : ℝ≥0∞)⁻¹ := by
    rw [PMF.map_apply,
      tsum_eq_single b fun b' hb' ↦ ite_eq_right fun h ↦ hb' (Prod.mk.inj h).2.symm,
      ite_eq_left rfl, PMF.uniformOfFintype_apply]
  have hb_ne : ∀ a', a' ≠ a → PMF.map (Prod.mk a') (PMF.uniformOfFintype β) (a, b) = 0 := by
    intro a' ha'
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun b' ↦ ite_eq_right fun h ↦ ha' (Prod.mk.inj h).1.symm
  rw [PMF.bind_apply, tsum_eq_single a fun a' ha' ↦ by rw [hb_ne a' ha', mul_zero], hb_eq,
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Two independent uniform points, combined by a bijection, make a uniform point. -/
lemma uniformOfFintype_bind_map_of_bijective {α β γ : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] {e : α × β → γ}
    (he : Function.Bijective e) :
    (PMF.uniformOfFintype α).bind
        (fun a ↦ PMF.map (fun b ↦ e (a, b)) (PMF.uniformOfFintype β))
      = PMF.uniformOfFintype γ := by
  rw [← uniformOfFintype_map_of_bijective he, ← uniformOfFintype_bind_map_prod, PMF.map_bind]
  exact congrArg (PMF.bind (PMF.uniformOfFintype α))
    (funext fun a ↦ (PMF.map_comp (Prod.mk a) _ e).symm)

/-- On a one-point type, the uniform law is the Dirac law. -/
lemma uniformOfFintype_eq_dirac {α : Type} [Fintype α] [Nonempty α] [Subsingleton α] (a : α) :
    PMF.uniformOfFintype α = δ a := by
  refine PMF.ext fun b ↦ ?_
  rw [PMF.uniformOfFintype_apply, PMF.pure_apply, ite_eq_left (Subsingleton.elim b a),
    Fintype.card_eq_one_iff.mpr ⟨a, fun b ↦ Subsingleton.elim b a⟩, Nat.cast_one, inv_one]

/-- The chance that a uniform point satisfies a decidable predicate. -/
lemma uniformOfFintype_map_decide_true {α : Type} [Fintype α] [Nonempty α] {P : α → Prop}
    [DecidablePred P] :
    PMF.map (fun x ↦ decide (P x)) (PMF.uniformOfFintype α) (true : Bool)
      = ((Finset.univ.filter P).card : ℝ≥0∞) / Fintype.card α := by
  have hs : (Finset.univ.filter fun x ↦ (true : Bool) = decide (P x))
      = Finset.univ.filter P := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and]
    exact ⟨fun h ↦ of_decide_eq_true h.symm, fun h ↦ (decide_eq_true h).symm⟩
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, hs]

/-! ### Polynomial identity testing -/

section RootTest

variable {p : ℕ} [Fact p.Prime]

/-- **Root test.**  Draw `x` uniformly from `ZMod p` (`unifSpec.query`, on `Fin (p - 1 + 1)`
recast) and report whether `f x = 0`. -/
def rootTest (f : Polynomial (ZMod p)) : OracleComp unifSpec Bool := do
  let x ← (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1)))
  pure (decide (f.eval (x.val : ZMod p) = 0))

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
  have hs : (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0) = f.roots.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hf, Polynomial.IsRoot.def]
  rw [rootLaw, uniformOfFintype_map_decide_true, hs, ZMod.card]

/-- **The law of the root test.**  For a nonzero `f`, the report of `rootTest f` has a law `μ`
with `μ true = |roots f| / p`, counting distinct roots.  The point is uniform
(`wp_unifSpec_query`, recast along `fin_val_cast_bijective`), the test is a deterministic
continuation (`wp_bind_pure`), and the law so obtained is `rootLaw f` (`rootLaw_true`). -/
theorem wp_rootTest_card (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    ⊢ wp (rootTest f)
        ⦃B, ∃ μ : PMF Bool, ⌜μ (true : Bool) = (f.roots.toFinset.card : ℝ≥0∞) / p⌝ ∗ B ~ μ⦄ := by
  -- the law of the report
  have hlaw : ⊢ wp (rootTest f) ⦃B, B ~ rootLaw f⦄ := by
    have hmap : PMF.map (fun x : Fin (p - 1 + 1) ↦ (x.val : ZMod p))
        (PMF.uniformOfFintype (Fin (p - 1 + 1))) = PMF.uniformOfFintype (ZMod p) :=
      uniformOfFintype_map_of_bijective fin_val_cast_bijective
    rw [rootLaw, ← hmap, PMF.map_comp]
    exact wp_bind_pure (C := (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1))))
      (fun x ↦ decide (f.eval (x.val : ZMod p) = 0)) (wp_unifSpec_query (p - 1))
  -- it is the witness
  refine entails_trans hlaw (WP_CONS fun B ↦ ?_)
  iintro H
  iexists rootLaw f
  isplitl []
  · ipureintro
    exact rootLaw_true f hf
  · iexact H

/-- **Schwartz–Zippel**, one variable: a nonzero `f` has at most `deg f` distinct roots, so
`rootTest f` reports `true` with probability at most `deg f / p`.  By consequence from
`wp_rootTest_card`. -/
theorem wp_rootTest (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    ⊢ wp (rootTest f)
        ⦃B, ∃ μ : PMF Bool, ⌜μ (true : Bool) ≤ (f.natDegree : ℝ≥0∞) / p⌝ ∗ B ~ μ⦄ := by
  refine entails_trans (wp_rootTest_card f hf) (WP_CONS fun B ↦ ?_)
  iintro ⟨%μ, %hμ, H⟩
  iexists μ
  isplitl []
  · ipureintro
    rw [hμ]
    exact ENNReal.div_le_div_right
      (by exact_mod_cast (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)) _
  · iexact H

end RootTest

/-! ### Multivariate polynomial identity testing -/

section MvRootTest

open scoped NNRat

variable {p : ℕ} [Fact p.Prime]

/-- A uniform point of `(ZMod p)^n`: `n` independent draws of `unifSpec.query`, recast. -/
def unifVec : (n : ℕ) → OracleComp unifSpec (Fin n → ZMod p)
  | 0 => pure Fin.elim0
  | n + 1 => do
    let x ← (unifSpec.query (p - 1) : OracleComp unifSpec (Fin (p - 1 + 1)))
    let xs ← unifVec n
    pure (Fin.cons (x.val : ZMod p) xs)

/-- Prepending a recast coordinate is a bijection onto the longer tuples. -/
lemma cons_val_cast_bijective (n : ℕ) :
    Function.Bijective fun q : Fin (p - 1 + 1) × (Fin n → ZMod p) ↦
      (Fin.cons (q.1.val : ZMod p) q.2 : Fin (n + 1) → ZMod p) := by
  show Function.Bijective ((fun q : ZMod p × (Fin n → ZMod p) ↦
    (Fin.cons q.1 q.2 : Fin (n + 1) → ZMod p)) ∘ Prod.map (fun x : Fin (p - 1 + 1) ↦ (x.val : ZMod p)) id)
  exact (Fin.consEquiv fun _ ↦ ZMod p).bijective.comp
    (fin_val_cast_bijective.prodMap Function.bijective_id)

/-- `unifVec n` is uniform on `(ZMod p)^n`, by induction on `n`: `wp_bind_law` sequences the
draw of a coordinate with the rest, `wp_bind_pure` prepends it. -/
theorem wp_unifVec : ∀ n : ℕ,
    ⊢ wp (unifVec (p := p) n) ⦃X, X ~ PMF.uniformOfFintype (Fin n → ZMod p)⦄
  | 0 => by
    rw [unifVec, uniformOfFintype_eq_dirac (Fin.elim0 : Fin 0 → ZMod p)]
    iapply (WP_PURE (Q := fun X ↦ X ~ δ (Fin.elim0 : Fin 0 → ZMod p)))
    exact DISTR_DIRAC
  | n + 1 => by
    have hmix : (PMF.uniformOfFintype (Fin (p - 1 + 1))).bind (fun x ↦
        PMF.map (fun xs ↦ (Fin.cons (x.val : ZMod p) xs : Fin (n + 1) → ZMod p))
          (PMF.uniformOfFintype (Fin n → ZMod p)))
        = PMF.uniformOfFintype (Fin (n + 1) → ZMod p) :=
      uniformOfFintype_bind_map_of_bijective (cons_val_cast_bijective n)
    rw [unifVec, ← hmix]
    exact wp_bind_law (wp_unifSpec_query (p - 1)) fun x ↦
      wp_bind_pure (fun xs ↦ (Fin.cons (x.val : ZMod p) xs : Fin (n + 1) → ZMod p))
        (wp_unifVec n)

/-- **Multivariate root test.**  Draw a uniform point of `(ZMod p)^n` and report whether `f`
vanishes there. -/
def mvRootTest {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) : OracleComp unifSpec Bool := do
  let xs ← unifVec n
  pure (decide (MvPolynomial.eval xs f = 0))

/-- The law of the report: `true` with the probability that a uniform point is a zero. -/
def mvRootLaw {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) : PMF Bool :=
  PMF.map (fun xs ↦ decide (MvPolynomial.eval xs f = 0))
    (PMF.uniformOfFintype (Fin n → ZMod p))

/-- `f` is reported as vanishing with probability `|zeros f| / p ^ n`. -/
lemma mvRootLaw_true {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) :
    mvRootLaw f (true : Bool)
      = ((Finset.univ.filter fun xs ↦ MvPolynomial.eval xs f = 0).card : ℝ≥0∞) / p ^ n := by
  rw [mvRootLaw, uniformOfFintype_map_decide_true, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, Nat.cast_pow]

/-- `MvPolynomial.schwartz_zippel_totalDegree` at `S := univ`, carried from `ℚ≥0` to `ℝ≥0∞`
through `ℕ`. -/
lemma card_zeros_div_le {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) (hf : f ≠ 0) :
    ((Finset.univ.filter fun xs ↦ MvPolynomial.eval xs f = 0).card : ℝ≥0∞) / p ^ n
      ≤ (f.totalDegree : ℝ≥0∞) / p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have h := MvPolynomial.schwartz_zippel_totalDegree hf (Finset.univ : Finset (ZMod p))
  simp only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] at h
  set N : ℕ := (Finset.univ.filter fun xs ↦ MvPolynomial.eval xs f = 0).card with hN
  set d : ℕ := f.totalDegree with hd
  -- cross-multiply in `ℚ≥0`, land in `ℕ`
  have hp' : (0 : ℚ≥0) < p := Nat.cast_pos.mpr hp
  rw [div_le_div_iff₀ (pow_pos hp' n) hp'] at h
  have hNd : N * p ≤ d * p ^ n := by exact_mod_cast h
  -- divide again in `ℝ≥0∞`
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hpt : (p : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top p
  calc (N : ℝ≥0∞) / p ^ n = N * p / (p ^ n * p) := (ENNReal.mul_div_mul_right _ _ hp0 hpt).symm
    _ ≤ d * p ^ n / (p ^ n * p) := ENNReal.div_le_div_right (by exact_mod_cast hNd) _
    _ = d / p := by
      rw [mul_comm (d : ℝ≥0∞),
        ENNReal.mul_div_mul_left _ _ (pow_ne_zero n hp0) (ENNReal.pow_ne_top hpt)]

/-- **The law of the multivariate root test.**  The report of `mvRootTest f` has a law `μ`
with `μ true = |zeros f| / p ^ n`: the point is uniform (`wp_unifVec`), the test is a
deterministic continuation (`wp_bind_pure`), and the law so obtained is `mvRootLaw f`
(`mvRootLaw_true`). -/
theorem wp_mvRootTest_card {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) :
    ⊢ wp (mvRootTest f)
        ⦃B, ∃ μ : PMF Bool, ⌜μ (true : Bool)
            = ((Finset.univ.filter fun xs ↦ MvPolynomial.eval xs f = 0).card : ℝ≥0∞) / p ^ n⌝
          ∗ B ~ μ⦄ := by
  have hlaw : ⊢ wp (mvRootTest f) ⦃B, B ~ mvRootLaw f⦄ :=
    wp_bind_pure (fun xs ↦ decide (MvPolynomial.eval xs f = 0)) (wp_unifVec n)
  refine entails_trans hlaw (WP_CONS fun B ↦ ?_)
  iintro H
  iexists mvRootLaw f
  isplitl []
  · ipureintro
    exact mvRootLaw_true f
  · iexact H

/-- **Schwartz–Zippel.**  A nonzero `f` in `n` variables vanishes at a uniform point of
`(ZMod p)^n` with probability at most `deg f / p` (`MvPolynomial.schwartz_zippel_totalDegree`).
By consequence from `wp_mvRootTest_card`. -/
theorem wp_mvRootTest {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) (hf : f ≠ 0) :
    ⊢ wp (mvRootTest f)
        ⦃B, ∃ μ : PMF Bool, ⌜μ (true : Bool) ≤ (f.totalDegree : ℝ≥0∞) / p⌝ ∗ B ~ μ⦄ := by
  refine entails_trans (wp_mvRootTest_card f) (WP_CONS fun B ↦ ?_)
  iintro ⟨%μ, %hμ, H⟩
  iexists μ
  isplitl []
  · ipureintro
    rw [hμ]
    exact card_zeros_div_le f hf
  · iexact H

end MvRootTest

end Sampling

end

end Foxglove
