module

public import Cslib.Foundations.Data.PFunctor.Free
public import VCVio.OracleComp.OracleComp
public import Foxglove.Basic
public import Init.Data.Rat.Basic


@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace

open unitInterval

inductive BernoulliOps
| Flip : I → BernoulliOps

def BernoulliPFunctor : PFunctor where
  A := BernoulliOps
  B _ := Bool

abbrev BernoulliM := PFunctor.FreeM BernoulliPFunctor

/-- An oracle spec whose operations can be implemented by Bernoulli coin flips. -/
class BernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliPFunctor.FreeM (oSpec.toPFunctor.B op)

def flip (r : I) : BernoulliM Bool :=
  PFunctor.FreeM.liftBind (BernoulliOps.Flip r) PFunctor.FreeM.pure

def split' {n : ℕ} (m : Fin n) : BernoulliM (Fin n) := do
  if h₁ : n = m.1 + 1
    then pure m
    else
      let b ← flip
        ⟨
          (mkRat 1 (n - m.1) : ℝ),
          by
            simp only [Set.mem_Icc, Rat.cast_nonneg, zero_le_one, Rat.mkRat_nonneg, true_and]
            norm_cast
            refine Rat.num_le_denom_iff.mp ?_
            unfold mkRat
            split_ifs with h
            · simp
            · simp only [Rat.num_normalize, isUnit_one, Int.natAbs_of_isUnit, Fin.is_le',
              isUnit_iff_eq_one, IsUnit.dvd, Nat.gcd_sub_left_right_of_dvd, Nat.gcd_one_left,
              Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
              Rat.den_normalize, Nat.div_one, Nat.cast_sub]
              omega⟩
      if b
        then pure m
        else split' (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

def split (n : ℕ) : BernoulliM (Fin (n + 1)) :=
  split' (0 : Fin (n + 1))

/-- The `ℝ≥0` value of a point of the unit interval is at most `1`. -/
lemma toNNReal_le_one (r : I) : unitInterval.toNNReal r ≤ 1 :=
  NNReal.coe_le_coe.mp
    (show ((unitInterval.toNNReal r : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) by simpa using r.2.2)

/-- An unbiased coin. -/
def half : I := ⟨0.5, by simp; apply And.intro <;> linarith⟩

def consFlip (b : Bool) (ω : Ω) : Ω := fun n => if n = 0 then b else ω (n - 1)

@[simp]
lemma consFlip_zero (b : Bool) (ω : Ω) : consFlip b ω 0 = b := rfl

@[simp]
lemma consFlip_succ (b : Bool) (ω : Ω) (n : ℕ) : consFlip b ω (n + 1) = ω n := rfl

@[simp]
lemma shift_consCoin (b : Bool) (ω : Ω) : (fun n => consFlip b ω (n + 1)) = ω := rfl

noncomputable def interp_psp {α : Type} (m : BernoulliM α) : PSp Ω × RV α :=
  match m with
  | PFunctor.FreeM.pure a => (1, fun _ ↦ a)
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
    let (p₀, rv₀) := interp_psp (f false)
    let (p₁, rv₁) := interp_psp (f true)
    let rv' (ω : Ω) : α :=
      if ω 0
      then rv₁ (fun n ↦ ω (n + 1))
      else rv₀ (fun n ↦ ω (n + 1))
    ( PSp.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
        (PSp.map (consFlip false) p₀) (PSp.map (consFlip true) p₁)
    , rv' )

noncomputable def outputPSp {α : Type} (out : PSp Ω × RV α) : PSp α := PSp.map out.2 out.1

/-! ## The `PSpace`-level interpretation

`interp_psp` never produces `↯`, so its space can be given at the `PSpace` level
(`interpSpace`); the output of a program is then `outSpace`, and `outputPSp_eq` relates
the two levels. -/

/-- `interp_psp` never yields `↯`; this is the same space at the `PSpace` level. -/
noncomputable def interpSpace {α : Type} (m : BernoulliM α) : PSpace Ω :=
  match m with
  | PFunctor.FreeM.pure _ => 1
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
      PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
        (PSpace.map (consFlip false) (interpSpace (f false)))
        (PSpace.map (consFlip true) (interpSpace (f true)))

lemma interp_psp_fst {α : Type} (m : BernoulliM α) :
    (interp_psp m).1 = .some (interpSpace m) := by
  induction m with
  | pure a => rfl
  | liftBind op f ih =>
      cases op with
      | Flip r =>
          show PSp.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
                 (PSp.map (consFlip false) (interp_psp (f false)).1)
                 (PSp.map (consFlip true) (interp_psp (f true)).1)
             = .some (PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
                 (PSpace.map (consFlip false) (interpSpace (f false)))
                 (PSpace.map (consFlip true) (interpSpace (f true))))
          rw [ih false, ih true]
          rfl

/-- The output space of an interpreted program. -/
noncomputable def outSpace {α : Type} (m : BernoulliM α) : PSpace α :=
  PSpace.map (interp_psp m).2 (interpSpace m)

lemma outputPSp_eq {α : Type} (m : BernoulliM α) :
    outputPSp (interp_psp m) = .some (outSpace m) := by
  show PSp.map (interp_psp m).2 (interp_psp m).1 = _
  rw [interp_psp_fst]
  rfl

section Interpretation

open MeasureTheory
open scoped ENNReal NNReal Classical

/-! ## Evaluating an interpreted program

The two laws that matter are `outSpace_pure_apply` and `outSpace_liftBind_apply`: the
output of `pure a` is the point mass at `a`, and the output of a flip is the *mixture* of
the two branch outputs.  Together they let any program be evaluated by structural
recursion, and `outSpace_ms` says the result is always discrete. -/

variable {α : Type}

lemma interpSpace_liftBind (r : I) (f : Bool → BernoulliM α) :
    interpSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)
      = PSpace.wsum₂ (unitInterval.toNNReal r) (toNNReal_le_one r)
          (PSpace.map (consFlip false) (interpSpace (f false)))
          (PSpace.map (consFlip true) (interpSpace (f true))) := rfl

lemma rv_liftBind (r : I) (f : Bool → BernoulliM α) :
    (interp_psp (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).2
      = fun ω : Ω => if ω 0 = true then (interp_psp (f true)).2 (fun n => ω (n + 1))
                     else (interp_psp (f false)).2 (fun n => ω (n + 1)) := rfl

/-- Prepending the bit `c` makes the outer random variable agree with branch `c`'s. -/
lemma preimage_consFlip_rv (r : I) (f : Bool → BernoulliM α)
    (c : Bool) (S : Set α) :
    consFlip c ⁻¹' ((interp_psp (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).2 ⁻¹' S)
      = (interp_psp (f c)).2 ⁻¹' S := by
  ext ω; cases c <;> simp [Set.mem_preimage, rv_liftBind]

/-! ### `pure` -/

lemma outSpace_pure (a : α) : outSpace (PFunctor.FreeM.pure a) = PSpace.map (fun _ : Ω => a) 1 :=
  rfl

@[simp] lemma outSpace_pure_ms (a : α) :
    (outSpace (PFunctor.FreeM.pure a)).ms = (⊤ : MeasurableSpace α) :=
  MeasurableSpace.map_const a

lemma measurableSet_outSpace_pure (a : α) (S : Set α) :
    MeasurableSet[(outSpace (PFunctor.FreeM.pure a)).ms] S := by
  rw [outSpace_pure_ms]; trivial

lemma outSpace_pure_apply (a : α) (S : Set α) :
    (outSpace (PFunctor.FreeM.pure a)).μ S = if a ∈ S then 1 else 0 := by
  rw [outSpace, PSpace.map_apply _ _ (measurableSet_outSpace_pure a S)]
  show (1 : PSpace Ω).μ ((fun _ : Ω => a) ⁻¹' S) = _
  by_cases h : a ∈ S
  · have he : (fun _ : Ω => a) ⁻¹' S = Set.univ := by ext ω; simp [h]
    rw [he]; simp [h]
  · have he : (fun _ : Ω => a) ⁻¹' S = ∅ := by ext ω; simp [h]
    rw [he]; simp [h]

/-! ### `flip` -/

lemma measurableSet_outSpace_liftBind (r : I) (f : Bool → BernoulliM α)
    {S : Set α}
    (h₀ : MeasurableSet[(outSpace (f false)).ms] S)
    (h₁ : MeasurableSet[(outSpace (f true)).ms] S) :
    MeasurableSet[(outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).ms] S := by
  rw [outSpace, PSpace.measurableSet_map, interpSpace_liftBind]
  refine PSpace.measurableSet_wsum₂ ?_ ?_ <;>
    rw [PSpace.measurableSet_map, preimage_consFlip_rv]
  · exact h₀
  · exact h₁

/-- The output measure of a flip is the mixture of the branch output measures. -/
lemma outSpace_liftBind_apply (r : I) (f : Bool → BernoulliM α)
    {S : Set α}
    (h₀ : MeasurableSet[(outSpace (f false)).ms] S)
    (h₁ : MeasurableSet[(outSpace (f true)).ms] S) :
    (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).μ S
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞)) * (outSpace (f false)).μ S
        + (unitInterval.toNNReal r : ℝ≥0∞) * (outSpace (f true)).μ S := by
  rw [outSpace, PSpace.map_apply _ _ (by
        rw [← outSpace]; exact measurableSet_outSpace_liftBind r f h₀ h₁),
      interpSpace_liftBind,
      PSpace.wsum₂_map_apply _ _ (consFlip false) (consFlip true) _ _
        (by rw [← interpSpace_liftBind, ← PSpace.measurableSet_map, ← outSpace]
            exact measurableSet_outSpace_liftBind r f h₀ h₁),
      preimage_consFlip_rv, preimage_consFlip_rv,
      ← PSpace.map_apply _ _ h₀, ← PSpace.map_apply _ _ h₁]
  rfl

/-- The output space of *any* interpreted program is discrete: a program only ever
produces finitely many values, through finitely many coin flips. -/
lemma outSpace_ms (m : BernoulliM α) :
    (outSpace m).ms = (⊤ : MeasurableSpace α) := by
  induction m with
  | pure a => exact outSpace_pure_ms a
  | liftBind op f ih =>
      cases op with
      | Flip r =>
          refine PSpace.ms_eq_top_of_all (fun S =>
            measurableSet_outSpace_liftBind r f ?_ ?_)
          · rw [ih false]; trivial
          · rw [ih true]; trivial

lemma measurableSet_outSpace (m : BernoulliM α) (S : Set α) :
    MeasurableSet[(outSpace m).ms] S := by rw [outSpace_ms]; trivial

/-- `outSpace_liftBind_apply` with its side conditions discharged by `outSpace_ms`.  This
is the workhorse: it evaluates a program one flip at a time. -/
lemma outSpace_liftBind_μ (r : I) (f : Bool → BernoulliM α)
    (S : Set α) :
    (outSpace (PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f)).μ S
      = (1 - (unitInterval.toNNReal r : ℝ≥0∞)) * (outSpace (f false)).μ S
        + (unitInterval.toNNReal r : ℝ≥0∞) * (outSpace (f true)).μ S :=
  outSpace_liftBind_apply r f (measurableSet_outSpace _ S) (measurableSet_outSpace _ S)

inductive ProbTree (α : Type) where
  | leaf (m : BernoulliM α)
  | node (p : I) (l r : ProbTree α)

def step {α} /-(μ : Ω → ℝ)-/ (tree : ProbTree α) : ProbTree α :=
  -- measure on a space where prefixes we care about are measurable
  -- from a given tree, we can construct this set of measurable events
  -- (all possible prefixes from root to leaf, and each of those map to an event,
  -- even of all ρ that agree on prefix)
  -- that is the atooms of a Σ-algebra, and then a probability measure on these atoms
  -- the step function updates the set of atoms
  -- new probability measure, that incorporates p and 1 - p
  -- for some event e i, split to e i' and e i''
  -- new μ' - non-split remains the same, otherwise = p * μ ei, 1 - p * μ ei
  match tree with
  | .leaf m =>
    match m with
    | .pure _ => tree
    | .liftBind a cont => split a cont
  | .node p l r => .node p (step l) (step r)
  where split (a : BernoulliPFunctor.A)
              (cont : BernoulliPFunctor.B a → BernoulliPFunctor.FreeM α) : ProbTree α :=
    let p := a.1
    let l : BernoulliM α := cont true
    let r : BernoulliM α := cont false 
    .node p (.leaf l) (.leaf r)

def done {α} (tree : ProbTree α) : Bool :=
  match tree with
  | .leaf m =>
    match m with
    | .pure _ => true
    | .liftBind a cont => false
  | .node p l r => done l && done r

def fixpoint (tree : ProbTree α) : ProbTree α :=
  if done tree
  then tree
  else fixpoint (step tree)
  decreasing_by sorry

-- def (X : RV (BernoulliM α)) (ω : Ω) : BernoulliM α := X ω

-- ∀ Y ∈ atoms P, ∀ ρ ρ' ∈ Y, c ρ = c ρ' -- bigstep to be well defined
-- one atom corresponds to a specific reduction of the expression to something
-- and we haven't reduced further

-- wf_event (atom : Set Ω) (n : ℕ) : Prop := ∀ Y ≤ n, ∀ ρ ρ' ∈ atom, ρ i ≤ ρ' i
-- ∀ ρ ∈ Y, ρ' : Ω, ∀ i < n, ρ i = ρ' i → ρ' ∈ Y

-- f : Finset (List Bool) -- prefixes
-- ∀ elem ∈ f, P elem = straightforward
-- 011101001010
-- ρ Ω, ∀ i < length.ls, ρ i = ls.get i
-- ^ event
-- μ event is the probability of event

def bigStep (comp : BernoulliM α) : PSpΩ → RV (BernoulliM α) → PSpΩ × RV α :=
  let trivialTree := ProbTree.leaf comp
  let f := fixpoint trivialTree
  _

def bigStep' (comp : BernoulliM α) (atoms : Finset (List Bool)) : RV (BernoulliM α) → PSpΩ × RV α :=
  let trivialTree := ProbTree.leaf comp
  let f := fixpoint trivialTree
  _

end Interpretation

end Interp

end Foxglove
