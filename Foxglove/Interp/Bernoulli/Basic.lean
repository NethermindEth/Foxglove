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

def shift (ω : Ω) : Ω := fun n => ω (n + 1)

noncomputable def interp_psp {α : Type} (m : BernoulliM α) : PSp Ω × RV α :=
  match m with
  | PFunctor.FreeM.pure a => (1, fun _ ↦ a)
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
    let (p₀, rv₀) := interp_psp (f false)
    let (p₁, rv₁) := interp_psp (f true)
    let rv' (ω : Ω) : α :=
      if ω 0
      then rv₁ (shift ω)
      else rv₀ (shift ω)
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
  | node (l r : ProbTree α)

/-
Honestly, abbrevs just for my own sanity.
-/
abbrev BoolSeq := List Bool

abbrev Event := Set Ω

namespace ProbTree

section

variable {α : Type}

/--
`{[true], [false]}`
`{[true, true], [true, false], [false, true], [false, false]}`
...
-/
def prefixes (tree : ProbTree α) : Finset BoolSeq :=
  match tree with
  | .leaf _ => {[]}
  | .node l r =>
    l.prefixes.map ⟨(true :: ·), List.cons_injective⟩ ∪
    r.prefixes.map ⟨(false :: ·), List.cons_injective⟩

def prefixEqEvent (tape : BoolSeq) : Event := {ω | ∀ (i : Fin tape.length), ω i = tape[i]}

def events (tree : ProbTree α) : Set Event := prefixEqEvent '' {tape | tape ∈ tree.prefixes}

def split (tree : ProbTree α) : ProbTree α :=
  match tree with
  | .leaf m =>
    match m with
    | .pure _ => tree
    | .liftBind _ cont => .node (.leaf (cont true)) (.leaf (cont false))
  | .node l r => .node l.split r.split

def _root_.unitInterval.invert (i : I) : I := ⟨(1 : ℝ) - i, by grind⟩

/--
Get it? A `tape... measure`? No? Ok :(.
-/
def updateMeasure (tree : ProbTree α) (tape : BoolSeq) (μ : BoolSeq → I) : BoolSeq → I :=
  letI lTape := tape ++ [true]
  letI rTape := tape ++ [false]
  match tree, μ with
  | .leaf m, μ =>
    match m with
    | .pure _ => μ
    | .liftBind a _ =>
      letI p := a.1
      letI lProb := p * μ tape
      letI rProb := unitInterval.invert p * μ tape
      letI updateLeft := Function.update μ lTape lProb
      letI updateRight := Function.update updateLeft rTape rProb
      updateRight
  | .node l r, μ => r.updateMeasure rTape (l.updateMeasure lTape μ)

@[instance_reducible]
def ms {α : Type} (tree : ProbTree α) : MeasurableSpace Ω := MeasurableSpace.generateFrom tree.events

/-- The empty prefix constrains nothing. -/
@[simp]
lemma prefixEqEvent_nil : prefixEqEvent [] = (Set.univ : Event) :=
  Set.eq_univ_of_forall fun _ i => i.elim0

/-- A leaf has only the empty prefix, so its only event is `Set.univ`. -/
@[simp]
lemma events_leaf (m : BernoulliM α) : (ProbTree.leaf m).events = {Set.univ} := by
  simp [events, prefixes]

/-- A leaf has not read the tape yet, so it carries the trivial σ-algebra `⊥`: the only
measurable sets are `∅` and `Set.univ`. -/
@[simp]
lemma ms_leaf (m : BernoulliM α) : (ProbTree.leaf m).ms = ⊥ := by
  rw [ms, events_leaf, MeasurableSpace.generateFrom_singleton_univ]

/-! ### The measure after one flip

Splitting the leaf `liftBind (Flip p) c` into `node (leaf (c true)) (leaf (c false))`
refines the trivial σ-algebra of `ms_leaf` into the one generated by the two halves "the
first flip came up `true`" and "… `false`".  Those two events are atoms — nothing in the
tree separates tapes that agree on their first bit — so a measure on the split tree is
exactly a choice of their masses, and `flipMeasure` makes that choice `p` and `1 - p`. -/

/-- `prefixEqEvent [b]` really is the event "the first flip came up `b`": it constrains
`ω 0` and nothing else. -/
@[simp]
lemma mem_prefixEqEvent_singleton (ω : Ω) (b : Bool) :
    ω ∈ prefixEqEvent [b] ↔ ω 0 = b := by
  simp [prefixEqEvent]

/-- The two events of a split leaf: the tapes starting with `true`, resp. with `false`. -/
@[simp]
lemma events_node_leaf (ml mr : BernoulliM α) :
    (ProbTree.node (.leaf ml) (.leaf mr)).events
      = {prefixEqEvent [true], prefixEqEvent [false]} := by
  simp only [events, prefixes]
  simp only [Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.mem_union,
    Finset.mem_singleton]
  exact Set.image_pair ..

noncomputable def flipMeasure (m : MeasurableSpace Ω) (p : I) : Measure[m] Ω :=
  ((toNNReal p) • Measure.dirac (fun _ ↦ true))
    + (1 - (toNNReal p)) • Measure.dirac (fun _ ↦ false)

lemma flipMeasure_apply {m : MeasurableSpace Ω} (p : I) {E : Set Ω} (hE : MeasurableSet[m] E) :
    flipMeasure m p E
      = (if (fun _ ↦ true) ∈ E then (toNNReal p : ℝ≥0∞) else 0)
        + (if (fun _ ↦ false) ∈ E then 1 - (toNNReal p : ℝ≥0∞) else 0) := by
  rw [flipMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, Measure.dirac_apply' _ hE]
  simp [Set.indicator_apply]

instance flipMeasure_isProbabilityMeasure {m : MeasurableSpace Ω} {p : I} :
    IsProbabilityMeasure (flipMeasure m p) where
  measure_univ := by
    rw [flipMeasure_apply p (@MeasurableSet.univ Ω m)]
    simp only [Set.mem_univ, ite_true]
    exact add_tsub_cancel_of_le (by exact_mod_cast toNNReal_le_one p)

def descend (b : Bool) (ω : Ω) : Ω := if ω 0 = b then shift ω else fun _ ↦ b

noncomputable def branchMeasure (b : Bool) {l r : ProbTree α}
    (μ : Measure[(ProbTree.node l r).ms] Ω) : Measure[(if b then l else r).ms] Ω :=
  Measure.map! (ProbTree.node l r).ms (if b then l else r).ms (descend b)
    (μ.restrict (prefixEqEvent [b]))

noncomputable def step' (tree : ProbTree α) (path : List Bool) (μ : Measure[tree.ms] Ω) : Σ tree : ProbTree α, Measure[tree.ms] Ω :=
  match h : tree with
  | .leaf m =>
    match m with
    | .pure _ => Sigma.mk (.leaf m) μ
    | .liftBind a c =>
      let tree' : ProbTree α := .node (.leaf (c true)) (.leaf (c false))
      let μ' : Measure[tree'.ms] Ω := flipMeasure tree'.ms a.1
      Sigma.mk tree' μ'
  | .node l r =>
    let μₗ : Measure[l.ms] Ω := branchMeasure true μ
    let μᵣ : Measure[r.ms] Ω := branchMeasure false μ
    let ⟨l', μₗ'⟩ := step' l (path ++ [true]) μₗ
    let ⟨r', μᵣ'⟩ := step' r (path ++ [true]) μᵣ
    let t' := ProbTree.node l' r'
    let μ' : Measure[t'.ms] Ω := sorry
    Sigma.mk (ProbTree.node l' r') μ'

@[instance_reducible]
def msAfterSplit {α : Type} (tree : ProbTree α) : MeasurableSpace Ω := tree.split.ms

def step (tree : ProbTree α) (μ : Measure[tree.ms] Ω) [IsProbabilityMeasure μ] :
         Measure[tree.msAfterSplit] Ω :=
  let w : BoolSeq → I :=
    tree.updateMeasure [] fun l ↦ ⟨μ.real (prefixEqEvent l), measureReal_nonneg, measureReal_le_one⟩
    -- fold over the set of traces that have been updated
    -- this yields a final boolseq (turn into a measure)
  sorry -- What now?

end

def done (tree : ProbTree α) : Bool :=
  match tree with
  | .leaf m =>
    match m with
    | .pure _ => true
    | .liftBind .. => false
  | .node l r => done l && done r

def leafDepth (m : BernoulliM α) : ℕ :=
  match m with
  | .pure _ => 0
  | .liftBind _ c => 1 + max (leafDepth (c true)) (leafDepth (c false))

def depth (tree : ProbTree α) : ℕ :=
  match tree with
  | .leaf m   => leafDepth m
  | .node l r => max l.depth r.depth

/-! ### Termination of `fixpoint`

`split` peels one layer of flips off every leaf, so it strictly decreases `depth` unless
the tree is already `done` — and a `done` tree has depth `0`. -/

/-- A finished tree has nothing left to split. -/
lemma depth_eq_zero_of_done {tree : ProbTree α} (h : tree.done = true) : tree.depth = 0 := by
  induction tree with
  | leaf m =>
      cases m with
      | pure a => rfl
      | liftBind op cont => simp [done] at h
  | node l r ihl ihr =>
      rw [done] at h
      simp only [Bool.and_eq_true] at h
      simp [depth, ihl h.1, ihr h.2]

/-- `split` never deepens a tree. -/
lemma depth_split_le (tree : ProbTree α) : tree.split.depth ≤ tree.depth := by
  induction tree with
  | leaf m =>
      cases m with
      | pure a => exact le_rfl
      | liftBind op cont => simp only [split, depth, leafDepth]; omega
  | node l r ihl ihr => simp only [split, depth]; omega

/-- As long as there is a flip left somewhere, `split` strictly decreases the depth. -/
lemma depth_split_lt (tree : ProbTree α) (h : tree.done = false) :
    tree.split.depth < tree.depth := by
  induction tree with
  | leaf m =>
      cases m with
      | pure a => simp [done] at h
      | liftBind op cont => simp only [split, depth, leafDepth]; omega
  | node l r ihl ihr =>
      have hl := depth_split_le l
      have hr := depth_split_le r
      rw [done] at h
      simp only [split, depth]
      cases hdl : l.done with
      | false =>
          have h₁ := ihl hdl
          cases hdr : r.done with
          | false => have h₂ := ihr hdr; omega
          | true => have h₂ := depth_eq_zero_of_done hdr; omega
      | true =>
          have hdr : r.done = false := by rw [hdl, Bool.true_and] at h; exact h
          have h₁ := ihr hdr
          have h₂ := depth_eq_zero_of_done hdl
          omega

instance isProbabilityMeasure_step {tree : ProbTree α}
  {μ : Measure[tree.ms] Ω} [IsProbabilityMeasure μ] :
  IsProbabilityMeasure (tree.step μ) := sorry

def fixpoint (tree : ProbTree α) (μ : Measure[tree.ms] Ω) [IsProbabilityMeasure μ] :
    Σ (tree' : ProbTree α), Measure[tree'.ms] Ω :=
  if done tree
  then ⟨tree, μ⟩
  else fixpoint tree.split (tree.step μ)
  termination_by tree.depth
  decreasing_by
    rename_i h
    simp only [Bool.not_eq_true] at h
    exact depth_split_lt tree h

structure BoundedFootprintPsp where
  psp : PSpΩ
  atoms : Set Event

  measurable : ∀ X ∈ atoms, ∀ (h : ✓psp), MeasurableSet[(ValidPSpΩ.toPSpace ⟨psp, h⟩).ms] X
  sigmaAgrees : (h : ✓psp) → (ValidPSpΩ.toPSpace ⟨psp, h⟩).ms = MeasurableSpace.generateFrom atoms
  disjoint : atoms.PairwiseDisjoint id

  prefixes : atoms → BoolSeq
  agreeOnPrefix : ∀ X : atoms, ∀ ρ ∈ X.1, ∀ i : Fin (prefixes X).length, ρ i.1 = (prefixes X)[i]
  determinedByPrefix : ∀ X : atoms, ∀ ρ ∈ X.1, ∀ ρ' : Ω, (∀ i < (prefixes X).length, ρ i = ρ' i) → ρ' ∈ X.1

  pathInTreeValid : ∀ X Y : atoms, X ≠ Y → ¬ prefixes X <+: prefixes Y
  complete : ∀ ρ : Ω, ∃ X ∈ atoms, ρ ∈ X

section scratch

end scratch

namespace BoundedFootprintPsp

def boundmap (bpsp : BoundedFootprintPsp) : bpsp.atoms → ℕ :=
  List.length ∘ bpsp.prefixes

/-- The prefixes of a footprint have bounded length: its nonempty atoms are cylinders, hence open,
and they cover the compact space `Ω`, so finitely many of them already do. By disjointness these are
all the nonempty atoms; the empty atom, if any, contributes one more value. -/
lemma bddAbove_boundmap (bfpsp : BoundedFootprintPsp) : BddAbove (Set.range bfpsp.boundmap) := by
  classical
  have hopen : ∀ X : {X : bfpsp.atoms // X.1.Nonempty}, IsOpen X.1.1 := by
    rintro ⟨X, ρ, hρ⟩
    have hX : X.1 = ⋂ i : Fin (bfpsp.prefixes X).length, (fun ω : Ω ↦ ω i) ⁻¹' {ρ i} := by
      ext ρ'
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h' i ↦ by rw [bfpsp.agreeOnPrefix X ρ' h' i, bfpsp.agreeOnPrefix X ρ hρ i],
        fun h' ↦ bfpsp.determinedByPrefix X ρ hρ ρ' fun i hi ↦ (h' ⟨i, hi⟩).symm⟩
    rw [hX]
    exact isOpen_iInter_of_finite fun i ↦ (isOpen_discrete _).preimage (continuous_apply _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun X : {X : bfpsp.atoms // X.1.Nonempty} ↦ X.1.1) hopen fun ρ _ ↦ by
      obtain ⟨X, hX, hρ⟩ := bfpsp.complete ρ
      exact Set.mem_iUnion.mpr ⟨⟨⟨X, hX⟩, ρ, hρ⟩, hρ⟩
  refine ((t.image fun X ↦ bfpsp.boundmap X.1).finite_toSet.union (Set.finite_singleton
    (if h : ∅ ∈ bfpsp.atoms then bfpsp.boundmap ⟨∅, h⟩ else 0))).bddAbove.mono ?_
  rintro _ ⟨X, rfl⟩
  by_cases hne : X.1.Nonempty
  · obtain ⟨ρ, hρ⟩ := hne
    obtain ⟨Y, hY, hρY⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ρ))
    have hYX : Y.1 = X := by
      by_contra hYX
      exact Set.disjoint_left.mp (bfpsp.disjoint Y.1.2 X.2 (Subtype.coe_ne_coe.mpr hYX)) hρY hρ
    left
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Y, hY, by rw [hYX]⟩)
  · right
    have hX : X.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hmem : ∅ ∈ bfpsp.atoms := hX ▸ X.2
    simp only [Set.mem_singleton_iff, hmem, ↓reduceDIte]
    exact congrArg bfpsp.boundmap (Subtype.ext hX)

noncomputable def toTree {α : Type}
  (bfpsp : BoundedFootprintPsp)
  (programs : bfpsp.atoms → BernoulliM α) : ProbTree α :=
  go []
where
  go (path : BoolSeq) : ProbTree α :=
  if leafy : ∃ X : bfpsp.atoms, bfpsp.prefixes X <+: path then
    .leaf (programs leafy.choose)
  else
    -- `complete` will be needed to reach the base case
    .node (go (path ++ [true])) (go (path ++ [false]))
  termination_by (⨆ X : bfpsp.atoms, bfpsp.boundmap X) - path.length
  decreasing_by
    all_goals
      -- the atom containing the tape through `path` has a prefix comparable with `path`, and
      -- (by `leafy`) not a prefix of it, so strictly longer
      obtain ⟨S, hS, hρ⟩ := bfpsp.complete (fun n ↦ path.getD n false)
      let X : bfpsp.atoms := ⟨S, hS⟩
      have hlt : path.length < (bfpsp.prefixes X).length := by
        by_contra hle
        rw [not_lt] at hle
        refine leafy ⟨X, List.prefix_iff_eq_take.mpr
          (List.ext_getElem (by simp; omega) fun i h₁ h₂ ↦ ?_)⟩
        have h := bfpsp.agreeOnPrefix X _ hρ ⟨i, h₁⟩
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : i < path.length), Option.getD_some] at h
        rw [List.getElem_take]
        exact h.symm
      have hle : (bfpsp.prefixes X).length ≤ ⨆ X : bfpsp.atoms, bfpsp.boundmap X :=
        le_ciSup (bddAbove_boundmap bfpsp) X
      simp only [List.length_append, List.length_singleton]
      omega

-- noncomputable def fromTree {α : Type}
--   (bfpsp : ProbTree α) : BoundedFootprintPsp :=
--   match bfpsp with
--   | .leaf m => _
--   | .node l r => _

end BoundedFootprintPsp

end ProbTree

open ProbTree BoundedFootprintPsp

noncomputable def bigStep (bfpsp : BoundedFootprintPsp)
            (programs : bfpsp.atoms → BernoulliM α) :
            Σ bfpsp : BoundedFootprintPsp, bfpsp.atoms → α :=
  let tree := toTree bfpsp programs
  let tree' := fixpoint tree -- cbfpsp.psp.measure
  -- measure is defined by breaking down input event into atoms,
  -- for each one of those atoms, identify the prefix from the pref. function
  -- pass the pref
  sorry

end Interpretation

end Interp

end Foxglove
