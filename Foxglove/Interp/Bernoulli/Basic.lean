module

public import Foxglove.Algebra.MeasureOnSpace
public import Foxglove.Algebra.OURA
public import Cslib.Foundations.Data.PFunctor.Free
public import Foxglove.Basic
public import Init.Data.Rat.Basic


@[expose] public section
namespace Foxglove

namespace Interp

open ProbSpace MeasureTheory unitInterval ENNReal NNReal Classical

inductive BernoulliOps
| Flip : I → BernoulliOps

/-- Reducible so that `BernoulliPFunctor.A` and `BernoulliPFunctor.B a` unfold to
`BernoulliOps` and `Bool` without delta: `rw` checks motives at `instances` transparency, and
would otherwise reject terms that mix the two spellings. -/
@[reducible]
def BernoulliPFunctor : PFunctor where
  A := BernoulliOps
  B _ := Bool

abbrev BernoulliM := PFunctor.FreeM BernoulliPFunctor

class BernoulliInterpretable (m : Type → Type) where
  interp {α : Type} : m α → BernoulliM α

class BernoulliInterpretable' (P : PFunctor) where
  interp {α : Type} : PFunctor.FreeM P α → BernoulliM α

/-- `BernoulliM` is its own interpretation. -/
instance : BernoulliInterpretable BernoulliM where
  interp := id

@[simp]
lemma interp_bernoulliM {α : Type} (m : BernoulliM α) :
    BernoulliInterpretable.interp m = m := rfl

/-- An interpretation that is a monad morphism.  Without these laws `interp (pure x)` and
`interp (t >>= f)` are unconstrained, so `run (pure x)` need have nothing to do with
returning `x`, and `run (t >>= f)` need have nothing to do with running `t` and then `f` --
and no `wp` rule for `pure` or `>>=` can hold. -/
class LawfulBernoulliInterpretable (m : Type → Type) [Monad m] extends
    BernoulliInterpretable m where
  interp_pure {α : Type} (a : α) :
    BernoulliInterpretable.interp (pure a : m α) = PFunctor.FreeM.pure a
  interp_bind {α β : Type} (t : m α) (f : α → m β) :
    BernoulliInterpretable.interp (t >>= f)
      = BernoulliInterpretable.interp t >>= fun a ↦ BernoulliInterpretable.interp (f a)

class LawfulBernoulliInterpretable' (P : PFunctor)  extends
    BernoulliInterpretable' P where
  interp_pure {α : Type} (a : α) :
    BernoulliInterpretable'.interp (pure a : PFunctor.FreeM P α) = PFunctor.FreeM.pure a
  interp_bind {α β : Type} (t : PFunctor.FreeM P α) (f : α → PFunctor.FreeM P β) :
    BernoulliInterpretable'.interp (t >>= f)
      = BernoulliInterpretable'.interp t >>= fun a ↦ BernoulliInterpretable'.interp (f a)

/-- `BernoulliM` interprets itself, and does so lawfully. -/
instance : LawfulBernoulliInterpretable BernoulliM where
  interp_pure _ := rfl
  interp_bind _ _ := rfl

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

lemma mem_prefixEqEvent_cons (b : Bool) (p : BoolSeq) (ρ : Ω) :
    ρ ∈ prefixEqEvent (b :: p) ↔ ρ 0 = b ∧ (fun n ↦ ρ (n + 1)) ∈ prefixEqEvent p := by
  simp [prefixEqEvent, Fin.forall_fin_succ]

/-- Every tape follows some root-to-leaf path. -/
lemma exists_prefix_mem (tree : ProbTree α) (ρ : Ω) :
    ∃ p ∈ tree.prefixes, ρ ∈ prefixEqEvent p := by
  induction tree generalizing ρ with
  | leaf m => exact ⟨[], by simp [prefixes], fun i ↦ i.elim0⟩
  | node l r ihl ihr =>
    cases h : ρ 0
    · obtain ⟨q, hq, hρ⟩ := ihr fun n ↦ ρ (n + 1)
      exact ⟨false :: q, by simp [prefixes, hq], (mem_prefixEqEvent_cons ..).mpr ⟨h, hρ⟩⟩
    · obtain ⟨q, hq, hρ⟩ := ihl fun n ↦ ρ (n + 1)
      exact ⟨true :: q, by simp [prefixes, hq], (mem_prefixEqEvent_cons ..).mpr ⟨h, hρ⟩⟩

/-- Every root-to-leaf prefix of a tree gives a measurable set in its σ-algebra: the events
are its generators. -/
lemma measurableSet_prefixEqEvent {tree : ProbTree α} {p : BoolSeq} (hp : p ∈ tree.prefixes) :
    MeasurableSet[tree.ms] (prefixEqEvent p) :=
  MeasurableSpace.measurableSet_generateFrom ⟨p, hp, rfl⟩

/-- A path of the `b`-subtree, prefixed by `b`, is a path of the node. -/
lemma mem_prefixes_node {l r : ProbTree α} (b : Bool) {p : BoolSeq}
    (hp : p ∈ (if b then l else r).prefixes) : b :: p ∈ (ProbTree.node l r).prefixes := by
  simp only [prefixes, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
  cases b
  · exact Or.inr ⟨p, by simpa using hp, rfl⟩
  · exact Or.inl ⟨p, by simpa using hp, rfl⟩

/-- `prefixEqEvent [b]` is the union of the events of the subtree's prefixes: every tape
starting with `b` follows one of the subtree's root-to-leaf paths. -/
lemma prefixEqEvent_singleton_eq_biUnion (tree : ProbTree α) (b : Bool) :
    prefixEqEvent [b] = ⋃ p ∈ tree.prefixes, prefixEqEvent (b :: p) := by
  ext ρ
  simp only [Set.mem_iUnion, mem_prefixEqEvent_cons, prefixEqEvent_nil, Set.mem_univ, and_true,
    exists_prop]
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h, _⟩ ↦ h⟩
  obtain ⟨p, hp, hρ⟩ := exists_prefix_mem tree (fun n ↦ ρ (n + 1))
  exact ⟨p, hp, h, hρ⟩

/-- A node has read its first flip, so each of its two halves is measurable. -/
lemma measurableSet_prefixEqEvent_singleton {l r : ProbTree α} (b : Bool) :
    MeasurableSet[(ProbTree.node l r).ms] (prefixEqEvent [b]) := by
  cases b
  · rw [prefixEqEvent_singleton_eq_biUnion r false]
    exact Finset.measurableSet_biUnion _ fun p hp ↦
      measurableSet_prefixEqEvent (mem_prefixes_node false (by simpa using hp))
  · rw [prefixEqEvent_singleton_eq_biUnion l true]
    exact Finset.measurableSet_biUnion _ fun p hp ↦
      measurableSet_prefixEqEvent (mem_prefixes_node true (by simpa using hp))

/-- The two halves of a node partition the tapes, so their masses add up to the total. -/
lemma measure_prefixEqEvent_add {l r : ProbTree α} (μ : Measure[(ProbTree.node l r).ms] Ω) :
    μ (prefixEqEvent [true]) + μ (prefixEqEvent [false]) = μ Set.univ := by
  rw [show prefixEqEvent ([false] : BoolSeq) = (prefixEqEvent ([true] : BoolSeq))ᶜ by
    ext ρ; simp [mem_prefixEqEvent_singleton]]
  exact measure_add_measure_compl (measurableSet_prefixEqEvent_singleton true)

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

/-- Descending into the `b` branch is measurable from the node into the `b`-subtree.  On the
tapes starting with `b` it is the shift, so the preimage of the subtree's event for `p` is the
node's event for `b :: p`; the remaining tapes all go to the constant tape `b`, which
contributes the other half `prefixEqEvent [!b]` exactly when that tape lies in the event. -/
lemma measurable_descend {l r : ProbTree α} (b : Bool) :
    Measurable[(ProbTree.node l r).ms, (if b then l else r).ms] (descend b) := by
  refine @measurable_generateFrom Ω Ω (ProbTree.node l r).ms _ _ ?_
  rintro _ ⟨p, hp, rfl⟩
  have hb : b :: p ∈ (ProbTree.node l r).prefixes := mem_prefixes_node b hp
  by_cases hc : (fun _ ↦ b) ∈ prefixEqEvent p
  · rw [show descend b ⁻¹' prefixEqEvent p = prefixEqEvent (b :: p) ∪ prefixEqEvent [!b] by
      ext ρ
      by_cases h : ρ 0 = b
      · simp only [Set.mem_preimage, descend, h, mem_prefixEqEvent_cons, Set.mem_union,
          Bool.eq_not_iff, ne_eq, not_true_eq_false, false_and, or_false, true_and]
        rfl
      · simp [Set.mem_preimage, descend, h, hc, mem_prefixEqEvent_cons, Bool.eq_not_iff]]
    exact (measurableSet_prefixEqEvent hb).union (measurableSet_prefixEqEvent_singleton _)
  · rw [show descend b ⁻¹' prefixEqEvent p = prefixEqEvent (b :: p) by
      ext ρ
      by_cases h : ρ 0 = b
      · simp only [Set.mem_preimage, descend, h, mem_prefixEqEvent_cons, true_and]
        rfl
      · simp [Set.mem_preimage, descend, h, hc, mem_prefixEqEvent_cons]]
    exact measurableSet_prefixEqEvent hb

/-- Pushing a measure forward along a measurable map keeps its total mass. -/
lemma map!_univ {m₁ m₂ : MeasurableSpace Ω} {f : Ω → Ω} (hf : Measurable[m₁, m₂] f)
    (ν : Measure[m₁] Ω) : (Measure.map! m₁ m₂ f ν) Set.univ = ν Set.univ := by
  rw [show Measure.map! m₁ m₂ f ν = @Measure.map Ω Ω m₁ m₂ f ν from rfl,
    @Measure.map_apply Ω Ω m₁ m₂ ν f hf Set.univ (@MeasurableSet.univ Ω m₂), Set.preimage_univ]

noncomputable def branchMeasure (b : Bool) {l r : ProbTree α}
    (μ : Measure[(ProbTree.node l r).ms] Ω) : Measure[(if b then l else r).ms] Ω :=
  Measure.map! (ProbTree.node l r).ms (if b then l else r).ms (descend b)
    (μ.restrict (prefixEqEvent [b]))

/-- Descending into the `b` branch keeps exactly the mass of the tapes starting with `b`. -/
lemma branchMeasure_univ {l r : ProbTree α} (b : Bool)
    (μ : Measure[(ProbTree.node l r).ms] Ω) :
    branchMeasure b μ Set.univ = μ (prefixEqEvent [b]) := by
  rw [branchMeasure, map!_univ (measurable_descend b), Measure.restrict_apply_univ]

/-- Prepending the bit `b` is measurable from the `b`-subtree into the node: the preimage of
the node's event for `b :: p` is the subtree's event for `p`, and the events of the other
branch pull back to `∅`. -/
lemma measurable_consFlip {l r : ProbTree α} (b : Bool) :
    Measurable[(if b then l else r).ms, (ProbTree.node l r).ms] (consFlip b) := by
  refine @measurable_generateFrom Ω Ω (if b then l else r).ms _ _ ?_
  rintro _ ⟨q, hq, rfl⟩
  simp only [Set.mem_ofPred_eq, prefixes, Finset.mem_union, Finset.mem_map,
    Function.Embedding.coeFn_mk] at hq
  rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;> cases b
  · rw [show consFlip false ⁻¹' prefixEqEvent (true :: p) = ∅ by
      ext ρ; simp [mem_prefixEqEvent_cons]]
    exact MeasurableSpace.measurableSet_empty _
  · rw [show consFlip true ⁻¹' prefixEqEvent (true :: p) = prefixEqEvent p by
      ext ρ; simp [mem_prefixEqEvent_cons]]
    exact measurableSet_prefixEqEvent (by simpa using hp)
  · rw [show consFlip false ⁻¹' prefixEqEvent (false :: p) = prefixEqEvent p by
      ext ρ; simp [mem_prefixEqEvent_cons]]
    exact measurableSet_prefixEqEvent (by simpa using hp)
  · rw [show consFlip true ⁻¹' prefixEqEvent (false :: p) = ∅ by
      ext ρ; simp [mem_prefixEqEvent_cons]]
    exact MeasurableSpace.measurableSet_empty _

noncomputable def joinMeasure {l r : ProbTree α}
    (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) : Measure[(ProbTree.node l r).ms] Ω :=
  Measure.map! l.ms (ProbTree.node l r).ms (consFlip true) μₗ
    + Measure.map! r.ms (ProbTree.node l r).ms (consFlip false) μᵣ

/-- Joining adds the masses of the two branches. -/
lemma joinMeasure_univ {l r : ProbTree α} (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) :
    joinMeasure μₗ μᵣ Set.univ = μₗ Set.univ + μᵣ Set.univ := by
  rw [joinMeasure, Measure.add_apply, map!_univ (measurable_consFlip (l := l) (r := r) true),
    map!_univ (measurable_consFlip (l := l) (r := r) false)]

abbrev TreeWithMeasure (α : Type) := Σ tree : ProbTree α, Measure[tree.ms] Ω

noncomputable def step' (path : BoolSeq) (tree : TreeWithMeasure α) : TreeWithMeasure α :=
  match tree with
  | ⟨.leaf m, μ⟩ =>
    match m with
    | .pure _ => Sigma.mk (.leaf m) μ
    | .liftBind a c =>
      let tree' : ProbTree α := .node (.leaf (c true)) (.leaf (c false))
      let μ' : Measure[tree'.ms] Ω := μ Set.univ • flipMeasure tree'.ms a.1
      Sigma.mk tree' μ'
  | ⟨.node l r, μ⟩ =>
    let μₗ : Measure[l.ms] Ω := branchMeasure true μ
    let μᵣ : Measure[r.ms] Ω := branchMeasure false μ
    let ⟨l', μₗ'⟩ := step' (path ++ [true]) ⟨l, μₗ⟩
    let ⟨r', μᵣ'⟩ := step' (path ++ [false]) ⟨r, μᵣ⟩
    let t' := ProbTree.node l' r'
    let μ' : Measure[t'.ms] Ω := joinMeasure μₗ' μᵣ'
    Sigma.mk (ProbTree.node l' r') μ'

noncomputable def step (tree : TreeWithMeasure α) : TreeWithMeasure α :=
  step' [] tree

/-- On trees, `step'` is just `split`; it only adds the measure. -/
lemma step'_fst {path : BoolSeq} {tree : TreeWithMeasure α} :
    (step' path tree).1 = tree.1.split := by
  obtain ⟨tree, μ⟩ := tree
  induction tree generalizing path with
  | leaf m =>
    cases m with
    | pure a => simp only [step', split]
    | liftBind a c => simp only [step', split]
  | node l r ihl ihr =>
    have hl := @ihl (path ++ [true]) (branchMeasure true μ)
    have hr := @ihr (path ++ [false]) (branchMeasure false μ)
    simp only [step', split]
    revert hl hr
    generalize step' (path ++ [true]) ⟨l, branchMeasure true μ⟩ = sl
    generalize step' (path ++ [false]) ⟨r, branchMeasure false μ⟩ = sr
    obtain ⟨l', μl'⟩ := sl
    obtain ⟨r', μr'⟩ := sr
    rintro (rfl : l' = l.split) (rfl : r' = r.split)
    rfl

lemma step_fst {tree : TreeWithMeasure α} : (step tree).1 = tree.1.split :=
  step'_fst

/-- `step'` only redistributes mass: a leaf keeps its own, a flip splits it between the two
new branches, and a node hands each branch the mass of its half and adds the two back up. -/
lemma step'_univ {path : BoolSeq} {tree : TreeWithMeasure α} :
    (step' path tree).2 Set.univ = tree.2 Set.univ := by
  obtain ⟨tree, μ⟩ := tree
  induction tree generalizing path with
  | leaf m =>
    cases m with
    | pure a => rw [step']
    | liftBind a c =>
      rw [step']
      show (μ Set.univ • flipMeasure _ a.1) Set.univ = μ Set.univ
      rw [Measure.smul_apply, smul_eq_mul]
      simp
  | node l r ihl ihr =>
    have hl := @ihl (path ++ [true]) (branchMeasure true μ)
    have hr := @ihr (path ++ [false]) (branchMeasure false μ)
    rw [step']
    revert hl hr
    generalize step' (path ++ [true]) ⟨l, branchMeasure true μ⟩ = sl
    generalize step' (path ++ [false]) ⟨r, branchMeasure false μ⟩ = sr
    obtain ⟨l', μl'⟩ := sl
    obtain ⟨r', μr'⟩ := sr
    intro hl hr
    show joinMeasure μl' μr' Set.univ = μ Set.univ
    rw [joinMeasure_univ, hl, hr, branchMeasure_univ, branchMeasure_univ,
      measure_prefixEqEvent_add]

lemma step_univ (tree : TreeWithMeasure α) :
    (step tree).2 Set.univ = tree.2 Set.univ :=
  step'_univ

@[instance_reducible]
def msAfterSplit {α : Type} (tree : ProbTree α) : MeasurableSpace Ω := tree.split.ms

end

def done {α : Type} (tree : ProbTree α) : Bool :=
  match tree with
  | .leaf m =>
    match m with
    | .pure _ => true
    | .liftBind .. => false
  | .node l r => done l && done r

def leafDepth {α : Type} (m : BernoulliM α) : ℕ :=
  match m with
  | .pure _ => 0
  | .liftBind _ c => 1 + max (leafDepth (c true)) (leafDepth (c false))

def depth {α : Type} (tree : ProbTree α) : ℕ :=
  match tree with
  | .leaf m   => leafDepth m
  | .node l r => max l.depth r.depth

/-! ### Termination of `fixpoint`

`split` peels one layer of flips off every leaf, so it strictly decreases `depth` unless
the tree is already `done` — and a `done` tree has depth `0`. -/

/-- A finished tree has nothing left to split. -/
lemma depth_eq_zero_of_done {α : Type} {tree : ProbTree α} (h : tree.done = true) : tree.depth = 0 := by
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
lemma depth_split_le {α : Type} (tree : ProbTree α) : tree.split.depth ≤ tree.depth := by
  induction tree with
  | leaf m =>
      cases m with
      | pure a => exact le_rfl
      | liftBind op cont => simp only [split, depth, leafDepth]; omega
  | node l r ihl ihr => simp only [split, depth]; omega

/-- As long as there is a flip left somewhere, `split` strictly decreases the depth. -/
lemma depth_split_lt {α : Type} (tree : ProbTree α) (h : tree.done = false) :
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

/-- A round of `step` is again a probability measure: by `step_univ` it has the same total
mass as the measure it started from. -/
instance {α : Type} {tree : TreeWithMeasure α} [IsProbabilityMeasure tree.2] :
  IsProbabilityMeasure (step tree).2 :=
  ⟨(step_univ tree).trans measure_univ⟩

noncomputable def fixpoint {α : Type} (tree : TreeWithMeasure α) : TreeWithMeasure α :=
  if done tree.1
  then tree
  else fixpoint (step tree)
  termination_by tree.1.depth
  decreasing_by
    rename_i h
    simp only [Bool.not_eq_true] at h
    rw [step_fst]
    exact depth_split_lt tree.1 h

instance {α : Type} {tree : TreeWithMeasure α} [IsProbabilityMeasure tree.2] :
  IsProbabilityMeasure (fixpoint tree).2 := by
  -- each round is a `step`, which preserves probability measures
  rename_i hμ
  revert hμ
  induction tree using fixpoint.induct with
  | case1 t hdone =>
    intro hμ
    -- `fixpoint t`'s measure has a type depending on `fixpoint t`, so rewrite it as a whole
    have e : fixpoint t = t := by rw [fixpoint]; simp [hdone]
    rw [e]
    exact hμ
  | case2 t hdone ih =>
    intro hμ
    have e : fixpoint t = fixpoint (step t) := by rw [fixpoint]; simp [hdone]
    rw [e]
    exact ih

/-- `fixpoint` only stops once every leaf is a `pure`. -/
lemma fixpoint_done {α : Type} {t : TreeWithMeasure α} : (fixpoint t).1.done = true := by
  induction t using fixpoint.induct with
  | case1 t hdone => rw [fixpoint]; simp [hdone]
  | case2 t hdone ih => rw [fixpoint]; simp [hdone, ih]

/-- The footprints over coin tapes: `ProbSpace.BoundedFootprintPsp` at `α := Bool`. -/
abbrev BoundedFootprintPsp := ProbSpace.BoundedFootprintPsp Bool

section scratch

end scratch

/-! ### Prefixes of a tree, for `ofTree` -/

section

variable {α : Type}

/-- Two prefixes of the same tape are comparable. -/
lemma prefix_or_prefix_of_mem {p q : BoolSeq} {ρ : Ω}
    (hp : ρ ∈ prefixEqEvent p) (hq : ρ ∈ prefixEqEvent q) : p <+: q ∨ q <+: p := by
  have key : ∀ {p q : BoolSeq}, ρ ∈ prefixEqEvent p → ρ ∈ prefixEqEvent q →
      p.length ≤ q.length → p <+: q := by
    intro p q hp hq hle
    refine List.prefix_iff_eq_take.mpr (List.ext_getElem (by simp; omega) fun i h₁ h₂ ↦ ?_)
    rw [List.getElem_take]
    exact (hp ⟨i, h₁⟩).symm.trans (hq ⟨i, by omega⟩)
  rcases le_total p.length q.length with h | h
  · exact .inl (key hp hq h)
  · exact .inr (key hq hp h)

/-- The root-to-leaf paths of a tree are prefix-free. -/
lemma prefixFree (tree : ProbTree α) {p q : BoolSeq}
    (hp : p ∈ tree.prefixes) (hq : q ∈ tree.prefixes) (hpq : p <+: q) : p = q := by
  induction tree generalizing p q with
  | leaf m => simp only [prefixes, Finset.mem_singleton] at hp hq; rw [hp, hq]
  | node l r ihl ihr =>
    simp only [prefixes, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hp hq
    rcases hp with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hq with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      simp only [List.cons_prefix_cons, true_and, Bool.true_eq_false, Bool.false_eq_true,
        false_and] at hpq
    · rw [ihl ha hb hpq]
    · rw [ihr ha hb hpq]

end

namespace BoundedFootprintPsp

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
        le_ciSup bfpsp.bddAbove_boundmap X
      simp only [List.length_append, List.length_singleton]
      omega

/-- Every atom is exactly the event of its prefix: any tape starting with the prefix lies in
some atom (`complete`), whose prefix is comparable with this one, so by `pathInTreeValid` it is
this atom. -/
lemma atom_eq_prefixEqEvent (bfpsp : BoundedFootprintPsp) (X : bfpsp.atoms) :
    X.1 = prefixEqEvent (bfpsp.prefixes X) := by
  ext ρ
  refine ⟨fun h ↦ bfpsp.agreeOnPrefix X ρ h, fun h ↦ ?_⟩
  obtain ⟨Y, hY, hρY⟩ := bfpsp.complete ρ
  let Y' : bfpsp.atoms := ⟨Y, hY⟩
  have hρY' : ρ ∈ prefixEqEvent (bfpsp.prefixes Y') := bfpsp.agreeOnPrefix Y' ρ hρY
  by_cases hXY : Y' = X
  · subst hXY
    exact hρY
  · rcases prefix_or_prefix_of_mem hρY' h with h' | h'
    · exact absurd h' (bfpsp.pathInTreeValid Y' X hXY)
    · exact absurd h' (bfpsp.pathInTreeValid X Y' (Ne.symm hXY))

/-- Started at a `path` that extends no atom's prefix except possibly as `path` itself, `toTree.go`
puts a leaf only at the full prefix of some atom. -/
lemma toTree_go_prefixes {α : Type} (bfpsp : BoundedFootprintPsp)
    (programs : bfpsp.atoms → BernoulliM α) (path : BoolSeq)
    (hpath : ∀ X : bfpsp.atoms, bfpsp.prefixes X <+: path → bfpsp.prefixes X = path)
    {q : BoolSeq} (hq : q ∈ (toTree.go bfpsp programs path).prefixes) :
    ∃ X : bfpsp.atoms, bfpsp.prefixes X = path ++ q := by
  induction path using toTree.go.induct bfpsp generalizing q with
  | case1 path leafy =>
    rw [toTree.go] at hq
    simp only [leafy, ↓reduceDIte] at hq
    simp only [ProbTree.prefixes, Finset.mem_singleton] at hq
    obtain ⟨X, hX⟩ := leafy
    exact ⟨X, by rw [hq, List.append_nil]; exact hpath X hX⟩
  | case2 path leafy ihl ihr =>
    rw [toTree.go] at hq
    simp only [leafy, ↓reduceDIte] at hq
    simp only [ProbTree.prefixes, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hq
    -- an atom's prefix below `path ++ [b]` is not below `path`, so it is `path ++ [b]`
    have hstep : ∀ b, ∀ X : bfpsp.atoms,
        bfpsp.prefixes X <+: path ++ [b] → bfpsp.prefixes X = path ++ [b] := by
      intro b X hX
      by_cases hle : (bfpsp.prefixes X).length ≤ path.length
      · exact absurd ⟨X, List.prefix_of_prefix_length_le hX (List.prefix_append _ _) hle⟩ leafy
      · exact hX.eq_of_length (by have := hX.length_le; simp at this ⊢; omega)
    rcases hq with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · obtain ⟨X, hX⟩ := ihl (hstep true) ha
      exact ⟨X, by simp [hX]⟩
    · obtain ⟨X, hX⟩ := ihr (hstep false) ha
      exact ⟨X, by simp [hX]⟩

/-- The tree's σ-algebra is no finer than the footprint's: each of the tree's events is the event of
an atom's prefix, which is that atom. -/
lemma toTree_ms_le {α : Type} (bfpsp : BoundedFootprintPsp) (programs : bfpsp.atoms → BernoulliM α) :
    (toTree bfpsp programs).ms ≤ MeasurableSpace.generateFrom bfpsp.atoms := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨X, hX⟩ := toTree_go_prefixes bfpsp programs [] (fun _ h ↦ List.prefix_nil.mp h) hq
  rw [List.nil_append] at hX
  rw [← hX, ← atom_eq_prefixEqEvent]
  exact MeasurableSpace.measurableSet_generateFrom X.2

/-- The footprint's measure, moved onto the tree's σ-algebra, is still a probability measure. -/
instance {α : Type} (bfpsp : BoundedFootprintPsp)
  (valid : ✓bfpsp.psp) (programs : bfpsp.atoms → BernoulliM α) :
    IsProbabilityMeasure
      ((ProbSpace.ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ.cast (toTree bfpsp programs).ms) where
  measure_univ := by
    have hle : (toTree bfpsp programs).ms ≤ (ProbSpace.ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).ms := by
      rw [bfpsp.sigmaAgrees valid]
      exact toTree_ms_le bfpsp programs
    rw [Measure.le_preserves_measure (h := hle) (hu := MeasurableSet.univ)]
    exact (ProbSpace.ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).2.measure_univ

noncomputable def ofTree {α : Type} (tree : TreeWithMeasure α) [φ : IsProbabilityMeasure tree.2] : BoundedFootprintPsp :=
  {
    psp                := .some ⟨⟨tree.1.ms, tree.2⟩, φ⟩
    atoms              := tree.1.events
    measurable         := fun _ hX _ ↦ MeasurableSpace.measurableSet_generateFrom hX
    sigmaAgrees        := fun _ ↦ rfl
    disjoint           := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
      refine Set.disjoint_left.mpr fun ρ hρp hρq ↦ hne ?_
      rcases prefix_or_prefix_of_mem hρp hρq with h | h
      · rw [prefixFree tree.1 hp hq h]
      · rw [prefixFree tree.1 hq hp h]
    prefixes           := fun X ↦ X.2.choose
    agreeOnPrefix      := fun X ρ hρ i ↦ by
      rw [← X.2.choose_spec.2] at hρ
      exact hρ i
    determinedByPrefix := fun X ρ hρ ρ' h ↦ by
      rw [← X.2.choose_spec.2] at hρ ⊢
      intro i
      rw [← h i.1 i.2]
      exact hρ i
    pathInTreeValid    := fun X Y hXY hpXY ↦ hXY (Subtype.ext (by
      rw [← X.2.choose_spec.2, ← Y.2.choose_spec.2,
        prefixFree tree.1 X.2.choose_spec.1 Y.2.choose_spec.1 hpXY]))
    complete           := fun ρ ↦ (exists_prefix_mem tree.1 ρ).elim
      fun p ⟨hp, hρ⟩ ↦ ⟨prefixEqEvent p, ⟨p, hp, rfl⟩, hρ⟩
  }

end BoundedFootprintPsp

end ProbTree

open ProbTree BoundedFootprintPsp

def _root_.Foxglove.Interp.ProbTree.followTape {α : Type}
  (tree : ProbTree α) (tape : BoolSeq) : Option α :=
  match tree, tape with
  | .leaf (.pure a), _             => .some a
  | .node l _      , true :: tape  => l.followTape tape
  | .node _ r      , false :: tape => r.followTape tape
  | _              , _             => .none

/-- Following a root-to-leaf path of a finished tree reaches a value. -/
lemma followTape_isSome {α : Type} {tree : ProbTree α} {tape : BoolSeq}
  (h₁ : tree.done = true) (h₂ : tape ∈ tree.prefixes) : (tree.followTape tape).isSome := by
  induction tree generalizing tape with
  | leaf m =>
    cases m with
    | pure a => rfl
    | liftBind op c => simp [done] at h₁
  | node l r ihl ihr =>
    simp only [done, Bool.and_eq_true] at h₁
    simp only [ProbTree.prefixes, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk] at h₂
    rcases h₂ with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact ihl h₁.1 ha
    · exact ihr h₁.2 ha

noncomputable def bigStep {α} [Inhabited α] (bfpsp : BoundedFootprintPsp)
                          (programs : bfpsp.atoms → BernoulliM α) :
                          (Σ bfpsp : BoundedFootprintPsp, bfpsp.atoms → α) :=
  if valid : ✓bfpsp.psp
  then
    let tree := toTree bfpsp programs
    -- `(ValidPSpΩ.toPSpace ⟨bfpsp.psp, valid⟩).ms = tree.ms`
    let tree' := fixpoint ⟨tree, (ProbSpace.ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ.cast tree.ms⟩
    Sigma.mk
      (ofTree tree')
      (fun X ↦ (tree'.1.followTape X.2.choose).get (followTape_isSome fixpoint_done X.2.choose_spec.1))
  else
    Sigma.mk bfpsp (fun _ ↦ default)

/-- **The global step.**  Run `t` in every atom of the current global view: the semantics
applied to the whole state, which is what `wp` quantifies over. -/
noncomputable def run {α : Type} [Inhabited α] {m : Type → Type} [BernoulliInterpretable m]
    (t : m α) (μ₀ : BoundedFootprintPsp) : Σ b : BoundedFootprintPsp, b.atoms → α :=
  bigStep μ₀ (fun _ ↦ BernoulliInterpretable.interp t)

/-- Running a program on the unit footprint: nothing has been read yet, so this is the whole
interpretation of a closed program. -/
noncomputable def interp_psp {α : Type} [Inhabited α] (m : BernoulliM α) : (Σ bfpsp : BoundedFootprintPsp, bfpsp.atoms → α) :=
  run m 1

lemma interp_psp_def {α : Type} [Inhabited α] (m : BernoulliM α) :
    interp_psp m = bigStep 1 (fun _ ↦ m) := rfl

/-- The value a finished interpretation reports, as a random variable: the value of the atom
the tape lands in. -/
noncomputable def result {α : Type} (out : Σ b : BoundedFootprintPsp, b.atoms → α) : RV α :=
  out.2 ∘ out.1.atomOf

/-- The space of outputs: push the footprint's space forward along the value the interpretation
gives to the atom each tape lands in. -/
noncomputable def outputPSp {α : Type} (input : Σ bfpsp : BoundedFootprintPsp, bfpsp.atoms → α) : PSp α :=
  PSp.map (result input) input.1.psp

/-! ## Reading off the distribution of a program

Everything below turns `outputPSp (interp_psp m) = ...` into three separable obligations:

* run `m`: exhibit the finished tree and measure `fixpoint` takes it to (`outputPSp_interp`);
* say what each root-to-leaf path reports (`ProbTree.Reports`);
* compute the mass of each atom, and compare point masses (`map_eq_of_singletons`).

`step'_leaf_liftBind`/`step'_node`/`fixpoint_of_done` do the running, `joinMeasure_apply_cons`
and `flipMeasure_apply_singleton` do the masses, and `oneFlipTree`/`twoFlipTree` package the
two shapes that come up in practice. -/

namespace ProbTree

section Reading

variable {α : Type}

/-! ### Equations for `step'` and `fixpoint` -/

/-- A finished leaf is left alone. -/
lemma step'_leaf_pure (path : BoolSeq) (a : α)
    (μ : Measure[(ProbTree.leaf (PFunctor.FreeM.pure a : BernoulliM α)).ms] Ω) :
    step' path ⟨.leaf (.pure a), μ⟩ = ⟨.leaf (.pure a), μ⟩ := by
  rw [step']

/-- A leaf that is about to flip becomes a node, and its mass is split between the two
branches by `flipMeasure`. -/
lemma step'_leaf_liftBind (path : BoolSeq) (a : BernoulliPFunctor.A)
    (c : BernoulliPFunctor.B a → BernoulliM α)
    (μ : Measure[(ProbTree.leaf (PFunctor.FreeM.liftBind a c)).ms] Ω) :
    step' path ⟨.leaf (.liftBind a c), μ⟩
      = ⟨.node (.leaf (c true)) (.leaf (c false)), μ Set.univ • flipMeasure _ a.1⟩ := by
  rw [step']

/-- A node hands each branch the mass of its half, steps both, and adds the two back up. -/
lemma step'_node (path : BoolSeq) {l r : ProbTree α} (μ : Measure[(ProbTree.node l r).ms] Ω) :
    step' path ⟨.node l r, μ⟩
      = ⟨.node (step' (path ++ [true]) ⟨l, branchMeasure true μ⟩).1
               (step' (path ++ [false]) ⟨r, branchMeasure false μ⟩).1,
         joinMeasure (step' (path ++ [true]) ⟨l, branchMeasure true μ⟩).2
                     (step' (path ++ [false]) ⟨r, branchMeasure false μ⟩).2⟩ := by
  rw [step']

lemma fixpoint_of_done {t : TreeWithMeasure α} (h : t.1.done = true) : fixpoint t = t := by
  rw [fixpoint, ite_eq_left h]

lemma fixpoint_of_not_done {t : TreeWithMeasure α} (h : t.1.done = false) :
    fixpoint t = fixpoint (step t) := by
  rw [fixpoint, ite_eq_right (by rw [h]; exact Bool.false_ne_true)]

/-! ### Root-to-leaf paths -/

@[simp]
lemma mem_prefixes_leaf {m : BernoulliM α} {q : BoolSeq} :
    q ∈ (ProbTree.leaf m).prefixes ↔ q = [] := by
  simp [ProbTree.prefixes]

lemma mem_prefixes_node_iff {l r : ProbTree α} {q : BoolSeq} :
    q ∈ (ProbTree.node l r).prefixes ↔
      (∃ q' ∈ l.prefixes, q = true :: q') ∨ (∃ q' ∈ r.prefixes, q = false :: q') := by
  simp [ProbTree.prefixes, eq_comm]

/-- The two root-to-leaf paths of a split leaf. -/
lemma mem_prefixes_node_leaf {ml mr : BernoulliM α} {q : BoolSeq} :
    q ∈ (ProbTree.node (.leaf ml) (.leaf mr)).prefixes ↔ q = [true] ∨ q = [false] := by
  simp [ProbTree.prefixes]

lemma mem_prefixEqEvent_pair (ρ : Ω) (b₀ b₁ : Bool) :
    ρ ∈ prefixEqEvent [b₀, b₁] ↔ ρ 0 = b₀ ∧ ρ 1 = b₁ := by
  simp [prefixEqEvent, Fin.forall_fin_succ]

/-- Distinct root-to-leaf paths describe disjoint sets of tapes. -/
lemma disjoint_prefixEqEvent {t : ProbTree α} {q q' : BoolSeq} (hq : q ∈ t.prefixes)
    (hq' : q' ∈ t.prefixes) (hne : q ≠ q') :
    Disjoint (prefixEqEvent q) (prefixEqEvent q') := by
  refine Set.disjoint_left.mpr fun ρ h h' ↦ hne ?_
  rcases prefix_or_prefix_of_mem h h' with hp | hp
  · exact prefixFree t hq hq' hp
  · exact (prefixFree t hq' hq hp).symm

/-- Two atoms are disjoint, so their masses add. -/
lemma measure_union_atoms {t : ProbTree α} (μ : Measure[t.ms] Ω) {q q' : BoolSeq}
    (hq : q ∈ t.prefixes) (hq' : q' ∈ t.prefixes) (hne : q ≠ q') :
    μ (prefixEqEvent q ∪ prefixEqEvent q') = μ (prefixEqEvent q) + μ (prefixEqEvent q') :=
  measure_union (disjoint_prefixEqEvent hq hq' hne) (measurableSet_prefixEqEvent hq')

/-! ### What a finished tree reports -/

/-- `t` *reports* `g` if the value at the end of each root-to-leaf path is `g`'s value on the
tapes that follow it.  This is the shape the output of a finished tree always has, and it is
all `outputPSp_interp` needs to know about it. -/
def Reports (t : ProbTree α) (g : Ω → α) : Prop :=
  ∀ q ∈ t.prefixes, ∀ ρ ∈ prefixEqEvent q, t.followTape q = some (g ρ)

/-- A reported value depends only on which atom the tape lands in. -/
lemma Reports.const {t : ProbTree α} {g : Ω → α} (hg : Reports t g) {q : BoolSeq}
    (hq : q ∈ t.prefixes) {ρ ρ' : Ω} (hρ : ρ ∈ prefixEqEvent q) (hρ' : ρ' ∈ prefixEqEvent q) :
    g ρ = g ρ' :=
  Option.some_injective _ ((hg q hq ρ hρ).symm.trans (hg q hq ρ' hρ'))

/-- A reported value pulls every set back to a measurable one: the preimage is the union of
the finitely many atoms whose value lies in it. -/
lemma Reports.measurableSet_preimage {t : ProbTree α} {g : Ω → α} (hg : Reports t g)
    (S : Set α) : MeasurableSet[t.ms] (g ⁻¹' S) := by
  classical
  have hEq : g ⁻¹' S
      = ⋃ q ∈ t.prefixes.filter (fun q ↦ ∃ ρ ∈ prefixEqEvent q, g ρ ∈ S), prefixEqEvent q := by
    ext ρ
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    refine ⟨fun hρ ↦ ?_, ?_⟩
    · obtain ⟨q, hq, hρq⟩ := exists_prefix_mem t ρ
      exact ⟨q, ⟨hq, ρ, hρq, hρ⟩, hρq⟩
    · rintro ⟨q, ⟨hq, ρ', hρ'q, hρ'S⟩, hρq⟩
      rwa [hg.const hq hρq hρ'q]
  rw [hEq]
  exact Finset.measurableSet_biUnion _ fun q hq ↦
    measurableSet_prefixEqEvent (Finset.mem_filter.mp hq).1

/-! ### The mass of an atom -/

lemma map!_apply {m₁ m₂ : MeasurableSpace Ω} {f : Ω → Ω} (hf : Measurable[m₁, m₂] f)
    (ν : Measure[m₁] Ω) {S : Set Ω} (hS : MeasurableSet[m₂] S) :
    (Measure.map! m₁ m₂ f ν) S = ν (f ⁻¹' S) :=
  @Measure.map_apply Ω Ω m₁ m₂ ν f hf S hS

lemma preimage_consFlip_cons (b b' : Bool) (q : BoolSeq) :
    consFlip b ⁻¹' prefixEqEvent (b' :: q) = if b = b' then prefixEqEvent q else ∅ := by
  ext ρ
  by_cases h : b = b' <;> simp [h, mem_prefixEqEvent_cons]

/-- Joining puts each branch's atoms back where they came from, mass unchanged. -/
lemma joinMeasure_apply_cons {l r : ProbTree α} (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω)
    (b : Bool) {q : BoolSeq} (hq : q ∈ (if b then l else r).prefixes) :
    joinMeasure μₗ μᵣ (prefixEqEvent (b :: q))
      = if b then μₗ (prefixEqEvent q) else μᵣ (prefixEqEvent q) := by
  have hm : MeasurableSet[(ProbTree.node l r).ms] (prefixEqEvent (b :: q)) :=
    measurableSet_prefixEqEvent (mem_prefixes_node b hq)
  rw [joinMeasure, Measure.add_apply,
    map!_apply (measurable_consFlip (l := l) (r := r) true) _ hm,
    map!_apply (measurable_consFlip (l := l) (r := r) false) _ hm,
    preimage_consFlip_cons, preimage_consFlip_cons]
  cases b <;> simp

/-- The weight a flip of bias `p` gives the outcome `b`. -/
noncomputable def flipWeight (p : I) (b : Bool) : ℝ≥0∞ :=
  if b then (unitInterval.toNNReal p : ℝ≥0∞) else 1 - (unitInterval.toNNReal p : ℝ≥0∞)

lemma flipWeight_add (p : I) : flipWeight p true + flipWeight p false = 1 := by
  rw [flipWeight, flipWeight]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact add_tsub_cancel_of_le (by exact_mod_cast toNNReal_le_one p)

lemma flipMeasure_apply_singleton {m : MeasurableSpace Ω} (p : I) (b : Bool)
    (hm : MeasurableSet[m] (prefixEqEvent [b])) :
    flipMeasure m p (prefixEqEvent [b]) = flipWeight p b := by
  rw [flipMeasure_apply p hm, flipWeight]
  cases b <;> simp

/-! ### Tapes: `consFlip`, `shift`, `descend` -/

lemma descend_of_eq {b : Bool} {ρ : Ω} (h : ρ 0 = b) : descend b ρ = shift ρ := ite_eq_left h

lemma consFlip_shift {b : Bool} {ρ : Ω} (h : ρ 0 = b) : consFlip b (shift ρ) = ρ := by
  funext n
  cases n with
  | zero => exact h.symm
  | succ k => rfl

@[simp]
lemma shift_consFlip (b : Bool) (ρ : Ω) : shift (consFlip b ρ) = ρ := rfl

@[simp]
lemma mem_prefixEqEvent_consFlip (b : Bool) (ρ : Ω) : consFlip b ρ ∈ prefixEqEvent [b] := by
  rw [mem_prefixEqEvent_singleton]; rfl

/-- `MeasureTheory.Measure.ext` at an explicitly given σ-algebra: the ambient instance on
`Ω` is the product one, which is never the one a tree carries. -/
lemma measure_ext {m : MeasurableSpace Ω} {μ ν : Measure[m] Ω}
    (h : ∀ E, MeasurableSet[m] E → μ E = ν E) : μ = ν :=
  @MeasureTheory.Measure.ext Ω m μ ν h

/-! ### `branchMeasure` and `joinMeasure`, applied -/

lemma branchMeasure_apply' {l r : ProbTree α} (b : Bool) (ν : Measure[(ProbTree.node l r).ms] Ω)
    {S : Set Ω} (hS : MeasurableSet[(if b then l else r).ms] S) :
    branchMeasure b ν S = ν (descend b ⁻¹' S ∩ prefixEqEvent [b]) := by
  rw [branchMeasure, map!_apply (measurable_descend b) _ hS,
    Measure.restrict_apply (measurable_descend b hS)]

lemma joinMeasure_apply {l r : ProbTree α} (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω)
    {E : Set Ω} (hE : MeasurableSet[(ProbTree.node l r).ms] E) :
    joinMeasure μₗ μᵣ E = μₗ (consFlip true ⁻¹' E) + μᵣ (consFlip false ⁻¹' E) := by
  rw [joinMeasure, Measure.add_apply,
    map!_apply (measurable_consFlip (l := l) (r := r) true) _ hE,
    map!_apply (measurable_consFlip (l := l) (r := r) false) _ hE]

lemma preimage_descend_consFlip (b : Bool) (E : Set Ω) :
    descend b ⁻¹' (consFlip b ⁻¹' E) ∩ prefixEqEvent [b] = E ∩ prefixEqEvent [b] := by
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_prefixEqEvent_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [descend_of_eq h2, consFlip_shift h2] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [descend_of_eq h2, consFlip_shift h2]
    exact h1

lemma preimage_consFlip_descend (b b' : Bool) (S : Set Ω) :
    consFlip b ⁻¹' (descend b' ⁻¹' S ∩ prefixEqEvent [b']) = if b = b' then S else ∅ := by
  ext ρ
  by_cases h : b = b'
  · subst h
    simp only [Set.mem_preimage, Set.mem_inter_iff, mem_prefixEqEvent_consFlip, and_true,
      ↓reduceIte]
    rw [descend_of_eq (show consFlip b ρ 0 = b from rfl), shift_consFlip]
  · simp only [Set.mem_preimage, Set.mem_inter_iff, mem_prefixEqEvent_singleton, h, ↓reduceIte,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    rw [show consFlip b ρ 0 = b from rfl]
    exact h

/-- Splitting a measure into its two halves and joining them back gives it back. -/
lemma joinMeasure_branchMeasure {l r : ProbTree α} (ν : Measure[(ProbTree.node l r).ms] Ω) :
    joinMeasure (branchMeasure true ν) (branchMeasure false ν) = ν := by
  refine measure_ext (fun E hE ↦ ?_)
  rw [joinMeasure_apply _ _ hE,
    branchMeasure_apply' true ν (measurable_consFlip (l := l) (r := r) true hE),
    branchMeasure_apply' false ν (measurable_consFlip (l := l) (r := r) false hE),
    preimage_descend_consFlip, preimage_descend_consFlip,
    show prefixEqEvent ([false] : BoolSeq) = (prefixEqEvent ([true] : BoolSeq))ᶜ by
      ext ρ; simp [mem_prefixEqEvent_singleton],
    ← Set.sdiff_eq]
  exact measure_inter_add_sdiff (μ := ν) E (measurableSet_prefixEqEvent_singleton true)

/-- Joining two measures and then taking the `true` half gives the first one back. -/
lemma branchMeasure_joinMeasure_true {l r : ProbTree α}
    (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) :
    branchMeasure (l := l) (r := r) true (joinMeasure μₗ μᵣ) = μₗ := by
  refine measure_ext (fun S hS ↦ ?_)
  rw [branchMeasure_apply' true _ hS,
    joinMeasure_apply _ _ ((measurable_descend (l := l) (r := r) true hS).inter
      (measurableSet_prefixEqEvent_singleton true)),
    preimage_consFlip_descend, preimage_consFlip_descend]
  simp

lemma branchMeasure_joinMeasure_false {l r : ProbTree α}
    (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) :
    branchMeasure (l := l) (r := r) false (joinMeasure μₗ μᵣ) = μᵣ := by
  refine measure_ext (fun S hS ↦ ?_)
  rw [branchMeasure_apply' false _ hS,
    joinMeasure_apply _ _ ((measurable_descend (l := l) (r := r) false hS).inter
      (measurableSet_prefixEqEvent_singleton false)),
    preimage_consFlip_descend, preimage_consFlip_descend]
  simp


/-! ### `step'` ignores its path, and fixes finished trees -/

lemma step'_path_irrel : ∀ (t : ProbTree α) (μ : Measure[t.ms] Ω) (p p' : BoolSeq),
    step' p ⟨t, μ⟩ = step' p' ⟨t, μ⟩ := by
  intro t
  induction t with
  | leaf m =>
    intro μ p p'
    cases m <;> rw [step', step']
  | node l r ihl ihr =>
    intro μ p p'
    rw [step', step', ihl _ (p ++ [true]) (p' ++ [true]), ihr _ (p ++ [false]) (p' ++ [false])]

lemma step'_of_done : ∀ (t : ProbTree α) (μ : Measure[t.ms] Ω) (p : BoolSeq), t.done = true →
    step' p ⟨t, μ⟩ = ⟨t, μ⟩ := by
  intro t
  induction t with
  | leaf m =>
    intro μ p h
    cases m with
    | pure a => rw [step']
    | liftBind a c => simp [done] at h
  | node l r ihl ihr =>
    intro μ p h
    simp only [done, Bool.and_eq_true] at h
    rw [step', ihl _ _ h.1, ihr _ _ h.2]
    simp only [joinMeasure_branchMeasure]

lemma step_of_done {t : TreeWithMeasure α} (h : t.1.done = true) : step t = t := by
  obtain ⟨t, μ⟩ := t
  exact step'_of_done t μ [] h

/-- `fixpoint` may always be unfolded by one `step`, finished or not. -/
lemma fixpoint_step (t : TreeWithMeasure α) : fixpoint t = fixpoint (step t) := by
  by_cases h : t.1.done = true
  · rw [step_of_done h]
  · exact fixpoint_of_not_done (by simpa using h)

lemma step_node {l r : ProbTree α} (ν : Measure[(ProbTree.node l r).ms] Ω) :
    step ⟨.node l r, ν⟩
      = ⟨.node (step ⟨l, branchMeasure true ν⟩).1 (step ⟨r, branchMeasure false ν⟩).1,
         joinMeasure (step ⟨l, branchMeasure true ν⟩).2
                     (step ⟨r, branchMeasure false ν⟩).2⟩ := by
  rw [step, step'_node, step'_path_irrel _ _ ([] ++ [true]) [],
    step'_path_irrel _ _ ([] ++ [false]) []]
  rfl

/-! ### `fixpoint` on a node, and under scaling -/

lemma done_of_depth_eq_zero : ∀ (t : ProbTree α), t.depth = 0 → t.done = true := by
  intro t
  induction t with
  | leaf m =>
    cases m with
    | pure a => intro _; rfl
    | liftBind a c => intro h; simp [depth, leafDepth] at h
  | node l r ihl ihr =>
    intro h
    simp only [depth, Nat.max_eq_zero_iff] at h
    simp [done, ihl h.1, ihr h.2]

lemma fixpoint_node_aux : ∀ (d : ℕ) (l r : ProbTree α) (ν : Measure[(ProbTree.node l r).ms] Ω),
    (ProbTree.node l r).depth ≤ d →
    fixpoint ⟨.node l r, ν⟩
      = ⟨.node (fixpoint ⟨l, branchMeasure true ν⟩).1 (fixpoint ⟨r, branchMeasure false ν⟩).1,
         joinMeasure (fixpoint ⟨l, branchMeasure true ν⟩).2
                     (fixpoint ⟨r, branchMeasure false ν⟩).2⟩ := by
  have hdoneCase : ∀ (l r : ProbTree α) (ν : Measure[(ProbTree.node l r).ms] Ω),
      (ProbTree.node l r).done = true →
      fixpoint ⟨.node l r, ν⟩
        = ⟨.node (fixpoint ⟨l, branchMeasure true ν⟩).1 (fixpoint ⟨r, branchMeasure false ν⟩).1,
           joinMeasure (fixpoint ⟨l, branchMeasure true ν⟩).2
                       (fixpoint ⟨r, branchMeasure false ν⟩).2⟩ := by
    intro l r ν hdone
    have h := hdone
    simp only [done, Bool.and_eq_true] at h
    rw [fixpoint_of_done hdone, fixpoint_of_done h.1, fixpoint_of_done h.2,
      joinMeasure_branchMeasure]
  intro d
  induction d with
  | zero =>
    intro l r ν hd
    exact hdoneCase l r ν (done_of_depth_eq_zero _ (Nat.le_zero.mp hd))
  | succ d ih =>
    intro l r ν hd
    by_cases hdone : (ProbTree.node l r).done = true
    · exact hdoneCase l r ν hdone
    · have hlt : (ProbTree.node (step ⟨l, branchMeasure true ν⟩).1
          (step ⟨r, branchMeasure false ν⟩).1).depth ≤ d := by
        have h1 : (step ⟨l, branchMeasure true ν⟩).1 = l.split := step_fst
        have h2 : (step ⟨r, branchMeasure false ν⟩).1 = r.split := step_fst
        have h3 := depth_split_lt (ProbTree.node l r) (by simpa using hdone)
        have h4 : ProbTree.node (step ⟨l, branchMeasure true ν⟩).1
            (step ⟨r, branchMeasure false ν⟩).1 = (ProbTree.node l r).split := by
          rw [h1, h2]; rfl
        rw [h4]
        omega
      rw [fixpoint_step ⟨.node l r, ν⟩, step_node, ih _ _ _ hlt,
        branchMeasure_joinMeasure_true, branchMeasure_joinMeasure_false,
        ← fixpoint_step ⟨l, branchMeasure true ν⟩, ← fixpoint_step ⟨r, branchMeasure false ν⟩]

/-- `fixpoint` on a node is the node of the `fixpoint`s of its two halves. -/
lemma fixpoint_node {l r : ProbTree α} (ν : Measure[(ProbTree.node l r).ms] Ω) :
    fixpoint ⟨.node l r, ν⟩
      = ⟨.node (fixpoint ⟨l, branchMeasure true ν⟩).1 (fixpoint ⟨r, branchMeasure false ν⟩).1,
         joinMeasure (fixpoint ⟨l, branchMeasure true ν⟩).2
                     (fixpoint ⟨r, branchMeasure false ν⟩).2⟩ :=
  fixpoint_node_aux _ l r ν le_rfl

lemma map!_smul {m₁ m₂ : MeasurableSpace Ω} (k : ℝ≥0∞) {f : Ω → Ω}
    (hf : Measurable[m₁, m₂] f) (μ : Measure[m₁] Ω) :
    Measure.map! m₁ m₂ f (k • μ) = k • Measure.map! m₁ m₂ f μ := by
  refine measure_ext (fun E hE ↦ ?_)
  rw [map!_apply hf _ hE, Measure.smul_apply, Measure.smul_apply, map!_apply hf _ hE]

lemma branchMeasure_smul {l r : ProbTree α} (b : Bool) (k : ℝ≥0∞)
    (ν : Measure[(ProbTree.node l r).ms] Ω) :
    branchMeasure b (k • ν) = k • branchMeasure b ν := by
  rw [branchMeasure, branchMeasure, Measure.restrict_smul, map!_smul k (measurable_descend b)]

lemma joinMeasure_smul {l r : ProbTree α} (k : ℝ≥0∞)
    (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) :
    joinMeasure (k • μₗ) (k • μᵣ) = k • joinMeasure μₗ μᵣ := by
  rw [joinMeasure, joinMeasure, map!_smul k (measurable_consFlip (l := l) (r := r) true),
    map!_smul k (measurable_consFlip (l := l) (r := r) false), smul_add]

lemma step'_smul (k : ℝ≥0∞) : ∀ (t : ProbTree α) (μ : Measure[t.ms] Ω) (p : BoolSeq),
    step' p ⟨t, k • μ⟩ = ⟨(step' p ⟨t, μ⟩).1, k • (step' p ⟨t, μ⟩).2⟩ := by
  intro t
  induction t with
  | leaf m =>
    intro μ p
    cases m with
    | pure a => rw [step', step']
    | liftBind a c =>
      rw [step', step']
      simp only [Measure.smul_apply, smul_eq_mul, smul_smul]
  | node l r ihl ihr =>
    intro μ p
    rw [step', step', branchMeasure_smul, branchMeasure_smul, ihl, ihr]
    simp only [joinMeasure_smul]

lemma step_smul (k : ℝ≥0∞) (t : ProbTree α) (μ : Measure[t.ms] Ω) :
    step ⟨t, k • μ⟩ = ⟨(step ⟨t, μ⟩).1, k • (step ⟨t, μ⟩).2⟩ :=
  step'_smul k t μ []

lemma fixpoint_smul_aux (k : ℝ≥0∞) : ∀ (d : ℕ) (t : ProbTree α) (μ : Measure[t.ms] Ω),
    t.depth ≤ d → fixpoint ⟨t, k • μ⟩ = ⟨(fixpoint ⟨t, μ⟩).1, k • (fixpoint ⟨t, μ⟩).2⟩ := by
  intro d
  induction d with
  | zero =>
    intro t μ hd
    have hdone : t.done = true := done_of_depth_eq_zero _ (Nat.le_zero.mp hd)
    rw [fixpoint_of_done hdone, fixpoint_of_done hdone]
  | succ d ih =>
    intro t μ hd
    by_cases hdone : t.done = true
    · rw [fixpoint_of_done hdone, fixpoint_of_done hdone]
    · have hlt : (step ⟨t, μ⟩).1.depth ≤ d := by
        have h1 : (step ⟨t, μ⟩).1 = t.split := step_fst
        have := depth_split_lt t (by simpa using hdone)
        rw [h1]; omega
      rw [fixpoint_step ⟨t, k • μ⟩, fixpoint_step ⟨t, μ⟩, step_smul, ih _ _ hlt]

/-- Scaling the measure a tree starts with scales the one it ends with. -/
lemma fixpoint_smul (k : ℝ≥0∞) {t : ProbTree α} (μ : Measure[t.ms] Ω) :
    fixpoint ⟨t, k • μ⟩ = ⟨(fixpoint ⟨t, μ⟩).1, k • (fixpoint ⟨t, μ⟩).2⟩ :=
  fixpoint_smul_aux k _ t μ le_rfl

/-- A leaf has read nothing, so a measure on it is pinned down by its total mass. -/
lemma measure_leaf_ext {m : BernoulliM α} {μ ν : Measure[(ProbTree.leaf m).ms] Ω}
    (h : μ Set.univ = ν Set.univ) : μ = ν := by
  refine measure_ext (fun E hE ↦ ?_)
  rw [ms_leaf] at hE
  rcases MeasurableSpace.measurableSet_bot_iff.mp hE with rfl | rfl
  · simp
  · exact h

/-! ### Composing `Reports` -/

lemma reports_node {l r : ProbTree α} {gt gf : Ω → α} (hl : Reports l gt) (hr : Reports r gf) :
    Reports (ProbTree.node l r) (fun ρ ↦ if ρ 0 then gt (shift ρ) else gf (shift ρ)) := by
  intro q hq ρ hρ
  rcases mem_prefixes_node_iff.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
  · rw [mem_prefixEqEvent_cons] at hρ
    simp only [hρ.1, ↓reduceIte]
    exact hl q' hq' (shift ρ) hρ.2
  · rw [mem_prefixEqEvent_cons] at hρ
    simp only [hρ.1, Bool.false_eq_true, ↓reduceIte]
    exact hr q' hq' (shift ρ) hρ.2

lemma preimage_consFlip_ite (b : Bool) {β : Type} (gt gf : Ω → β) (S : Set β) :
    consFlip b ⁻¹' ((fun ρ ↦ if ρ 0 then gt (shift ρ) else gf (shift ρ)) ⁻¹' S)
      = (if b then gt else gf) ⁻¹' S := by
  ext ρ
  cases b <;> simp [Set.mem_preimage]

lemma joinMeasure_smul_preimage {l r : ProbTree α} {β : Type} (kt kf : ℝ≥0∞)
    (μₗ : Measure[l.ms] Ω) (μᵣ : Measure[r.ms] Ω) {g gt gf : Ω → β} {S : Set β}
    (hT : consFlip true ⁻¹' (g ⁻¹' S) = gt ⁻¹' S)
    (hF : consFlip false ⁻¹' (g ⁻¹' S) = gf ⁻¹' S)
    (hE : MeasurableSet[(ProbTree.node l r).ms] (g ⁻¹' S)) :
    joinMeasure (kt • μₗ) (kf • μᵣ) (g ⁻¹' S) = kt * μₗ (gt ⁻¹' S) + kf * μᵣ (gf ⁻¹' S) := by
  rw [joinMeasure_apply _ _ hE, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    hT, hF]

end Reading

end ProbTree

section Reading

open ProbTree

variable {α : Type}

/-- The atom a tape lands in is the event of the path it follows, so the path `ofTree` chose
for it is that path. -/
lemma choose_atomOf_eq {W : TreeWithMeasure α} [IsProbabilityMeasure W.2]
    {q : BoolSeq} (hq : q ∈ W.1.prefixes) {ρ : Ω} (hρ : ρ ∈ prefixEqEvent q) :
    ((ofTree W).atomOf ρ).2.choose = q := by
  obtain ⟨q', hq0, hq1, hq2⟩ :
      ∃ q', ((ofTree W).atomOf ρ).2.choose = q' ∧ q' ∈ W.1.prefixes
        ∧ prefixEqEvent q' = ((ofTree W).atomOf ρ).1 :=
    ⟨_, rfl, ((ofTree W).atomOf ρ).2.choose_spec.1, ((ofTree W).atomOf ρ).2.choose_spec.2⟩
  rw [hq0]
  have hρ' : ρ ∈ prefixEqEvent q' := by
    rw [hq2]; exact ProbSpace.BoundedFootprintPsp.mem_atomOf _ ρ
  rcases prefix_or_prefix_of_mem hρ hρ' with h | h
  · exact (prefixFree W.1 hq hq1 h).symm
  · exact prefixFree W.1 hq1 hq h

/-- The unit footprint has a single atom, read to depth `0`, so `toTree` stops at the root:
the whole program sits at a single leaf. -/
lemma toTree_one (m : BernoulliM α) :
    toTree (1 : BoundedFootprintPsp) (fun _ ↦ m) = ProbTree.leaf m := by
  rw [toTree, toTree.go]
  rw [dite_eq_left (⟨⟨Set.univ, rfl⟩, List.prefix_refl _⟩ :
    ∃ X : (1 : BoundedFootprintPsp).atoms, (1 : BoundedFootprintPsp).prefixes X <+: [])]

/-- The whole program at the root of a one-leaf tree, carrying the unit space's measure:
where `bigStep` starts from when the footprint is the unit, which is what `interp_psp`
passes it. -/
@[reducible]
noncomputable def rootTree (m : BernoulliM α) : TreeWithMeasure α :=
  ⟨ProbTree.leaf m,
    (ProbSpace.ValidPSp.toPSpace
      ⟨(1 : BoundedFootprintPsp).psp, ProbSpace.BoundedFootprintPsp.valid_one⟩).μ.cast
        (ProbTree.leaf m).ms⟩

@[simp]
lemma rootTree_fst (m : BernoulliM α) : (rootTree m).1 = ProbTree.leaf m := rfl

/-- A leaf has read nothing, so its σ-algebra is trivial and the cast off the unit space
keeps the total mass. -/
lemma rootTree_univ (m : BernoulliM α) : (rootTree m).2 Set.univ = 1 := by
  have hf : Measurable[⊥, (ProbTree.leaf m).ms] id := by
    rw [ProbTree.ms_leaf]; exact measurable_id
  exact (ProbTree.map!_univ hf _).trans (PSpace.unit : PSpace Ω).2.measure_univ

instance rootTree_isProbabilityMeasure (m : BernoulliM α) :
    IsProbabilityMeasure (rootTree m).2 :=
  ⟨rootTree_univ m⟩

/-- `outputPSp` on an explicit pair. -/
lemma outputPSp_mk {b : BoundedFootprintPsp} (f : b.atoms → α) :
    outputPSp ⟨b, f⟩ = PSp.map (fun ρ ↦ f (b.atomOf ρ)) b.psp := rfl

/-- The body of `bigStep`, with the tree it ran to abstracted.  Stating it this way is what
lets `outputPSp_interp` rewrite `toTree` away: the tree appears in the type of `ofTree`'s
instance argument, so it cannot be rewritten in place. -/
lemma outputPSp_bigStep_body (W : TreeWithMeasure α) (hW : IsProbabilityMeasure W.2)
    (hd : W.1.done = true) {t : ProbTree α} {μ : Measure[t.ms] Ω} [hμ : IsProbabilityMeasure μ]
    (hWt : W = ⟨t, μ⟩) {g : Ω → α} (hg : ProbTree.Reports t g) :
    outputPSp (⟨@ofTree α W hW, fun X ↦ (W.1.followTape X.2.choose).get
        (followTape_isSome hd X.2.choose_spec.1)⟩ : Σ b : BoundedFootprintPsp, b.atoms → α)
      = .some (PSpace.map g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω)) := by
  subst hWt
  have := hW
  have hval : ∀ ρ : Ω, ∀ h : (t.followTape (((@ofTree α ⟨t, μ⟩ hW).atomOf ρ)).2.choose).isSome,
      (t.followTape (((@ofTree α ⟨t, μ⟩ hW).atomOf ρ)).2.choose).get h = g ρ := by
    intro ρ h
    obtain ⟨q, hq, hρq⟩ := exists_prefix_mem t ρ
    apply Option.some_injective
    rw [Option.some_get, choose_atomOf_eq (W := ⟨t, μ⟩) hq hρq]
    exact hg q hq ρ hρq
  rw [outputPSp_mk]
  simp only [hval]
  rfl

/-- **The interpretation of a program**, in terms of the finished tree it runs to: if
`fixpoint` takes `m` to `t` carrying `μ`, and `t` reports `g`, then `m`'s output space is
`μ` pushed forward along `g`. -/
lemma outputPSp_interp [Inhabited α] (m : BernoulliM α)
    {t : ProbTree α} {μ : Measure[t.ms] Ω} [hμ : IsProbabilityMeasure μ]
    (hW : fixpoint (rootTree m) = ⟨t, μ⟩) {g : Ω → α} (hg : ProbTree.Reports t g) :
    outputPSp (interp_psp m) = .some (PSpace.map g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω)) := by
  rw [interp_psp_def, bigStep, dite_eq_left ProbSpace.BoundedFootprintPsp.valid_one]
  refine outputPSp_bigStep_body _ _ fixpoint_done ?_ hg
  rw [toTree_one]
  exact hW

/-! ### Identifying the pushforward -/

/-- A reported value's pushforward is pinned down by its point masses. -/
lemma map_eq_of_singletons {β : Type} [Countable β] {t : ProbTree α} {μ : Measure[t.ms] Ω}
    [hμ : IsProbabilityMeasure μ] {g : Ω → β}
    (hmeas : ∀ S : Set β, MeasurableSet[t.ms] (g ⁻¹' S))
    {P : PSpace β} (hP : P.ms = ⊤) (h : ∀ a, μ (g ⁻¹' {a}) = P.μ {a}) :
    PSpace.map g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω) = P := by
  refine PSpace.ext_of_ms_top (PSpace.map_ms_eq_top hmeas) hP (fun a ↦ ?_)
  rw [PSpace.map_apply g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω) (hmeas {a})]
  exact h a

/-- Two programs are indistinguishable as soon as their point masses agree. -/
lemma map_eq_map_of_singletons {α' β : Type} [Countable β]
    {t : ProbTree α} {μ : Measure[t.ms] Ω} [hμ : IsProbabilityMeasure μ] {g : Ω → β}
    {t' : ProbTree α'} {μ' : Measure[t'.ms] Ω} [hμ' : IsProbabilityMeasure μ'] {g' : Ω → β}
    (hmeas : ∀ S : Set β, MeasurableSet[t.ms] (g ⁻¹' S))
    (hmeas' : ∀ S : Set β, MeasurableSet[t'.ms] (g' ⁻¹' S))
    (h : ∀ a, μ (g ⁻¹' {a}) = μ' (g' ⁻¹' {a})) :
    PSpace.map g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω)
      = PSpace.map g' (⟨⟨t'.ms, μ'⟩, hμ'⟩ : PSpace Ω) := by
  refine PSpace.ext_of_ms_top (PSpace.map_ms_eq_top hmeas) (PSpace.map_ms_eq_top hmeas')
    (fun a ↦ ?_)
  rw [PSpace.map_apply g (⟨⟨t.ms, μ⟩, hμ⟩ : PSpace Ω) (hmeas {a}),
    PSpace.map_apply g' (⟨⟨t'.ms, μ'⟩, hμ'⟩ : PSpace Ω) (hmeas' {a})]
  exact h a

lemma bernoulli_μ_singleton (p : I) (b : Bool) :
    (PSpace.bernoulli p).μ {b} = ProbTree.flipWeight p b := by
  cases b
  · exact PSpace.bernoulli_μ_false
  · exact PSpace.bernoulli_μ_true

lemma preimage_head (a : Bool) : (fun ρ : Ω ↦ ρ 0) ⁻¹' {a} = ProbTree.prefixEqEvent [a] := by
  ext ρ; simp [ProbTree.mem_prefixEqEvent_singleton]

lemma preimage_pair (x y : Bool) :
    (fun ρ : Ω ↦ (ρ 0, ρ 1)) ⁻¹' {(x, y)} = ProbTree.prefixEqEvent [x, y] := by
  ext ρ; simp [ProbTree.mem_prefixEqEvent_pair, Prod.ext_iff]

/-! ### One flip -/

/-- Peeling the first flip off the root. -/
lemma step_rootTree_liftBind (a : BernoulliPFunctor.A)
    (c : BernoulliPFunctor.B a → BernoulliM α) :
    step (rootTree (PFunctor.FreeM.liftBind a c))
      = ⟨.node (.leaf (c true)) (.leaf (c false)), flipMeasure _ a.1⟩ := by
  have h : step (rootTree (PFunctor.FreeM.liftBind a c))
      = ⟨.node (.leaf (c true)) (.leaf (c false)),
         (rootTree (PFunctor.FreeM.liftBind a c)).2 Set.univ • flipMeasure _ a.1⟩ :=
    ProbTree.step'_leaf_liftBind [] a c _
  rw [h, measure_univ, one_smul]

/-- The tree a single flip runs to, reporting `v b` on the `b` branch. -/
abbrev oneFlipTree (v : Bool → α) : ProbTree α :=
  .node (.leaf (.pure (v true))) (.leaf (.pure (v false)))

lemma fixpoint_oneFlip (v : Bool → α) (p : I) :
    fixpoint (rootTree (PFunctor.FreeM.liftBind (BernoulliOps.Flip p) (fun b ↦ .pure (v b))))
      = ⟨oneFlipTree v, flipMeasure (oneFlipTree v).ms p⟩ := by
  rw [ProbTree.fixpoint_of_not_done rfl, step_rootTree_liftBind, ProbTree.fixpoint_of_done rfl]

lemma reports_oneFlipTree (v : Bool → α) :
    ProbTree.Reports (oneFlipTree v) (fun ρ : Ω ↦ v (ρ 0)) := by
  intro q hq ρ hρ
  rcases ProbTree.mem_prefixes_node_leaf.mp hq with rfl | rfl <;>
    rw [ProbTree.mem_prefixEqEvent_singleton] at hρ <;> simp only [hρ] <;> rfl

/-! ### Two flips -/

/-- The tree two flips run to, reporting `v b₀ b₁`. -/
abbrev twoFlipTree (v : Bool → Bool → α) : ProbTree α :=
  .node (oneFlipTree (v true)) (oneFlipTree (v false))

/-- The measure two flips, of biases `p` then `q`, put on that tree. -/
noncomputable def twoFlipMeasure (v : Bool → Bool → α) (p q : I) :
    Measure[(twoFlipTree v).ms] Ω :=
  joinMeasure (ProbTree.flipWeight p true • flipMeasure (oneFlipTree (v true)).ms q)
              (ProbTree.flipWeight p false • flipMeasure (oneFlipTree (v false)).ms q)

instance twoFlipMeasure_isProbabilityMeasure {v : Bool → Bool → α} {p q : I} :
    IsProbabilityMeasure (twoFlipMeasure v p q) where
  measure_univ := by
    rw [twoFlipMeasure, joinMeasure_univ, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ProbTree.flipWeight_add]

lemma fixpoint_twoFlips (v : Bool → Bool → α) (p q : I) :
    fixpoint (rootTree (PFunctor.FreeM.liftBind (BernoulliOps.Flip p)
        (fun b₀ ↦ PFunctor.FreeM.liftBind (BernoulliOps.Flip q) (fun b₁ ↦ .pure (v b₀ b₁)))))
      = ⟨twoFlipTree v, twoFlipMeasure v p q⟩ := by
  rw [ProbTree.fixpoint_of_not_done rfl, step_rootTree_liftBind,
    ProbTree.fixpoint_of_not_done rfl, step, ProbTree.step'_node,
    ProbTree.step'_leaf_liftBind _ (BernoulliOps.Flip q) _ _,
    ProbTree.step'_leaf_liftBind _ (BernoulliOps.Flip q) _ _, ProbTree.fixpoint_of_done rfl,
    branchMeasure_univ, branchMeasure_univ,
    ProbTree.flipMeasure_apply_singleton p true (measurableSet_prefixEqEvent_singleton true),
    ProbTree.flipMeasure_apply_singleton p false (measurableSet_prefixEqEvent_singleton false)]
  rfl

lemma reports_twoFlipTree (v : Bool → Bool → α) :
    ProbTree.Reports (twoFlipTree v) (fun ρ : Ω ↦ v (ρ 0) (ρ 1)) := by
  intro s hs ρ hρ
  rcases ProbTree.mem_prefixes_node_iff.mp hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩ <;>
    rcases ProbTree.mem_prefixes_node_leaf.mp hs' with rfl | rfl <;>
    rw [ProbTree.mem_prefixEqEvent_pair] at hρ <;> simp only [hρ.1, hρ.2] <;> rfl

lemma mem_prefixes_twoFlipTree {v : Bool → Bool → α} {b₀ b₁ : Bool} :
    [b₀, b₁] ∈ (twoFlipTree v).prefixes := by
  rw [ProbTree.mem_prefixes_node_iff]
  cases b₀ <;> cases b₁ <;> simp [ProbTree.prefixes]

lemma twoFlipMeasure_apply (v : Bool → Bool → α) (p q : I) (b₀ b₁ : Bool) :
    twoFlipMeasure v p q (ProbTree.prefixEqEvent [b₀, b₁])
      = ProbTree.flipWeight p b₀ * ProbTree.flipWeight q b₁ := by
  rw [twoFlipMeasure,
    ProbTree.joinMeasure_apply_cons _ _ b₀ (q := [b₁])
      (by cases b₀ <;> cases b₁ <;> simp [ProbTree.prefixes])]
  cases b₀ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Measure.smul_apply, smul_eq_mul] <;>
    rw [ProbTree.flipMeasure_apply_singleton q b₁ (measurableSet_prefixEqEvent_singleton b₁)]

/-! ### Peeling the first flip off a program

The equations above run a program of *known* shape.  To run one given by a recursion, the
tree has to be taken apart one flip at a time instead: `fixpoint_rootTree_liftBind` says the
whole run is the node of the two continuations' runs, each scaled by that flip's weight. -/

/-- The result of running a program is a probability measure. -/
lemma isProbabilityMeasure_of_fixpoint {m : BernoulliM α} {t : ProbTree α} {μ : Measure[t.ms] Ω}
    (h : fixpoint (rootTree m) = ⟨t, μ⟩) : IsProbabilityMeasure μ := by
  have hinst : IsProbabilityMeasure (fixpoint (rootTree m)).2 := inferInstance
  rw [h] at hinst
  exact hinst

lemma fixpoint_rootTree_pure (a : α) :
    fixpoint (rootTree (PFunctor.FreeM.pure a : BernoulliM α))
      = ⟨.leaf (.pure a), (rootTree (PFunctor.FreeM.pure a : BernoulliM α)).2⟩ :=
  fixpoint_of_done rfl

lemma reports_leaf_pure (a : α) :
    ProbTree.Reports (ProbTree.leaf (PFunctor.FreeM.pure a : BernoulliM α)) (fun _ ↦ a) := by
  intro q hq ρ _
  rw [ProbTree.mem_prefixes_leaf.mp hq]
  rfl

/-- A node whose two halves carry scaled measures: `fixpoint` scales right through. -/
lemma fixpoint_node_smul {lt rt : ProbTree α} (kt kf : ℝ≥0∞)
    {νt : Measure[lt.ms] Ω} {νf : Measure[rt.ms] Ω}
    (ν : Measure[(ProbTree.node lt rt).ms] Ω)
    (hT : branchMeasure (l := lt) (r := rt) true ν = kt • νt)
    (hF : branchMeasure (l := lt) (r := rt) false ν = kf • νf) :
    fixpoint ⟨.node lt rt, ν⟩
      = ⟨.node (fixpoint ⟨lt, νt⟩).1 (fixpoint ⟨rt, νf⟩).1,
         joinMeasure (kt • (fixpoint ⟨lt, νt⟩).2) (kf • (fixpoint ⟨rt, νf⟩).2)⟩ := by
  rw [fixpoint_node, hT, hF, fixpoint_smul, fixpoint_smul]

/-- **Peeling the first flip.**  A program that starts with a flip runs to the node of what
its two continuations run to, each branch scaled by that flip's weight. -/
lemma fixpoint_rootTree_liftBind (a : BernoulliPFunctor.A)
    (c : BernoulliPFunctor.B a → BernoulliM α) :
    fixpoint (rootTree (PFunctor.FreeM.liftBind a c))
      = ⟨.node (fixpoint (rootTree (c true))).1 (fixpoint (rootTree (c false))).1,
         joinMeasure (ProbTree.flipWeight a.1 true • (fixpoint (rootTree (c true))).2)
                     (ProbTree.flipWeight a.1 false • (fixpoint (rootTree (c false))).2)⟩ := by
  have hb : ∀ b : Bool,
      (ProbTree.flipWeight a.1 b • (rootTree (c b)).2) Set.univ = ProbTree.flipWeight a.1 b := by
    intro b
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have hT : branchMeasure (l := ProbTree.leaf (c true)) (r := ProbTree.leaf (c false)) true
      (flipMeasure (ProbTree.node (ProbTree.leaf (c true)) (ProbTree.leaf (c false))).ms a.1)
      = ProbTree.flipWeight a.1 true • (rootTree (c true)).2 := by
    refine measure_leaf_ext ?_
    rw [branchMeasure_univ, ProbTree.flipMeasure_apply_singleton a.1 true
      (measurableSet_prefixEqEvent_singleton true)]
    exact (hb true).symm
  have hF : branchMeasure (l := ProbTree.leaf (c true)) (r := ProbTree.leaf (c false)) false
      (flipMeasure (ProbTree.node (ProbTree.leaf (c true)) (ProbTree.leaf (c false))).ms a.1)
      = ProbTree.flipWeight a.1 false • (rootTree (c false)).2 := by
    refine measure_leaf_ext ?_
    rw [branchMeasure_univ, ProbTree.flipMeasure_apply_singleton a.1 false
      (measurableSet_prefixEqEvent_singleton false)]
    exact (hb false).symm
  refine (fixpoint_step (rootTree _)).trans ?_
  rw [step_rootTree_liftBind]
  exact fixpoint_node_smul _ _ _ hT hF

/-- `fixpoint_rootTree_liftBind` with the two continuations named. -/
lemma fixpoint_rootTree_liftBind₂ (a : BernoulliPFunctor.A)
    (c : BernoulliPFunctor.B a → BernoulliM α) (ct cf : BernoulliM α)
    (hct : c true = ct) (hcf : c false = cf) :
    fixpoint (rootTree (PFunctor.FreeM.liftBind a c))
      = ⟨.node (fixpoint (rootTree ct)).1 (fixpoint (rootTree cf)).1,
         joinMeasure (ProbTree.flipWeight a.1 true • (fixpoint (rootTree ct)).2)
                     (ProbTree.flipWeight a.1 false • (fixpoint (rootTree cf)).2)⟩ := by
  subst hct
  subst hcf
  exact fixpoint_rootTree_liftBind a c

end Reading

/-! ## Running a program that reads nothing

`toTree` turns the footprint into a tree with a leaf per atom, so it neither loses nor
invents σ-algebra: `toTree_ms_eq`.  If on top of that the tree is already `done` -- which is
exactly the case for the constant program `pure x` -- `fixpoint` is the identity, so the run
hands the footprint's space straight back (`bigStep_psp_of_done`) and every atom reports `x`
(`result_bigStep_of_done`).  Together these are what `CWPPure` needs. -/

section Pure

open ProbSpace MeasureTheory ProbTree BoundedFootprintPsp

variable {α : Type}

/-- Every atom's prefix really is a root-to-leaf path of the tree: `toTree.go` stops only
once it has reached one, and it does reach every one. -/
lemma toTree_go_mem_prefixes (bfpsp : BoundedFootprintPsp)
    (programs : bfpsp.atoms → BernoulliM α) (path : BoolSeq) (X : bfpsp.atoms) :
    path <+: bfpsp.prefixes X →
    (bfpsp.prefixes X).drop path.length ∈ (toTree.go bfpsp programs path).prefixes := by
  induction path using toTree.go.induct bfpsp with
  | case1 path leafy =>
    intro h
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    obtain ⟨Y, hY⟩ := leafy
    have hYX : Y = X := by
      by_contra hne
      exact bfpsp.pathInTreeValid Y X hne (hY.trans h)
    subst hYX
    have heq : path = bfpsp.prefixes Y :=
      h.eq_of_length (le_antisymm h.length_le hY.length_le)
    rw [← heq, List.drop_length]
    simp
  | case2 path leafy ihl ihr =>
    intro h
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    obtain ⟨t, ht⟩ := h
    have hne : t ≠ [] := by
      rintro rfl
      exact leafy ⟨X, by simp at ht; rw [← ht]⟩
    obtain ⟨b, t', rfl⟩ : ∃ b t', t = b :: t' := by
      cases t with
      | nil => exact absurd rfl hne
      | cons b t' => exact ⟨b, t', rfl⟩
    have hpre : path ++ [b] <+: bfpsp.prefixes X := ⟨t', by rw [← ht]; simp⟩
    have hdrop : (bfpsp.prefixes X).drop path.length = b :: t' := by rw [← ht]; simp
    have hdrop' : (bfpsp.prefixes X).drop (path ++ [b]).length = t' := by rw [← ht]; simp
    rw [hdrop]
    refine mem_prefixes_node b ?_
    cases b
    · simpa [← hdrop'] using ihr hpre
    · simpa [← hdrop'] using ihl hpre

lemma mem_prefixes_toTree (bfpsp : BoundedFootprintPsp)
    (programs : bfpsp.atoms → BernoulliM α) (X : bfpsp.atoms) :
    bfpsp.prefixes X ∈ (toTree bfpsp programs).prefixes := by
  rw [toTree]
  simpa using toTree_go_mem_prefixes bfpsp programs [] X List.nil_prefix

/-- The tree's σ-algebra is exactly the footprint's: `toTree_ms_le` is one inclusion, and
every atom is the event of its own prefix, which the tree has. -/
lemma toTree_ms_eq (bfpsp : BoundedFootprintPsp) (programs : bfpsp.atoms → BernoulliM α) :
    (toTree bfpsp programs).ms = MeasurableSpace.generateFrom bfpsp.atoms := by
  refine le_antisymm (toTree_ms_le bfpsp programs) (MeasurableSpace.generateFrom_le ?_)
  intro S hS
  rw [show S = _ from atom_eq_prefixEqEvent bfpsp ⟨S, hS⟩]
  exact measurableSet_prefixEqEvent (mem_prefixes_toTree bfpsp programs ⟨S, hS⟩)

/-- A tree whose every leaf is `pure x` has nothing left to run. -/
lemma toTree_go_pure_done (bfpsp : BoundedFootprintPsp) (x : α) (path : BoolSeq) :
    (toTree.go bfpsp (fun _ ↦ (.pure x : BernoulliM α)) path).done = true := by
  induction path using toTree.go.induct bfpsp with
  | case1 path leafy =>
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    rfl
  | case2 path leafy ihl ihr =>
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte, ProbTree.done, Bool.and_eq_true]
    exact ⟨ihl, ihr⟩

lemma toTree_pure_done (bfpsp : BoundedFootprintPsp) (x : α) :
    (toTree bfpsp (fun _ ↦ (.pure x : BernoulliM α))).done = true := by
  rw [toTree]; exact toTree_go_pure_done bfpsp x []

/-- Every root-to-leaf path of such a tree reports `x`. -/
lemma followTape_toTree_go_pure (bfpsp : BoundedFootprintPsp) (x : α) (path : BoolSeq) :
    ∀ q ∈ (toTree.go bfpsp (fun _ ↦ (.pure x : BernoulliM α)) path).prefixes,
      (toTree.go bfpsp (fun _ ↦ (.pure x : BernoulliM α)) path).followTape q = some x := by
  induction path using toTree.go.induct bfpsp with
  | case1 path leafy =>
    intro q _
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    rfl
  | case2 path leafy ihl ihr =>
    intro q hq
    rw [toTree.go] at hq ⊢
    simp only [leafy, ↓reduceDIte] at hq ⊢
    rcases ProbTree.mem_prefixes_node_iff.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · exact ihl q' hq'
    · exact ihr q' hq'

lemma reports_toTree_pure (bfpsp : BoundedFootprintPsp) (x : α) :
    ProbTree.Reports (toTree bfpsp (fun _ ↦ (.pure x : BernoulliM α))) (fun _ ↦ x) := by
  intro q hq ρ _
  rw [toTree] at hq ⊢
  exact followTape_toTree_go_pure bfpsp x [] q hq

/-- `ofTree`'s space, with the tree it was built from named: the instance argument sits in
`W`'s type, so it cannot be rewritten in place. -/
lemma ofTree_psp [Inhabited α] (W : TreeWithMeasure α) (hW : IsProbabilityMeasure W.2)
    {t : ProbTree α} {μ : Measure[t.ms] Ω} [hμ : IsProbabilityMeasure μ] (hWt : W = ⟨t, μ⟩) :
    (@ofTree α W hW).psp = .some ⟨⟨t.ms, μ⟩, hμ⟩ := by
  subst hWt; rfl

/-- **Running a finished program leaves the footprint's space alone.** -/
lemma bigStep_psp_of_done [Inhabited α] (bfpsp : BoundedFootprintPsp)
    (programs : bfpsp.atoms → BernoulliM α) (valid : ✓bfpsp.psp)
    (hdone : (toTree bfpsp programs).done = true) :
    (bigStep bfpsp programs).1.psp = bfpsp.psp := by
  set P : PSpace Ω := ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩ with hP
  have hms : (toTree bfpsp programs).ms = P.ms := by
    rw [toTree_ms_eq, hP, bfpsp.sigmaAgrees valid]
  have hsome : bfpsp.psp = .some P := (Option.some_get _).symm
  rw [bigStep, dite_eq_left valid]
  refine Eq.trans (ofTree_psp _ _ (ProbTree.fixpoint_of_done hdone)) (Eq.trans ?_ hsome.symm)
  congr 1
  exact PSpace.ext_ms hms
    (fun E hE ↦ Measure.le_preserves_measure (h := le_of_eq hms) (μ := P.μ) (hu := hE))

/-- The value a finished run reports, with the tree it ran to named. -/
lemma result_bigStep_body [Inhabited α] (W : TreeWithMeasure α)
    (hW : IsProbabilityMeasure W.2) (hd : W.1.done = true) {g : Ω → α}
    (hg : ProbTree.Reports W.1 g) :
    result (⟨@ofTree α W hW, fun X ↦ (W.1.followTape X.2.choose).get
        (followTape_isSome hd X.2.choose_spec.1)⟩
      : Σ b : BoundedFootprintPsp, b.atoms → α) = g := by
  funext ρ
  show (W.1.followTape ((@ofTree α W hW).atomOf ρ).2.choose).get _ = g ρ
  obtain ⟨q, hq, hρq⟩ := ProbTree.exists_prefix_mem W.1 ρ
  apply Option.some_injective
  rw [Option.some_get, @choose_atomOf_eq α W hW q hq ρ hρq]
  exact hg q hq ρ hρq

lemma result_bigStep_of_done [Inhabited α] (bfpsp : BoundedFootprintPsp)
    (programs : bfpsp.atoms → BernoulliM α) (valid : ✓bfpsp.psp)
    (hdone : (toTree bfpsp programs).done = true) {g : Ω → α}
    (hg : ProbTree.Reports (toTree bfpsp programs) g) :
    result (bigStep bfpsp programs) = g := by
  rw [bigStep, dite_eq_left valid]
  refine result_bigStep_body _ _ ProbTree.fixpoint_done ?_
  rwa [congrArg Sigma.fst (ProbTree.fixpoint_of_done hdone)]

/-- `pure x` does not touch the footprint. -/
lemma run_pure_psp [Inhabited α] {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m]
    (x : α) (μ₀ : BoundedFootprintPsp) (valid : ✓μ₀.psp) :
    (run (pure x : m α) μ₀).1.psp = μ₀.psp := by
  rw [run]
  simp only [LawfulBernoulliInterpretable.interp_pure]
  exact bigStep_psp_of_done μ₀ _ valid (toTree_pure_done μ₀ x)

/-- `pure x` reports `x`, whatever the tape. -/
lemma result_run_pure [Inhabited α] {m : Type → Type} [Monad m]
    [LawfulBernoulliInterpretable m] (x : α) (μ₀ : BoundedFootprintPsp) (valid : ✓μ₀.psp) :
    result (run (pure x : m α) μ₀) = fun _ ↦ x := by
  rw [run]
  simp only [LawfulBernoulliInterpretable.interp_pure]
  exact result_bigStep_of_done μ₀ _ valid (toTree_pure_done μ₀ x) (reports_toTree_pure μ₀ x)

end Pure

/-! ## Running a program from an arbitrary footprint

`flip_dist` and friends run a program from the *unit* footprint, which is all `interp_psp`
needs.  `wp` quantifies over every footprint, so what is needed here is a program run from an
arbitrary one.

`toTree` puts a copy of the program at each atom, so what the run produces is, at each atom,
the same tree carrying the same law.  `run_const` records the three consequences: the output
space refines the input (`ms_le_fixpoint`) and leaves its measure alone
(`fixpoint_preserves`), the value reported is `treeValue`, and that value is distributed as
the program's own law **independently of everything the footprint could already measure**
(`fixpoint_constTree_inter`).  The last is what lets a program's result be owned alongside a
frame. -/

namespace ProbTree

section Program

open ProbSpace MeasureTheory unitInterval BoundedFootprintPsp

noncomputable section

variable {α : Type}

/-- Tapes agreeing with a longer prefix agree with a shorter one. -/
lemma prefixEqEvent_mono {q q' : BoolSeq} (h : q <+: q') :
    prefixEqEvent q' ⊆ prefixEqEvent q := by
  intro ρ hρ i
  have hi : i.1 < q'.length := lt_of_lt_of_le i.2 h.length_le
  rw [hρ ⟨i.1, hi⟩]
  exact (h.getElem i.2).symm

/-- A path splits into its two one-bit extensions. -/
lemma prefixEqEvent_split (q : BoolSeq) :
    prefixEqEvent q = prefixEqEvent (q ++ [true]) ∪ prefixEqEvent (q ++ [false]) := by
  refine Set.Subset.antisymm (fun ρ hρ ↦ ?_) (Set.union_subset
    (prefixEqEvent_mono (List.prefix_append _ _)) (prefixEqEvent_mono (List.prefix_append _ _)))
  have hmem : ∀ b : Bool, ρ q.length = b → ρ ∈ prefixEqEvent (q ++ [b]) := by
    intro b hb i
    rcases lt_or_ge i.1 q.length with hi | hi
    · rw [hρ ⟨i.1, hi⟩]
      simp [List.getElem_append_left hi]
    · have hlen : i.1 = q.length := by have := i.2; simp at this; omega
      have hval : (q ++ [b])[i] = b := by simp [Fin.getElem_fin, hlen]
      rw [hval, hlen]
      exact hb
  cases hb : ρ q.length
  · exact Or.inr (hmem false hb)
  · exact Or.inl (hmem true hb)

/-- Equal trees-with-measure assign equal mass; stated so that `step'`'s and `fixpoint`'s
equations can be used without rewriting under the measure's dependent type. -/
lemma measure_congr_tree {α : Type} {W W' : TreeWithMeasure α} (h : W = W') (G : Set Ω) :
    W.2 G = W'.2 G :=
  congrArg (fun V : TreeWithMeasure α ↦ V.2 G) h

/-- `ofTree`'s space, read off directly. -/
lemma ofTree_psp' {α : Type} [Inhabited α] (W : TreeWithMeasure α)
    (hW : IsProbabilityMeasure W.2) :
    (@ofTree α W hW).psp = .some ⟨⟨W.1.ms, W.2⟩, hW⟩ := rfl

/-- The flip weights are the Bernoulli weights. -/
lemma flipWeight_eq_bernoulliWeights (p : I) (b : Bool) :
    flipWeight p b = bernoulliWeights (toNNReal p) (toNNReal_le_one p) b := by
  rw [bernoulliWeights_apply, flipWeight]
  cases b
  · simp [ENNReal.coe_sub]
  · simp

/-- The value a program reports on a tape: follow the flips the tape dictates. -/
def runValue : BernoulliM α → Ω → α
  | .pure a, _ => a
  | .liftBind _ c, ρ => runValue (c (ρ 0)) (shift ρ)

/-- A tree every leaf of which is the same program. -/
def IsConstTree (m : BernoulliM α) : ProbTree α → Prop
  | .leaf n => n = m
  | .node l r => IsConstTree m l ∧ IsConstTree m r

/-- The value such a tree reports: run `m` on what is left of the tape after the path the
tape took through the tree. -/
def treeValue (m : BernoulliM α) : ProbTree α → Ω → α
  | .leaf _, ρ => runValue m ρ
  | .node l r, ρ => if ρ 0 then treeValue m l (shift ρ) else treeValue m r (shift ρ)

/-- Running a program from a leaf reports `runValue`. -/
lemma reports_fixpoint_rootTree (m : BernoulliM α) :
    Reports (fixpoint (rootTree m)).1 (runValue m) := by
  induction m with
  | pure a =>
    rw [fixpoint_rootTree_pure]
    exact reports_leaf_pure a
  | liftBind op c ih =>
    rw [fixpoint_rootTree_liftBind op c]
    have h := reports_node (ih true) (ih false)
    refine fun q hq ρ hρ ↦ ?_
    have := h q hq ρ hρ
    rw [this]
    cases h0 : ρ 0 <;> simp [runValue, h0]

/-- A leaf carries a measure pinned down by its total mass, so running it is running the
program from the unit footprint, scaled. -/
lemma fixpoint_leaf (m : BernoulliM α) (ν : Measure[(ProbTree.leaf m).ms] Ω) :
    fixpoint ⟨ProbTree.leaf m, ν⟩
      = ⟨(fixpoint (rootTree m)).1, ν Set.univ • (fixpoint (rootTree m)).2⟩ := by
  have hν : ν = ν Set.univ • (rootTree m).2 := by
    refine measure_leaf_ext ?_
    rw [Measure.smul_apply, smul_eq_mul, rootTree_univ, mul_one]
  rw [show (⟨ProbTree.leaf m, ν⟩ : TreeWithMeasure α)
      = ⟨ProbTree.leaf m, ν Set.univ • (rootTree m).2⟩ from by rw [← hν],
    show (⟨ProbTree.leaf m, ν Set.univ • (rootTree m).2⟩ : TreeWithMeasure α)
      = ⟨(rootTree m).1, ν Set.univ • (rootTree m).2⟩ from rfl,
    fixpoint_smul]

/-- Splitting either leaves a path alone (at a finished leaf) or extends it by one bit. -/
lemma mem_prefixes_split_or :
    ∀ {t : ProbTree α} {q : BoolSeq}, q ∈ t.prefixes →
      q ∈ t.split.prefixes ∨ ∀ b : Bool, q ++ [b] ∈ t.split.prefixes := by
  intro t
  induction t with
  | leaf n =>
    intro q hq
    rw [mem_prefixes_leaf.mp hq]
    cases n with
    | pure a => exact Or.inl (by simp [ProbTree.split])
    | liftBind op c =>
      refine Or.inr fun b ↦ ?_
      simpa [ProbTree.split] using mem_prefixes_node_leaf.mpr (by cases b <;> simp)
  | node l r ihl ihr =>
    intro q hq
    rcases mem_prefixes_node_iff.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · rcases ihl hq' with h | h
      · exact Or.inl (mem_prefixes_node true (by simpa using h))
      · exact Or.inr fun b ↦ mem_prefixes_node true (by simpa using h b)
    · rcases ihr hq' with h | h
      · exact Or.inl (mem_prefixes_node false (by simpa using h))
      · exact Or.inr fun b ↦ mem_prefixes_node false (by simpa using h b)

/-- Splitting only refines. -/
lemma ms_le_split (t : ProbTree α) : t.ms ≤ t.split.ms := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨q, hq, rfl⟩
  rcases mem_prefixes_split_or hq with h | h
  · exact measurableSet_prefixEqEvent h
  · rw [prefixEqEvent_split q]
    exact (measurableSet_prefixEqEvent (h true)).union (measurableSet_prefixEqEvent (h false))

/-- Running only refines. -/
lemma ms_le_fixpoint : ∀ (d : ℕ) (t : ProbTree α) (ν : Measure[t.ms] Ω), t.depth ≤ d →
    t.ms ≤ (fixpoint ⟨t, ν⟩).1.ms := by
  intro d
  induction d with
  | zero =>
    intro t ν hd
    rw [fixpoint_of_done (done_of_depth_eq_zero _ (Nat.le_zero.mp hd))]
  | succ d ih =>
    intro t ν hd
    by_cases hdone : t.done = true
    · rw [fixpoint_of_done hdone]
    · have hlt : (step ⟨t, ν⟩).1.depth ≤ d := by
        have h1 : (step ⟨t, ν⟩).1 = t.split := step_fst
        have := depth_split_lt t (by simpa using hdone)
        rw [h1]; omega
      rw [fixpoint_step ⟨t, ν⟩]
      refine le_trans (ms_le_split t) ?_
      rw [← show (step (⟨t, ν⟩ : TreeWithMeasure α)).1 = t.split from step_fst]
      exact ih (step ⟨t, ν⟩).1 (step ⟨t, ν⟩).2 hlt

lemma ms_le_fixpoint' (t : ProbTree α) (ν : Measure[t.ms] Ω) :
    t.ms ≤ (fixpoint ⟨t, ν⟩).1.ms :=
  ms_le_fixpoint t.depth t ν le_rfl

/-- A tree of copies of `m` reports `treeValue m`: the path through the tree, then `m`'s own
report on what is left of the tape. -/
lemma reports_fixpoint_constTree {m : BernoulliM α} :
    ∀ {t : ProbTree α}, IsConstTree m t → ∀ (ν : Measure[t.ms] Ω),
      Reports (fixpoint ⟨t, ν⟩).1 (treeValue m t) := by
  intro t
  induction t with
  | leaf n =>
    rintro rfl ν
    rw [congrArg Sigma.fst (fixpoint_leaf n ν)]
    exact reports_fixpoint_rootTree n
  | node l r ihl ihr =>
    rintro ⟨hl, hr⟩ ν
    rw [congrArg Sigma.fst (fixpoint_node ν)]
    exact reports_node (ihl hl _) (ihr hr _)

/-- **Fresh randomness, from any footprint.**  Running the same program at every leaf makes
the value it reports independent of everything the tree could already measure, with the law
the program has on its own. -/
lemma fixpoint_constTree_inter {m : BernoulliM α} :
    ∀ {t : ProbTree α}, IsConstTree m t → ∀ (ν : Measure[t.ms] Ω) (a : α)
      {E : Set Ω}, MeasurableSet[t.ms] E →
      (fixpoint ⟨t, ν⟩).2 (treeValue m t ⁻¹' {a} ∩ E)
        = (fixpoint (rootTree m)).2 (runValue m ⁻¹' {a}) * ν E := by
  intro t
  induction t with
  | leaf n =>
    rintro rfl ν a E hE
    rw [ms_leaf] at hE
    refine Eq.trans (measure_congr_tree (fixpoint_leaf n ν) _) ?_
    rcases MeasurableSpace.measurableSet_bot_iff.mp hE with rfl | rfl
    · show (ν Set.univ • (fixpoint (rootTree n)).2) _ = _
      simp
    · show (ν Set.univ • (fixpoint (rootTree n)).2) _ = _
      rw [Set.inter_univ, Measure.smul_apply, smul_eq_mul, mul_comm]
      rfl
  | node l r ihl ihr =>
    rintro ⟨hl, hr⟩ ν a E hE
    have hGm : MeasurableSet[(fixpoint (⟨ProbTree.node l r, ν⟩ : TreeWithMeasure α)).1.ms]
        (treeValue m (ProbTree.node l r) ⁻¹' {a} ∩ E) :=
      ((reports_fixpoint_constTree (t := ProbTree.node l r) ⟨hl, hr⟩
          ν).measurableSet_preimage {a}).inter
        (ms_le_fixpoint' (ProbTree.node l r) ν E hE)
    rw [congrArg Sigma.fst (fixpoint_node ν)] at hGm
    refine Eq.trans (measure_congr_tree (fixpoint_node ν) _) ?_
    show joinMeasure _ _ _ = _
    rw [joinMeasure_apply _ _ hGm, Set.preimage_inter, Set.preimage_inter]
    simp only [treeValue, preimage_consFlip_ite, Bool.false_eq_true, ↓reduceIte]
    rw [ihl hl _ a (by simpa using measurable_consFlip (l := l) (r := r) true hE),
      ihr hr _ a (by simpa using measurable_consFlip (l := l) (r := r) false hE),
      ← mul_add, ← joinMeasure_apply _ _ hE, joinMeasure_branchMeasure]

/-! ### Running does not disturb what was already known -/

lemma step'_preserves : ∀ (t : ProbTree α) (ν : Measure[t.ms] Ω) (path : BoolSeq)
    (E : Set Ω), MeasurableSet[t.ms] E → (step' path ⟨t, ν⟩).2 E = ν E := by
  intro t
  induction t with
  | leaf n =>
    intro ν path E hE
    rw [ms_leaf] at hE
    cases n with
    | pure a => exact measure_congr_tree (step'_leaf_pure path a ν) E
    | liftBind op c =>
      refine Eq.trans (measure_congr_tree (step'_leaf_liftBind path op c ν) E) ?_
      rcases MeasurableSpace.measurableSet_bot_iff.mp hE with rfl | rfl
      · show (ν Set.univ • flipMeasure _ op.1) _ = _
        simp
      · show (ν Set.univ • flipMeasure _ op.1) _ = _
        simp
  | node l r ihl ihr =>
    intro ν path E hE
    have hE' : MeasurableSet[(ProbTree.node (step' (path ++ [true])
        (⟨l, branchMeasure true ν⟩ : TreeWithMeasure α)).1
        (step' (path ++ [false]) (⟨r, branchMeasure false ν⟩ : TreeWithMeasure α)).1).ms] E := by
      rw [show ProbTree.node (step' (path ++ [true])
            (⟨l, branchMeasure true ν⟩ : TreeWithMeasure α)).1
          (step' (path ++ [false]) (⟨r, branchMeasure false ν⟩ : TreeWithMeasure α)).1
          = (ProbTree.node l r).split from by rw [step'_fst, step'_fst]; rfl]
      exact ms_le_split (ProbTree.node l r) E hE
    refine Eq.trans (measure_congr_tree (step'_node path ν) E) ?_
    show joinMeasure _ _ _ = _
    rw [joinMeasure_apply _ _ hE',
      ihl _ _ _ (by simpa using measurable_consFlip (l := l) (r := r) true hE),
      ihr _ _ _ (by simpa using measurable_consFlip (l := l) (r := r) false hE),
      ← joinMeasure_apply _ _ hE, joinMeasure_branchMeasure]

lemma fixpoint_preserves : ∀ (d : ℕ) (t : ProbTree α) (ν : Measure[t.ms] Ω), t.depth ≤ d →
    ∀ (E : Set Ω), MeasurableSet[t.ms] E → (fixpoint ⟨t, ν⟩).2 E = ν E := by
  intro d
  induction d with
  | zero =>
    intro t ν hd E hE
    rw [measure_congr_tree (fixpoint_of_done (done_of_depth_eq_zero _ (Nat.le_zero.mp hd))) E]
  | succ d ih =>
    intro t ν hd E hE
    by_cases hdone : t.done = true
    · rw [measure_congr_tree (fixpoint_of_done hdone) E]
    · have hlt : (step ⟨t, ν⟩).1.depth ≤ d := by
        have h1 : (step ⟨t, ν⟩).1 = t.split := step_fst
        have := depth_split_lt t (by simpa using hdone)
        rw [h1]; omega
      have hEs : MeasurableSet[(step (⟨t, ν⟩ : TreeWithMeasure α)).1.ms] E := by
        rw [show (step (⟨t, ν⟩ : TreeWithMeasure α)).1 = t.split from step_fst]
        exact ms_le_split t E hE
      rw [measure_congr_tree (fixpoint_step (⟨t, ν⟩ : TreeWithMeasure α)) E,
        ih (step ⟨t, ν⟩).1 (step ⟨t, ν⟩).2 hlt E hEs]
      exact step'_preserves t ν [] E hE

lemma fixpoint_preserves' {t : ProbTree α} (ν : Measure[t.ms] Ω) {E : Set Ω}
    (hE : MeasurableSet[t.ms] E) : (fixpoint ⟨t, ν⟩).2 E = ν E :=
  fixpoint_preserves t.depth t ν le_rfl E hE

/-! ### Running a program from an arbitrary footprint -/

lemma isConstTree_toTree_go (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) (path : BoolSeq) :
    IsConstTree m (toTree.go bfpsp (fun _ ↦ m) path) := by
  induction path using toTree.go.induct bfpsp with
  | case1 path leafy =>
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    rfl
  | case2 path leafy ihl ihr =>
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    exact ⟨ihl, ihr⟩

lemma isConstTree_toTree (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) :
    IsConstTree m (toTree bfpsp (fun _ ↦ m)) := by
  rw [toTree]; exact isConstTree_toTree_go bfpsp m []

set_option linter.style.haveILetI false in
/-- **Running a program from an arbitrary footprint.**  The output space refines the input
and leaves its measure alone, the value reported is `treeValue`, and that value is
distributed as the program's own law, *independently of everything the footprint could
already measure*. -/
lemma run_const [Inhabited α] (bfpsp : BoundedFootprintPsp) (m : BernoulliM α)
    (valid : ✓bfpsp.psp) :
    ∃ S : PSpace Ω,
      (run m bfpsp).1.psp = .some S ∧
      result (run m bfpsp) = treeValue m (toTree bfpsp (fun _ ↦ m)) ∧
      (toTree bfpsp (fun _ ↦ m)).ms ≤ S.ms ∧
      (∀ a : α, MeasurableSet[S.ms] (treeValue m (toTree bfpsp (fun _ ↦ m)) ⁻¹' {a})) ∧
      (∀ {E : Set Ω}, MeasurableSet[(toTree bfpsp (fun _ ↦ m)).ms] E →
        S.μ E = (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ E) ∧
      (∀ (a : α) {E : Set Ω}, MeasurableSet[(toTree bfpsp (fun _ ↦ m)).ms] E →
        S.μ (treeValue m (toTree bfpsp (fun _ ↦ m)) ⁻¹' {a} ∩ E)
          = (fixpoint (rootTree m)).2 (runValue m ⁻¹' {a})
            * (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ E) := by
  have ht : IsConstTree m (toTree bfpsp (fun _ ↦ m)) := isConstTree_toTree bfpsp m
  have hms : (toTree bfpsp (fun _ ↦ m)).ms = (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).ms := by
    rw [toTree_ms_eq, bfpsp.sigmaAgrees valid]
  have hcast : ∀ {E : Set Ω}, MeasurableSet[(toTree bfpsp (fun _ ↦ m)).ms] E →
      ((ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ.cast (toTree bfpsp (fun _ ↦ m)).ms) E
        = (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ E := fun hE ↦
    Measure.le_preserves_measure (h := le_of_eq hms)
      (μ := (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ) (hu := hE)
  refine ⟨⟨⟨_, (fixpoint (⟨toTree bfpsp (fun _ ↦ m),
      (ValidPSp.toPSpace ⟨bfpsp.psp, valid⟩).μ.cast
        (toTree bfpsp (fun _ ↦ m)).ms⟩ : TreeWithMeasure α)).2⟩, inferInstance⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run, interp_bernoulliM, bigStep, dite_eq_left valid]
    exact ofTree_psp' _ _
  · rw [run, interp_bernoulliM, bigStep, dite_eq_left valid]
    exact result_bigStep_body _ _ fixpoint_done (reports_fixpoint_constTree ht _)
  · exact ms_le_fixpoint' _ _
  · intro a
    exact (reports_fixpoint_constTree ht _).measurableSet_preimage {a}
  · intro E hE
    exact (fixpoint_preserves' _ hE).trans (hcast hE)
  · intro a E hE
    exact (fixpoint_constTree_inter ht _ a hE).trans (by rw [hcast hE])


/-! ### The law of a program -/

/-- **The law of a program**: the mass its own run puts on each value. -/
def lawOf (t : BernoulliM α) (a : α) : ℝ≥0∞ :=
  (fixpoint (rootTree t)).2 (runValue t ⁻¹' {a})

lemma lawOf_pure (a a' : α) :
    lawOf (PFunctor.FreeM.pure a : BernoulliM α) a' = if a' = a then 1 else 0 := by
  unfold lawOf
  refine Eq.trans (measure_congr_tree (fixpoint_rootTree_pure a) _) ?_
  show (rootTree (PFunctor.FreeM.pure a : BernoulliM α)).2 _ = _
  by_cases h : a' = a
  · rw [show runValue (PFunctor.FreeM.pure a : BernoulliM α) ⁻¹' {a'} = Set.univ from by
      ext ρ; simp [runValue, h], rootTree_univ]
    simp [h]
  · rw [show runValue (PFunctor.FreeM.pure a : BernoulliM α) ⁻¹' {a'} = ∅ from by
      ext ρ; simp [runValue]; exact fun hh ↦ h hh.symm, measure_empty]
    simp [h]

/-- Peeling the first flip off a program's law. -/
lemma lawOf_liftBind (op : BernoulliPFunctor.A) (c : BernoulliPFunctor.B op → BernoulliM α)
    (b : α) :
    lawOf (PFunctor.FreeM.liftBind op c) b
      = flipWeight op.1 true * lawOf (c true) b
        + flipWeight op.1 false * lawOf (c false) b := by
  have hE : MeasurableSet[(ProbTree.node (fixpoint (rootTree (c true))).1
      (fixpoint (rootTree (c false))).1).ms]
      (runValue (PFunctor.FreeM.liftBind op c) ⁻¹' {b}) := by
    have h := (reports_fixpoint_rootTree
      (PFunctor.FreeM.liftBind op c)).measurableSet_preimage {b}
    rw [congrArg Sigma.fst (fixpoint_rootTree_liftBind op c)] at h
    exact h
  unfold lawOf
  refine Eq.trans (measure_congr_tree (fixpoint_rootTree_liftBind op c) _) ?_
  show joinMeasure (flipWeight op.1 true • _) (flipWeight op.1 false • _) _ = _
  exact joinMeasure_smul_preimage _ _ _ _
    (by ext ρ; simp [runValue]) (by ext ρ; simp [runValue]) hE

/-- **The law of a bind** is the bind of the laws. -/
lemma lawOf_bind : ∀ (t : BernoulliM α) (f : α → BernoulliM β) (b : β),
    lawOf (t >>= f) b = ∑' a, lawOf t a * lawOf (f a) b := by
  intro t
  induction t with
  | pure a =>
    intro f b
    rw [show ((PFunctor.FreeM.pure a : BernoulliM α) >>= f) = f a from rfl]
    rw [show (∑' a' : α, lawOf (PFunctor.FreeM.pure a : BernoulliM α) a' * lawOf (f a') b)
        = ∑' a' : α, if a' = a then lawOf (f a') b else 0 from
      tsum_congr fun a' ↦ by rw [lawOf_pure]; split <;> simp_all,
      tsum_ite_eq a (fun a' ↦ lawOf (f a') b)]
  | liftBind op c ih =>
    intro f b
    rw [show ((PFunctor.FreeM.liftBind op c : BernoulliM α) >>= f)
        = PFunctor.FreeM.liftBind op (fun u ↦ c u >>= f) from rfl,
      lawOf_liftBind, ih true f b, ih false f b, ← ENNReal.tsum_mul_left,
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun a ↦ ?_
    rw [lawOf_liftBind, add_mul, ← mul_assoc, ← mul_assoc]

/-- The tree a run ends at does not depend on the measure it carried.  Stated over two
(propositionally equal) trees so that the step case can be applied to `step`'s output. -/
lemma fixpoint_fst_congr : ∀ (d : ℕ) (t t' : ProbTree α), t = t' →
    ∀ (μ : Measure[t.ms] Ω) (ν : Measure[t'.ms] Ω), t.depth ≤ d →
      (fixpoint ⟨t, μ⟩).1 = (fixpoint ⟨t', ν⟩).1 := by
  intro d
  induction d with
  | zero =>
    rintro t t' rfl μ ν hd
    rw [fixpoint_of_done (done_of_depth_eq_zero _ (Nat.le_zero.mp hd)),
      fixpoint_of_done (done_of_depth_eq_zero _ (Nat.le_zero.mp hd))]
  | succ d ih =>
    rintro t t' rfl μ ν hd
    by_cases hdone : t.done = true
    · rw [fixpoint_of_done hdone, fixpoint_of_done hdone]
    · have hlt : (step (⟨t, μ⟩ : TreeWithMeasure α)).1.depth ≤ d := by
        have h1 : (step (⟨t, μ⟩ : TreeWithMeasure α)).1 = t.split := step_fst
        have := depth_split_lt t (by simpa using hdone)
        rw [h1]; omega
      rw [fixpoint_step (⟨t, μ⟩ : TreeWithMeasure α), fixpoint_step (⟨t, ν⟩ : TreeWithMeasure α)]
      exact ih (step (⟨t, μ⟩ : TreeWithMeasure α)).1 (step (⟨t, ν⟩ : TreeWithMeasure α)).1
        ((step_fst (tree := (⟨t, μ⟩ : TreeWithMeasure α))).trans
          (step_fst (tree := (⟨t, ν⟩ : TreeWithMeasure α))).symm)
        (step (⟨t, μ⟩ : TreeWithMeasure α)).2
        (step (⟨t, ν⟩ : TreeWithMeasure α)).2 hlt

lemma fixpoint_fst_congr' {t : ProbTree α} (μ ν : Measure[t.ms] Ω) :
    (fixpoint ⟨t, μ⟩).1 = (fixpoint ⟨t, ν⟩).1 :=
  fixpoint_fst_congr t.depth t t rfl μ ν le_rfl

/-! ### Running is linear in the measure

Stated with the mixture given pointwise rather than as a `Measure.sum`, so that the
induction can be structural: `fixpoint_leaf` and `fixpoint_node` land the sub-runs at
σ-algebras that do not depend on the measure, which is what keeps the families in scope
well-typed. -/

lemma fixpoint_sum {ι : Type} :
    ∀ (t : ProbTree α) (ν : Measure[t.ms] Ω) (f : ι → Measure[t.ms] Ω),
      (∀ E, MeasurableSet[t.ms] E → ν E = ∑' i, f i E) →
      ∀ (E : Set Ω), MeasurableSet[(fixpoint ⟨t, ν⟩).1.ms] E →
        (fixpoint ⟨t, ν⟩).2 E = ∑' i, (fixpoint ⟨t, f i⟩).2 E := by
  intro t
  induction t with
  | leaf n =>
    intro ν f hf E hE
    refine Eq.trans (measure_congr_tree (fixpoint_leaf n ν) E) ?_
    show (ν Set.univ • (fixpoint (rootTree n)).2) E = _
    rw [Measure.smul_apply, smul_eq_mul,
      hf Set.univ (by rw [ms_leaf]; exact MeasurableSet.univ), ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i ↦ ?_
    refine Eq.trans ?_ (measure_congr_tree (fixpoint_leaf n (f i)) E).symm
    show _ = ((f i) Set.univ • (fixpoint (rootTree n)).2) E
    rw [Measure.smul_apply, smul_eq_mul]
  | node l r ihl ihr =>
    intro ν f hf E hE
    have hbr : ∀ (b : Bool) (E' : Set Ω), MeasurableSet[(if b then l else r).ms] E' →
        branchMeasure b ν E' = ∑' i, branchMeasure b (f i) E' := by
      intro b E' hE'
      rw [branchMeasure_apply' b ν hE',
        hf _ ((measurable_descend b hE').inter (measurableSet_prefixEqEvent_singleton b))]
      exact tsum_congr fun i ↦ (branchMeasure_apply' b (f i) hE').symm
    have hsplit : ∀ ρ : Measure[(ProbTree.node l r).ms] Ω,
        MeasurableSet[(fixpoint (⟨ProbTree.node l r, ρ⟩ : TreeWithMeasure α)).1.ms] E →
        (fixpoint (⟨ProbTree.node l r, ρ⟩ : TreeWithMeasure α)).2 E
          = (fixpoint ⟨l, branchMeasure true ρ⟩).2 (consFlip true ⁻¹' E)
            + (fixpoint ⟨r, branchMeasure false ρ⟩).2 (consFlip false ⁻¹' E) := by
      intro ρ hρ
      rw [congrArg Sigma.fst (fixpoint_node ρ)] at hρ
      refine Eq.trans (measure_congr_tree (fixpoint_node ρ) E) ?_
      show joinMeasure _ _ _ = _
      rw [joinMeasure_apply _ _ hρ]
    have hEν := hE
    rw [congrArg Sigma.fst (fixpoint_node ν)] at hEν
    have hT : MeasurableSet[(fixpoint (⟨l, branchMeasure true ν⟩ : TreeWithMeasure α)).1.ms]
        (consFlip true ⁻¹' E) := by
      simpa using measurable_consFlip
        (l := (fixpoint (⟨l, branchMeasure true ν⟩ : TreeWithMeasure α)).1)
        (r := (fixpoint (⟨r, branchMeasure false ν⟩ : TreeWithMeasure α)).1) true hEν
    have hF : MeasurableSet[(fixpoint (⟨r, branchMeasure false ν⟩ : TreeWithMeasure α)).1.ms]
        (consFlip false ⁻¹' E) := by
      simpa using measurable_consFlip
        (l := (fixpoint (⟨l, branchMeasure true ν⟩ : TreeWithMeasure α)).1)
        (r := (fixpoint (⟨r, branchMeasure false ν⟩ : TreeWithMeasure α)).1) false hEν
    rw [hsplit ν hE,
      ihl (branchMeasure true ν) (fun i ↦ branchMeasure true (f i)) (hbr true) _ hT,
      ihr (branchMeasure false ν) (fun i ↦ branchMeasure false (f i)) (hbr false) _ hF,
      ← ENNReal.tsum_add]
    refine tsum_congr fun i ↦ ?_
    refine (hsplit (f i) ?_).symm
    have h := hE
    rw [fixpoint_fst_congr' ν (f i)] at h
    exact h

lemma fixpoint_sum' {ι : Type} {t : ProbTree α} (ν : Measure[t.ms] Ω)
    (f : ι → Measure[t.ms] Ω) (hf : ∀ E, MeasurableSet[t.ms] E → ν E = ∑' i, f i E)
    {E : Set Ω} (hE : MeasurableSet[(fixpoint ⟨t, ν⟩).1.ms] E) :
    (fixpoint ⟨t, ν⟩).2 E = ∑' i, (fixpoint ⟨t, f i⟩).2 E :=
  fixpoint_sum t ν f hf E hE

/-- Drop the first `n` bits of a tape. -/
def shiftBy (n : ℕ) (ρ : Ω) : Ω := fun i ↦ ρ (i + n)

@[simp] lemma shiftBy_zero (ρ : Ω) : shiftBy 0 ρ = ρ := rfl

lemma shiftBy_succ (n : ℕ) (ρ : Ω) : shiftBy (n + 1) ρ = shift (shiftBy n ρ) := by
  funext i
  show ρ (i + (n + 1)) = ρ (i + 1 + n)
  congr 1
  omega

lemma shift_shiftBy (n : ℕ) (ρ : Ω) : shift (shiftBy n ρ) = shiftBy (n + 1) ρ :=
  (shiftBy_succ n ρ).symm

/-- A tape extending `p` extends `p ++ [b]` exactly when its next bit is `b`. -/
lemma mem_prefixEqEvent_append (q : BoolSeq) {ρ : Ω} (hρ : ρ ∈ prefixEqEvent q) (b : Bool)
    (hb : ρ q.length = b) : ρ ∈ prefixEqEvent (q ++ [b]) := by
  intro i
  rcases lt_or_ge i.1 q.length with hi | hi
  · rw [hρ ⟨i.1, hi⟩]
    simp [List.getElem_append_left hi]
  · have hlen : i.1 = q.length := by have := i.2; simp at this; omega
    have hval : (q ++ [b])[i] = b := by simp [Fin.getElem_fin, hlen]
    rw [hval, hlen]
    exact hb

/-- What a footprint's tree reports on a tape: run the program on the tape left after the
tape's own atom prefix. -/
lemma treeValue_toTree_go (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) :
    ∀ (p : BoolSeq), (∀ X : bfpsp.atoms, bfpsp.prefixes X <+: p → bfpsp.prefixes X = p) →
      ∀ ρ : Ω, ρ ∈ prefixEqEvent p →
        treeValue m (toTree.go bfpsp (fun _ ↦ m) p) (shiftBy p.length ρ)
          = runValue m (shiftBy (bfpsp.prefixes (bfpsp.atomOf ρ)).length ρ) := by
  intro p
  induction p using toTree.go.induct bfpsp with
  | case1 p leafy =>
    intro hp ρ hρ
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    obtain ⟨X, hX⟩ := leafy
    have hpX : bfpsp.prefixes X = p := hp X hX
    have hρX : ρ ∈ X.1 := by
      rw [atom_eq_prefixEqEvent bfpsp X, hpX]; exact hρ
    rw [show bfpsp.atomOf ρ = X from atomOf_eq bfpsp hρX, hpX]
    rfl
  | case2 p leafy ihl ihr =>
    intro hp ρ hρ
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    have hstep : ∀ b : Bool, ∀ X : bfpsp.atoms,
        bfpsp.prefixes X <+: p ++ [b] → bfpsp.prefixes X = p ++ [b] := by
      intro b X hX
      by_cases hle : (bfpsp.prefixes X).length ≤ p.length
      · exact absurd ⟨X, List.prefix_of_prefix_length_le hX (List.prefix_append _ _) hle⟩ leafy
      · exact hX.eq_of_length (by have := hX.length_le; simp at this ⊢; omega)
    have hlen : ∀ b : Bool, (p ++ [b]).length = p.length + 1 := by simp
    show (if (shiftBy p.length ρ) 0 then _ else _) = _
    have h0 : (shiftBy p.length ρ) 0 = ρ p.length := by
      show ρ (0 + p.length) = _
      congr 1
      omega
    rw [h0]
    cases hb : ρ p.length
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [shift_shiftBy, ← hlen false]
      exact ihr (hstep false) ρ (mem_prefixEqEvent_append p hρ false hb)
    · simp only [↓reduceIte]
      rw [shift_shiftBy, ← hlen true]
      exact ihl (hstep true) ρ (mem_prefixEqEvent_append p hρ true hb)

/-- The value a footprint's run reports, read off the footprint alone: no tree involved, so
it is invariant under anything that leaves the atoms and prefixes alone. -/
def footprintValue (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) : Ω → α :=
  fun ρ ↦ runValue m (shiftBy (bfpsp.prefixes (bfpsp.atomOf ρ)).length ρ)

lemma treeValue_toTree (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) :
    treeValue m (toTree bfpsp (fun _ ↦ m)) = footprintValue bfpsp m := by
  funext ρ
  rw [toTree]
  simpa [footprintValue] using treeValue_toTree_go bfpsp m [] (fun _ h ↦ List.prefix_nil.mp h) ρ (by simp)

/-! ### Reweighting a footprint

Changing a footprint's measure while keeping its atoms and prefixes.  `footprintValue` is
then invariant by `rfl`, and `toTree` by `toTree_congr`. -/

/-- A footprint with its measure replaced. -/
def BoundedFootprintPsp.reweight (b : BoundedFootprintPsp) (h : ✓b.psp)
    (ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω) (hν : IsProbabilityMeasure ν) :
    BoundedFootprintPsp where
  psp := .some ⟨⟨(ValidPSp.toPSpace ⟨b.psp, h⟩).ms, ν⟩, hν⟩
  atoms := b.atoms
  measurable := fun X hX _ ↦ b.measurable X hX h
  sigmaAgrees := fun _ ↦ b.sigmaAgrees h
  disjoint := b.disjoint
  prefixes := b.prefixes
  agreeOnPrefix := b.agreeOnPrefix
  determinedByPrefix := b.determinedByPrefix
  pathInTreeValid := b.pathInTreeValid
  complete := b.complete

lemma reweight_valid {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν} :
    ✓(BoundedFootprintPsp.reweight b h ν hν).psp := Option.some_ne_none _

lemma footprintValue_reweight {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν}
    (m : BernoulliM α) :
    footprintValue (BoundedFootprintPsp.reweight b h ν hν) m = footprintValue b m := rfl

/-- `toTree` only reads the atoms and their prefixes. -/
lemma toTree_go_congr (b b' : BoundedFootprintPsp) (m : BernoulliM α)
    (hb : b.atoms = b'.atoms)
    (hp : ∀ (S : Set Ω) (hS : S ∈ b.atoms) (hS' : S ∈ b'.atoms),
      b.prefixes ⟨S, hS⟩ = b'.prefixes ⟨S, hS'⟩) :
    ∀ p : BoolSeq, toTree.go b (fun _ ↦ m) p = toTree.go b' (fun _ ↦ m) p := by
  have mem' : ∀ S : Set Ω, S ∈ b.atoms → S ∈ b'.atoms := fun S h ↦ by rw [← hb]; exact h
  have mem : ∀ S : Set Ω, S ∈ b'.atoms → S ∈ b.atoms := fun S h ↦ by rw [hb]; exact h
  intro p
  induction p using toTree.go.induct b with
  | case1 p leafy =>
    have leafy' : ∃ X : b'.atoms, b'.prefixes X <+: p := by
      obtain ⟨X, hX⟩ := leafy
      exact ⟨⟨X.1, mem' X.1 X.2⟩, by rw [← hp X.1 X.2 (mem' X.1 X.2)]; exact hX⟩
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    conv_rhs => rw [toTree.go]
    simp only [leafy', ↓reduceDIte]
  | case2 p leafy ihl ihr =>
    have leafy' : ¬ ∃ X : b'.atoms, b'.prefixes X <+: p := by
      rintro ⟨X, hX⟩
      exact leafy ⟨⟨X.1, mem X.1 X.2⟩, by rw [hp X.1 (mem X.1 X.2) X.2]; exact hX⟩
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    conv_rhs => rw [toTree.go]
    simp only [leafy', ↓reduceDIte]
    rw [ihl, ihr]

lemma toTree_congr (b b' : BoundedFootprintPsp) (m : BernoulliM α)
    (hb : b.atoms = b'.atoms)
    (hp : ∀ (S : Set Ω) (hS : S ∈ b.atoms) (hS' : S ∈ b'.atoms),
      b.prefixes ⟨S, hS⟩ = b'.prefixes ⟨S, hS'⟩) :
    toTree b (fun _ ↦ m) = toTree b' (fun _ ↦ m) := by
  rw [toTree, toTree]
  exact toTree_go_congr b b' m hb hp []

lemma toTree_reweight {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν}
    (m : BernoulliM α) :
    toTree (BoundedFootprintPsp.reweight b h ν hν) (fun _ ↦ m) = toTree b (fun _ ↦ m) :=
  toTree_congr _ _ m rfl (fun _ _ _ ↦ rfl)

/-! ### The run of a mixture is the mixture of the runs -/

lemma fixpoint_measure_congr {t t' : ProbTree α} (ht : t = t') (μ : Measure[t.ms] Ω)
    (μ' : Measure[t'.ms] Ω) (hμ : ∀ E, MeasurableSet[t.ms] E → μ E = μ' E) (E : Set Ω) :
    (fixpoint ⟨t, μ⟩).2 E = (fixpoint ⟨t', μ'⟩).2 E := by
  subst ht
  rw [measure_ext hμ]

lemma fixpoint_fst_tree_congr {t t' : ProbTree α} (ht : t = t') (μ : Measure[t.ms] Ω)
    (μ' : Measure[t'.ms] Ω) : (fixpoint ⟨t, μ⟩).1 = (fixpoint ⟨t', μ'⟩).1 := by
  subst ht
  exact fixpoint_fst_congr' μ μ'

/-- The space a run lands in, with the tree spelled out. -/
lemma run_psp_eq [Inhabited α] (b : BoundedFootprintPsp) (h : ✓b.psp) (m : BernoulliM α) :
    (run m b).1.psp
      = .some ⟨⟨(fixpoint (⟨toTree b (fun _ ↦ m),
            (ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms⟩
              : TreeWithMeasure α)).1.ms,
          (fixpoint (⟨toTree b (fun _ ↦ m),
            (ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms⟩
              : TreeWithMeasure α)).2⟩, inferInstance⟩ := by
  rw [run, interp_bernoulliM, bigStep, dite_eq_left h]
  exact ofTree_psp' _ _

/-- The measure a run lands with, computed at any tree the footprint builds and any measure
agreeing with the footprint's. -/
lemma run_psp_apply [Inhabited α] (b : BoundedFootprintPsp) (h : ✓b.psp) (m : BernoulliM α)
    {T : ProbTree α} (hT : toTree b (fun _ ↦ m) = T)
    {S : PSpace Ω} (hS : (run m b).1.psp = .some S)
    (ρ : Measure[T.ms] Ω)
    (hρ : ∀ F, MeasurableSet[T.ms] F → ρ F = (ValidPSp.toPSpace ⟨b.psp, h⟩).μ F)
    (E : Set Ω) : S.μ E = (fixpoint (⟨T, ρ⟩ : TreeWithMeasure α)).2 E := by
  have hms : (toTree b (fun _ ↦ m)).ms = (ValidPSp.toPSpace ⟨b.psp, h⟩).ms := by
    rw [toTree_ms_eq, b.sigmaAgrees h]
  have hval := Option.some_injective _ ((run_psp_eq b h m).symm.trans hS)
  rw [← hval]
  show (fixpoint (⟨toTree b (fun _ ↦ m),
    (ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms⟩
      : TreeWithMeasure α)).2 E = _
  refine fixpoint_measure_congr hT _ ρ (fun F hF ↦ ?_) E
  rw [Measure.le_preserves_measure (h := le_of_eq hms)
    (μ := (ValidPSp.toPSpace ⟨b.psp, h⟩).μ) (hu := hF), hρ F (hT ▸ hF)]

/-- **Running a mixture.**  If a footprint's measure is a weighted mixture, the space the run
lands in is the same mixture of the spaces the reweighted runs land in. -/
lemma run_psp_mixture {ι : Type} [Inhabited α] (b : BoundedFootprintPsp) (h : ✓b.psp)
    (m : BernoulliM α) (w : ι → ℝ≥0∞)
    (ν : ι → Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω)
    (hν : ∀ i, IsProbabilityMeasure (ν i))
    (hmix : ∀ E, MeasurableSet[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] E →
      (ValidPSp.toPSpace ⟨b.psp, h⟩).μ E = ∑' i, w i * ν i E)
    {S : PSpace Ω} (hS : (run m b).1.psp = .some S)
    {S' : ι → PSpace Ω}
    (hS' : ∀ i, (run m (BoundedFootprintPsp.reweight b h (ν i) (hν i))).1.psp = .some (S' i))
    {E : Set Ω} (hE : MeasurableSet[S.ms] E) :
    S.μ E = ∑' i, w i * (S' i).μ E := by
  have hms : (toTree b (fun _ ↦ m)).ms = (ValidPSp.toPSpace ⟨b.psp, h⟩).ms := by
    rw [toTree_ms_eq, b.sigmaAgrees h]
  have hcast : ∀ (ρ : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω) (F : Set Ω),
      MeasurableSet[(toTree b (fun _ ↦ m)).ms] F →
      (ρ.cast (toTree b (fun _ ↦ m)).ms) F = ρ F := fun ρ F hF ↦
    Measure.le_preserves_measure (h := le_of_eq hms) (μ := ρ) (hu := hF)
  -- the mixture run
  have hmain := run_psp_apply b h m rfl hS
    ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms)
    (fun F hF ↦ hcast _ F hF) E
  -- each reweighted run, at the same tree
  have hpart : ∀ i, (S' i).μ E
      = (fixpoint (⟨toTree b (fun _ ↦ m), (ν i).cast (toTree b (fun _ ↦ m)).ms⟩
          : TreeWithMeasure α)).2 E := fun i ↦
    run_psp_apply (BoundedFootprintPsp.reweight b h (ν i) (hν i)) reweight_valid m
      (toTree_reweight m) (hS' i) _ (fun F hF ↦ hcast (ν i) F hF) E
  rw [hmain]
  rw [fixpoint_sum (toTree b (fun _ ↦ m))
      ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms)
      (fun i ↦ (w i) • ((ν i).cast (toTree b (fun _ ↦ m)).ms))
      (fun F hF ↦ by
        rw [hcast _ F hF, hmix F (hms ▸ hF)]
        exact tsum_congr fun i ↦ by rw [Measure.smul_apply, smul_eq_mul, hcast (ν i) F hF])
      E (by
        have hval := Option.some_injective _ ((run_psp_eq b h m).symm.trans hS)
        rw [← hval] at hE
        exact hE)]
  refine tsum_congr fun i ↦ ?_
  rw [hpart i]
  refine Eq.trans (measure_congr_tree (fixpoint_smul (w i) _) E) ?_
  show (w i • (fixpoint (⟨toTree b (fun _ ↦ m), (ν i).cast (toTree b (fun _ ↦ m)).ms⟩
    : TreeWithMeasure α)).2) E = _
  rw [Measure.smul_apply, smul_eq_mul]
/-! ### The randomness a run adds

`runValue` records what a program reports; `runPath` records *how it got there* -- the bits
it actually read.  The σ-algebra that generates is the randomness the run contributes on top
of the footprint it started from. -/

/-- The path a program takes on a tape: the bits it reads. -/
def runPath : BernoulliM α → Ω → BoolSeq
  | .pure _, _ => []
  | .liftBind _ c, ρ => ρ 0 :: runPath (c (ρ 0)) (shift ρ)

/-- The path a run takes from a footprint: the program's own path on the tape left after the
tape's atom prefix.  Like `footprintValue`, this reads only the atoms and their prefixes. -/
def footprintPath (b : BoundedFootprintPsp) (m : BernoulliM α) : Ω → BoolSeq :=
  fun ρ ↦ runPath m (shiftBy (b.prefixes (b.atomOf ρ)).length ρ)

/-- The randomness a run adds, as a σ-algebra. -/
def freshMs (b : BoundedFootprintPsp) (m : BernoulliM α) : MeasurableSpace Ω :=
  MeasurableSpace.comap (footprintPath b m) ⊤

lemma footprintPath_reweight {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν}
    (m : BernoulliM α) :
    footprintPath (BoundedFootprintPsp.reweight b h ν hν) m = footprintPath b m := rfl

lemma freshMs_reweight {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν}
    (m : BernoulliM α) :
    freshMs (BoundedFootprintPsp.reweight b h ν hν) m = freshMs b m := rfl

/-- Reweighting a footprint does not change what a run from it reports. -/
lemma result_run_reweight [Inhabited α] {b : BoundedFootprintPsp} {h : ✓b.psp}
    {ν : Measure[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] Ω} {hν : IsProbabilityMeasure ν}
    (m : BernoulliM α) :
    result (run m (BoundedFootprintPsp.reweight b h ν hν)) = result (run m b) := by
  obtain ⟨_, _, hres, -⟩ := run_const (BoundedFootprintPsp.reweight b h ν hν) m reweight_valid
  obtain ⟨_, _, hres', -⟩ := run_const b m h
  rw [hres, hres', toTree_reweight]

/-! ### The randomness a run adds is fresh

`fixpoint_constTree_inter`, for the path a program reads rather than the value it reports:
the bits a run reads past the footprint are independent of everything the footprint could
already measure. -/

/-- `g` is constant on each atom of `t`. -/
def ConstOnAtoms {γ : Type} (t : ProbTree α) (g : Ω → γ) : Prop :=
  ∀ q ∈ t.prefixes, ∀ ρ ∈ prefixEqEvent q, ∀ ρ' ∈ prefixEqEvent q, g ρ = g ρ'

/-- A function constant on atoms pulls every set back to a measurable one. -/
lemma ConstOnAtoms.measurableSet_preimage {γ : Type} {t : ProbTree α} {g : Ω → γ}
    (hg : ConstOnAtoms t g) (S : Set γ) : MeasurableSet[t.ms] (g ⁻¹' S) := by
  classical
  have hEq : g ⁻¹' S
      = ⋃ q ∈ t.prefixes.filter (fun q ↦ ∃ ρ ∈ prefixEqEvent q, g ρ ∈ S), prefixEqEvent q := by
    ext ρ
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    refine ⟨fun hρ ↦ ?_, ?_⟩
    · obtain ⟨q, hq, hρq⟩ := exists_prefix_mem t ρ
      exact ⟨q, ⟨hq, ρ, hρq, hρ⟩, hρq⟩
    · rintro ⟨q, ⟨hq, ρ', hρ'q, hρ'S⟩, hρq⟩
      rwa [hg q hq ρ hρq ρ' hρ'q]
  rw [hEq]
  exact Finset.measurableSet_biUnion _ fun q hq ↦
    measurableSet_prefixEqEvent (Finset.mem_filter.mp hq).1

lemma constOnAtoms_node {γ : Type} {l r : ProbTree α} {gt gf : Ω → γ}
    (hl : ConstOnAtoms l gt) (hr : ConstOnAtoms r gf) :
    ConstOnAtoms (ProbTree.node l r) (fun ρ ↦ if ρ 0 then gt (shift ρ) else gf (shift ρ)) := by
  intro q hq ρ hρ ρ' hρ'
  rcases mem_prefixes_node_iff.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
  · rw [mem_prefixEqEvent_cons] at hρ hρ'
    simp only [hρ.1, hρ'.1, ↓reduceIte]
    exact hl q' hq' _ hρ.2 _ hρ'.2
  · rw [mem_prefixEqEvent_cons] at hρ hρ'
    simp only [hρ.1, hρ'.1, Bool.false_eq_true, ↓reduceIte]
    exact hr q' hq' _ hρ.2 _ hρ'.2

/-- A program's own run is finished exactly along the paths it reads. -/
lemma constOnAtoms_fixpoint_rootTree (m : BernoulliM α) :
    ConstOnAtoms (fixpoint (rootTree m)).1 (runPath m) := by
  induction m with
  | pure a =>
    rw [fixpoint_rootTree_pure]
    intro _ _ _ _ _ _
    rfl
  | liftBind op c ih =>
    rw [fixpoint_rootTree_liftBind op c]
    have heq : runPath (PFunctor.FreeM.liftBind op c)
        = fun ρ ↦ if ρ 0 then (fun ρ ↦ true :: runPath (c true) ρ) (shift ρ)
          else (fun ρ ↦ false :: runPath (c false) ρ) (shift ρ) := by
      funext ρ
      cases h0 : ρ 0 <;> simp [runPath, h0]
    rw [heq]
    exact constOnAtoms_node (l := (fixpoint (rootTree (c true))).1)
      (r := (fixpoint (rootTree (c false))).1)
      (gt := fun ρ ↦ true :: runPath (c true) ρ) (gf := fun ρ ↦ false :: runPath (c false) ρ)
      (fun q hq ρ hρ ρ' hρ' ↦ congrArg (true :: ·) (ih true q hq ρ hρ ρ' hρ'))
      (fun q hq ρ hρ ρ' hρ' ↦ congrArg (false :: ·) (ih false q hq ρ hρ ρ' hρ'))

/-- The path such a tree reads: the path through the tree, then `m`'s own path on what is
left of the tape. -/
def treePath (m : BernoulliM α) : ProbTree α → Ω → BoolSeq
  | .leaf _, ρ => runPath m ρ
  | .node l r, ρ => if ρ 0 then treePath m l (shift ρ) else treePath m r (shift ρ)

lemma constOnAtoms_fixpoint_constTree {m : BernoulliM α} :
    ∀ {t : ProbTree α}, IsConstTree m t → ∀ (ν : Measure[t.ms] Ω),
      ConstOnAtoms (fixpoint ⟨t, ν⟩).1 (treePath m t) := by
  intro t
  induction t with
  | leaf n =>
    rintro rfl ν
    rw [congrArg Sigma.fst (fixpoint_leaf n ν)]
    exact constOnAtoms_fixpoint_rootTree n
  | node l r ihl ihr =>
    rintro ⟨hl, hr⟩ ν
    rw [congrArg Sigma.fst (fixpoint_node ν)]
    exact constOnAtoms_node (ihl hl _) (ihr hr _)

/-- **Fresh paths, from any footprint.** -/
lemma fixpoint_constTree_inter_path {m : BernoulliM α} :
    ∀ {t : ProbTree α}, IsConstTree m t → ∀ (ν : Measure[t.ms] Ω) (S : Set BoolSeq)
      {E : Set Ω}, MeasurableSet[t.ms] E →
      (fixpoint ⟨t, ν⟩).2 (treePath m t ⁻¹' S ∩ E)
        = (fixpoint (rootTree m)).2 (runPath m ⁻¹' S) * ν E := by
  intro t
  induction t with
  | leaf n =>
    rintro rfl ν S E hE
    rw [ms_leaf] at hE
    refine Eq.trans (measure_congr_tree (fixpoint_leaf n ν) _) ?_
    rcases MeasurableSpace.measurableSet_bot_iff.mp hE with rfl | rfl
    · show (ν Set.univ • (fixpoint (rootTree n)).2) _ = _
      simp
    · show (ν Set.univ • (fixpoint (rootTree n)).2) _ = _
      rw [Set.inter_univ, Measure.smul_apply, smul_eq_mul, mul_comm]
      rfl
  | node l r ihl ihr =>
    rintro ⟨hl, hr⟩ ν S E hE
    have hGm : MeasurableSet[(fixpoint (⟨ProbTree.node l r, ν⟩ : TreeWithMeasure α)).1.ms]
        (treePath m (ProbTree.node l r) ⁻¹' S ∩ E) :=
      ((constOnAtoms_fixpoint_constTree (t := ProbTree.node l r) ⟨hl, hr⟩
          ν).measurableSet_preimage S).inter
        (ms_le_fixpoint' (ProbTree.node l r) ν E hE)
    rw [congrArg Sigma.fst (fixpoint_node ν)] at hGm
    refine Eq.trans (measure_congr_tree (fixpoint_node ν) _) ?_
    show joinMeasure _ _ _ = _
    rw [joinMeasure_apply _ _ hGm, Set.preimage_inter, Set.preimage_inter]
    simp only [treePath, preimage_consFlip_ite, Bool.false_eq_true, ↓reduceIte]
    rw [ihl hl _ S (by simpa using measurable_consFlip (l := l) (r := r) true hE),
      ihr hr _ S (by simpa using measurable_consFlip (l := l) (r := r) false hE),
      ← mul_add, ← joinMeasure_apply _ _ hE, joinMeasure_branchMeasure]

lemma treePath_toTree_go (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) :
    ∀ (p : BoolSeq), (∀ X : bfpsp.atoms, bfpsp.prefixes X <+: p → bfpsp.prefixes X = p) →
      ∀ ρ : Ω, ρ ∈ prefixEqEvent p →
        treePath m (toTree.go bfpsp (fun _ ↦ m) p) (shiftBy p.length ρ)
          = runPath m (shiftBy (bfpsp.prefixes (bfpsp.atomOf ρ)).length ρ) := by
  intro p
  induction p using toTree.go.induct bfpsp with
  | case1 p leafy =>
    intro hp ρ hρ
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    obtain ⟨X, hX⟩ := leafy
    have hpX : bfpsp.prefixes X = p := hp X hX
    have hρX : ρ ∈ X.1 := by
      rw [atom_eq_prefixEqEvent bfpsp X, hpX]; exact hρ
    rw [show bfpsp.atomOf ρ = X from atomOf_eq bfpsp hρX, hpX]
    rfl
  | case2 p leafy ihl ihr =>
    intro hp ρ hρ
    rw [toTree.go]
    simp only [leafy, ↓reduceDIte]
    have hstep : ∀ b : Bool, ∀ X : bfpsp.atoms,
        bfpsp.prefixes X <+: p ++ [b] → bfpsp.prefixes X = p ++ [b] := by
      intro b X hX
      by_cases hle : (bfpsp.prefixes X).length ≤ p.length
      · exact absurd ⟨X, List.prefix_of_prefix_length_le hX (List.prefix_append _ _) hle⟩ leafy
      · exact hX.eq_of_length (by have := hX.length_le; simp at this ⊢; omega)
    have hlen : ∀ b : Bool, (p ++ [b]).length = p.length + 1 := by simp
    show (if (shiftBy p.length ρ) 0 then _ else _) = _
    have h0 : (shiftBy p.length ρ) 0 = ρ p.length := by
      show ρ (0 + p.length) = _
      congr 1
      omega
    rw [h0]
    cases hb : ρ p.length
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [shift_shiftBy, ← hlen false]
      exact ihr (hstep false) ρ (mem_prefixEqEvent_append p hρ false hb)
    · simp only [↓reduceIte]
      rw [shift_shiftBy, ← hlen true]
      exact ihl (hstep true) ρ (mem_prefixEqEvent_append p hρ true hb)

lemma treePath_toTree (bfpsp : BoundedFootprintPsp) (m : BernoulliM α) :
    treePath m (toTree bfpsp (fun _ ↦ m)) = footprintPath bfpsp m := by
  funext ρ
  rw [toTree]
  simpa [footprintPath] using
    treePath_toTree_go bfpsp m [] (fun _ h ↦ List.prefix_nil.mp h) ρ (by simp)

/-- **The randomness a run adds is fresh.**  The run's space measures it, and it is
independent of everything the footprint could already measure. -/
lemma run_fresh [Inhabited α] (b : BoundedFootprintPsp) (m : BernoulliM α) (h : ✓b.psp)
    {S : PSpace Ω} (hS : (run m b).1.psp = .some S) :
    freshMs b m ≤ S.ms ∧
      ∀ {F : Set Ω}, MeasurableSet[freshMs b m] F → ∀ {E : Set Ω},
        MeasurableSet[(ValidPSp.toPSpace ⟨b.psp, h⟩).ms] E →
          S.μ (F ∩ E) = S.μ F * (ValidPSp.toPSpace ⟨b.psp, h⟩).μ E := by
  have hval := Option.some_injective _ ((run_psp_eq b h m).symm.trans hS)
  subst hval
  have hms : (toTree b (fun _ ↦ m)).ms = (ValidPSp.toPSpace ⟨b.psp, h⟩).ms := by
    rw [toTree_ms_eq, b.sigmaAgrees h]
  have hct := isConstTree_toTree b m
  refine ⟨?_, ?_⟩
  · rintro _ ⟨T, -, rfl⟩
    rw [← treePath_toTree]
    exact (constOnAtoms_fixpoint_constTree hct _).measurableSet_preimage T
  · rintro _ ⟨T, -, rfl⟩ E hE
    rw [← treePath_toTree]
    have hE' : MeasurableSet[(toTree b (fun _ ↦ m)).ms] E := hms ▸ hE
    have hcast : ∀ {E : Set Ω}, MeasurableSet[(toTree b (fun _ ↦ m)).ms] E →
        ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms) E
          = (ValidPSp.toPSpace ⟨b.psp, h⟩).μ E := fun hE ↦
      Measure.le_preserves_measure (h := le_of_eq hms)
        (μ := (ValidPSp.toPSpace ⟨b.psp, h⟩).μ) (hu := hE)
    have h1 := fixpoint_constTree_inter_path hct
      ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms) T hE'
    have h2 := fixpoint_constTree_inter_path hct
      ((ValidPSp.toPSpace ⟨b.psp, h⟩).μ.cast (toTree b (fun _ ↦ m)).ms) T
      (@MeasurableSet.univ _ (toTree b (fun _ ↦ m)).ms)
    rw [Set.inter_univ, hcast MeasurableSet.univ,
      (ValidPSp.toPSpace ⟨b.psp, h⟩).2.measure_univ, mul_one] at h2
    show (fixpoint _).2 _ = (fixpoint _).2 _ * _
    rw [h1, h2, hcast hE']

end

end Program

end ProbTree


end Interp

end Foxglove
