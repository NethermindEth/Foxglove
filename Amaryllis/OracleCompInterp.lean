
-- import VCVio.Prelude.Core
import VCVio.OracleComp.Support
import VCVio.EvalDist.Defs.Support.Failure
import ToMathlib.Control.OptionT
import Batteries.Control.OptionT
import Init.Data.Rat.Basic

import Amaryllis.MeasureOnSpace
import Amaryllis.OURA

namespace BernoulliInterpretable

inductive BernoulliOps
| Flip : ℝ → BernoulliOps

@[expose]
def BernoulliPFunctor : PFunctor where
  A := BernoulliOps
  B _ := Bool

class BernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliPFunctor.FreeM (oSpec.toPFunctor.B op)

def flip (r : ℝ) : PFunctor.FreeM BernoulliPFunctor Bool :=
  PFunctor.FreeM.liftBind (BernoulliOps.Flip r) (PFunctor.FreeM.pure)

def split {n : ℕ} (m : Fin n) : PFunctor.FreeM BernoulliPFunctor (Fin n) := do
  if h₁ : n = m.1 + 1
    then pure m
    else
      let b ← flip (mkRat 1 (n - m.1))
      if b
        then pure m
        else split (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

instance : BernoulliInterpretable unifSpec where
  interp_op op := split (0 : (Fin (op + 1)))

open BernoulliInterpretable in
instance {α β} {oSpec₁ : OracleSpec α} {oSpec₂ : OracleSpec β} [BernoulliInterpretable oSpec₁]
    [BernoulliInterpretable oSpec₂]
  : BernoulliInterpretable (oSpec₁ + oSpec₂) where
  interp_op op := match op with
                    | .inl a => interp_op a
                    | .inr a => interp_op a

open BernoulliInterpretable in
def interp {α β} {oSpec : OracleSpec β} [BernoulliInterpretable oSpec] (p : OracleComp oSpec α)
      : PFunctor.FreeM (BernoulliPFunctor) α :=
  match p with
   | PFunctor.FreeM.pure a => pure a
   | PFunctor.FreeM.liftBind op f => bind (interp_op op) (fun x => interp (f x))

def Ω : Type := ℕ → Bool
def RV (α : Type) := Ω → α

instance : Inhabited Ω where
  default := fun _ ↦ True

def interp_psp' {α : Type} (m : PFunctor.FreeM (BernoulliPFunctor) α) (n : ℕ) (p : PSp Ω) : PSp Ω × RV α :=
  match m with
  | PFunctor.FreeM.pure a => (p, fun _ ↦ a)
  | PFunctor.FreeM.liftBind (BernoulliOps.Flip r) f =>
    let p' : PSp Ω := sorry -- defined in terms of p and n
    let p'' : PSp Ω := sorry -- Bind.bind p' sorry  -- weighted sum, i.e. the Giri Monad bind (?)
    (
      p'',
      fun ω ↦ (interp_psp' (f (ω n)) (n + 1) p').2 ω
    )

noncomputable def interp_psp {α : Type} (m : PFunctor.FreeM (BernoulliPFunctor) α) : PSp Ω × RV α :=
  interp_psp' m 0 (.some 1)


end BernoulliInterpretable
