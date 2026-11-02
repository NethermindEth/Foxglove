module

public import Foxglove.Interp.OracleComp.Basic
public import VCVio.OracleComp.QueryTracking.CachingOracle

namespace Foxglove

namespace Interp

def romSpec (D : Type) (n : ℕ) : OracleSpec D := D →ₒ Fin (n + 1)

def romImpl (D : Type) [DecidableEq D] (n : ℕ) :
    QueryImpl (romSpec D n) (StateT (romSpec D n).QueryCache BernoulliM) :=
  QueryImpl.withCaching fun _ ↦ split n

instance {D : Type} [DecidableEq D] {n : ℕ} :
    LawfulBernoulliInterpretableState (OracleComp (romSpec D n)) where
  st := (romSpec D n).QueryCache
  interp := simulateQ (romImpl D n)
  interp_pure _ := rfl
  interp_bind := simulateQ_bind _

instance {D : Type} [DecidableEq D] {n : ℕ} :
    Inhabited (BernoulliInterpretableState.st (OracleComp (romSpec D n))) :=
  ⟨(∅ : (romSpec D n).QueryCache)⟩

def hashSpec (k : ℕ) : OracleSpec (List Bool) := List Bool →ₒ BitVec k

def sampleBits : (k : ℕ) → BernoulliM (BitVec k)
  | 0 => pure 0#0
  | k + 1 => do
    let b ← flip half
    let v ← sampleBits k
    pure (BitVec.cons b v)

def hashImpl (k : ℕ) : QueryImpl (hashSpec k) (StateT (hashSpec k).QueryCache BernoulliM) :=
  QueryImpl.withCaching fun _ ↦ sampleBits k

instance {k : ℕ} : LawfulBernoulliInterpretableState (OracleComp (hashSpec k)) where
  st := (hashSpec k).QueryCache
  interp := simulateQ (hashImpl k)
  interp_pure _ := rfl
  interp_bind := simulateQ_bind _

instance {k : ℕ} : Inhabited (BernoulliInterpretableState.st (OracleComp (hashSpec k))) :=
  ⟨(∅ : (hashSpec k).QueryCache)⟩

end Interp

end Foxglove
