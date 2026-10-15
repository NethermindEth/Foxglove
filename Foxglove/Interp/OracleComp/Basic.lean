module

public import Foxglove.Interp.Bernoulli.Basic
public import VCVio.OracleComp.OracleComp

@[expose] public section
namespace Foxglove

namespace Interp

/-- An oracle spec whose operations can be implemented by Bernoulli coin flips. -/
class OracleBernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliM (oSpec.toPFunctor.B op)

instance : OracleBernoulliInterpretable unifSpec where
  interp_op := split

open OracleBernoulliInterpretable in
instance {α β} {oSpec₁ : OracleSpec α} {oSpec₂ : OracleSpec β} [OracleBernoulliInterpretable oSpec₁]
    [OracleBernoulliInterpretable oSpec₂]
  : OracleBernoulliInterpretable (oSpec₁ + oSpec₂) where
  interp_op op := match op with
                    | .inl a => interp_op a
                    | .inr a => interp_op a

open OracleBernoulliInterpretable in
def interp {α β} {oSpec : OracleSpec β} [OracleBernoulliInterpretable oSpec] (p : OracleComp oSpec α)
      : BernoulliM α :=
  match p with
   | PFunctor.FreeM.pure a => pure a
   | PFunctor.FreeM.liftBind op f => bind (interp_op op) (fun x => interp (f x))

instance {α} {oSpec : OracleSpec α} [OracleBernoulliInterpretable oSpec] :
  BernoulliInterpretable (OracleComp oSpec) where
    interp := interp

end Interp

end Foxglove
