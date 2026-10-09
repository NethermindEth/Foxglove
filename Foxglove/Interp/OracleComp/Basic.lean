module

public import Foxglove.Interp.Bernoulli.Basic
public import VCVio.OracleComp.OracleComp


@[expose] public section
namespace Foxglove

namespace Interp

instance : BernoulliInterpretable unifSpec where
  interp_op := split

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

end Interp

end Foxglove
