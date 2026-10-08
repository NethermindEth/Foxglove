import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finmap

import Amaryllis.MeasureOnSpace
import Amaryllis.Model

namespace Amaryllis

-- instance : FunLike ABprop PSpΩ Prop where
--   coe := fun P ↦ P.holds
--   coe_injective {P Q h} := by aesop

noncomputable section

attribute [local aesop simp] Equivalence.refl Equivalence.trans Equivalence.symm

instance : OrderedUnitalResourceAlgebra PSpΩ := inferInstance

instance : DiscreteCMRA PSpΩ := inferInstance

instance : Iris.CMRA PSpΩ := inferInstance

instance : Iris.UCMRA PSpΩ := inferInstance

open Iris

end

end Amaryllis
