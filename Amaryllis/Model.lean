import Mathlib.Data.Finmap
import Mathlib.Data.Nat.Basic

import Iris.Algebra.UPred

import Amaryllis.MeasureOnSpace

namespace Amaryllis

abbrev RId : Type := ℕ

abbrev Ω : Type := RId → Bool

abbrev PSpΩ := PSp Ω

abbrev RV (α : Type) := Ω → α

abbrev ABprop := Iris.UPred PSpΩ

end Amaryllis
