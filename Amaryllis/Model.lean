import Mathlib.Data.Finmap
import Mathlib.Data.Nat.Basic

import Amaryllis.MeasureOnSpace

namespace Amaryllis

abbrev RId : Type := ℕ

abbrev Ω : Type := RId → Bool

abbrev PSpΩ := PSp Ω

abbrev RV (α : Type) := Ω → α

end Amaryllis
