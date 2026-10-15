module

import Mathlib.Data.Nat.Notation

@[expose] public section
namespace Foxglove

abbrev Ω : Type := ℕ → Bool

abbrev RV (α : Type) := Ω → α

end Foxglove
