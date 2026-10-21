module

public import Mathlib.Topology.UnitInterval

@[expose] public section

open unitInterval

def unitInterval.invert (i : I) : I := ⟨(1 : ℝ) - i, by grind⟩

end
