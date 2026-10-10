module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `m(0) = 0` ([P] p. 344): the factor `r/2` vanishes. -/
theorem mass_zero {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} : mass h hh 0 = 0 := by
  simp [mass]

end Christodoulou.Bondi.Provider
