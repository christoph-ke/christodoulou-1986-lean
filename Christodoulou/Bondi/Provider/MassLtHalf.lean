module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `m < r/2` for `r > 0` ([P] p. 344), from `ḡ > 0` and `g > 0`. -/
theorem mass_lt_half {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} (hr : 0 < r := by assumption) :
    mass h hh r < (r : ℝ) / 2 := by
  have hr' : (0 : ℝ) < r := hr
  have hq : 0 < gBar h hh r / g h hh r := div_pos (gBar_pos h hh r) (g_pos h hh r)
  unfold mass
  nlinarith

end Christodoulou.Bondi.Provider
