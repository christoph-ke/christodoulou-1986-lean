module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `g > 0`: it is an exponential. -/
theorem g_pos {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} : 0 < g h hh r := Real.exp_pos _

end Christodoulou.Bondi.Provider
