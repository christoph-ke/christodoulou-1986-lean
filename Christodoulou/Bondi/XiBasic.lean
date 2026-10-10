module
public import Christodoulou.Frozen.Bondi.Xi



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem xi_zero (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : xi h hh 0 = 0 := by
  simp [xi]

end Christodoulou.Bondi
