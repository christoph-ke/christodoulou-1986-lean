module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.MassTail



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem tendsto_mul_one_sub_g {h : C(ℝ≥0, ℝ)}
    (hh : IsSlice h := by assumption) :
    Tendsto (fun r : ℝ≥0 => (r : ℝ) * (1 - g h hh r)) atTop (𝓝 0) :=
  XMT.tendsto_mul_one_sub_g h hh

end Christodoulou.Bondi.Provider
