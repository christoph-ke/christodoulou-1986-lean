module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.InitialSize
import Christodoulou.Bondi.ScaleInvariantSize



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem scaleInvariantSize_le_initialSize {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption) :
    0 ≤ scaleInvariantSize data hdata ∧
      scaleInvariantSize data hdata ≤ initialSize data hdata :=
  XSV.scaleInvariantSize_le_initialSize data hdata

end Christodoulou.Bondi.Provider
