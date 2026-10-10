module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
import Christodoulou.Bondi.ScaleInvariantSize



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem exists_scaledInitialSize_lt {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    {δ : ℝ}
    (h : scaleInvariantSize data hdata < δ := by assumption) :
    ∃ (a : ℝ≥0) (ha : 0 < a), scaledInitialSize a ha data hdata < δ :=
  XSV.exists_scaledInitialSize_lt hdata h

end Christodoulou.Bondi.Provider
