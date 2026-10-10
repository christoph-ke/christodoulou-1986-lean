module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
import Christodoulou.Bondi.ScaledSizeIdentity



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem initialSize_radialScale {a : ℝ≥0}
    (ha : 0 < a := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hs : IsDecaySlice (radialScale a data) := by assumption) :
    initialSize (radialScale a data) hs = scaledInitialSize a ha data hdata :=
  XSI.initialSize_radialScale ha hdata hs

end Christodoulou.Bondi.Provider
