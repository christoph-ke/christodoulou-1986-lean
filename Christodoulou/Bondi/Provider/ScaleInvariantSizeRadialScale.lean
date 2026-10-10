module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.RadialScale
import Christodoulou.Bondi.ScaleInvariance



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem scaleInvariantSize_radialScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hs : IsDecaySlice (radialScale b data) := by assumption) :
    scaleInvariantSize (radialScale b data) hs = scaleInvariantSize data hdata :=
  XSN.scaleInvariantSize_radialScale hb hdata hs

end Christodoulou.Bondi.Provider
