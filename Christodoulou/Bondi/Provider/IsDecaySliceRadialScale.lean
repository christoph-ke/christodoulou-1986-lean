module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.RadialScaleData



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem isDecaySlice_radialScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption) : IsDecaySlice (radialScale b data) :=
  XRS.isDecaySlice_radialScale hb hdata

end Christodoulou.Bondi.Provider
