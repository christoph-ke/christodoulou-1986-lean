module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
import Christodoulou.Bondi.XPrimeBasics



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem translatedDataField_apply {T : ℝ≥0}
    {data : C(ℝ≥0, ℝ)}
    {u r : ℝ≥0}
    (hu : u ≤ T := by assumption) :
    translatedDataField T data (u, r) = data (r + u / 2) :=
  XPB.translatedDataField_apply T data u r hu

end Christodoulou.Bondi.Provider
