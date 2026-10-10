module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.XPrimeSeed



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem translatedDataField_memXPrimeBall {T : ℝ≥0}
    {d : ℝ}
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : InitialBound data d := by assumption) :
    MemXPrimeBall T d (translatedDataField T data) :=
  XPS.translatedDataField_memXPrimeBall data hdata hbound

end Christodoulou.Bondi.Provider
