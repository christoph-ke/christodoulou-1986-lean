module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.FieldScale
import Christodoulou.Bondi.BondiMassScaling



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem bondiMass_fieldScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {u : ℝ≥0}
    (hs : IsSlice ((fieldScale b H).curry u) := by assumption)
    (hs' : IsSlice (H.curry (b * u)) := by assumption) :
    bondiMass ((fieldScale b H).curry u) hs = (b : ℝ)⁻¹ * bondiMass (H.curry (b * u)) hs' :=
  XBMS.bondiMass_fieldScale hb H u hs hs'

end Christodoulou.Bondi.Provider
