module
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.FieldScale
import Christodoulou.Bondi.MassScaling



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem mass_fieldScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {u r : ℝ≥0}
    (hs : IsSlice ((fieldScale b H).curry u) := by assumption)
    (hs' : IsSlice (H.curry (b * u)) := by assumption) :
    mass ((fieldScale b H).curry u) hs r = (b : ℝ)⁻¹ * mass (H.curry (b * u)) hs' (b * r) :=
  XMS.mass_fieldScale hb H u r hs hs'

end Christodoulou.Bondi.Provider
