module
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.RadialDerivativeScale



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem radialDerivative_fieldScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {u r : ℝ≥0} :
    radialDerivative (fieldScale b H) u r = (b : ℝ) * radialDerivative H (b * u) (b * r) :=
  XRDS.radialDerivative_fieldScale hb H u r

end Christodoulou.Bondi.Provider
