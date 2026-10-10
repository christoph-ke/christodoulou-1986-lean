module
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.ScalingCovariance



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem isClassicalSolution_fieldScale {b : ℝ≥0}
    (hb : 0 < b := by assumption)
    {T : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution (b * T) H := by assumption) :
    IsClassicalSolution T (fieldScale b H) :=
  XSC.isClassicalSolution_fieldScale hb hH

end Christodoulou.Bondi.Provider
