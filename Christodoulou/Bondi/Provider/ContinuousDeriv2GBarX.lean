module
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_deriv2GBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => deriv2GBarX hH p.1 p.2) :=
  XCoef.continuous_deriv2GBarX hH

end Christodoulou.Bondi.Provider
