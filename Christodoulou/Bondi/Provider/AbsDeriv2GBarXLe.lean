module
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem abs_deriv2GBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u r : ℝ≥0} : |deriv2GBarX hH u r| ≤ π * x ^ 2 / (1 + (r : ℝ)) ^ 3 :=
  XCoef.abs_deriv2GBarX_le hH u r

end Christodoulou.Bondi.Provider
