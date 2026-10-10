module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem abs_deriv_linearSource_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u r : ℝ≥0} :
    |-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r - linearCoeff hH u r * derivHBarX hH u r| ≤
      7 * π * x ^ 3 / (12 * (1 + (r : ℝ)) ^ 4) :=
  XCoef.abs_deriv_linearSource_le hH u r

end Christodoulou.Bondi.Provider
