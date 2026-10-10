module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivWithinAt_linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u r : ℝ≥0} :
    HasDerivWithinAt (fun s : ℝ => linearSource hH u (Real.toNNReal s))
      (-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r -
        linearCoeff hH u r * derivHBarX hH u r) (Ici 0) (r : ℝ) :=
  XCoef.hasDerivWithinAt_linearSource hH u r

end Christodoulou.Bondi.Provider
