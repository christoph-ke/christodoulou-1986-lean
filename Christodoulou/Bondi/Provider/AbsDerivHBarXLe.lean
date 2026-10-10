module
public import Christodoulou.Frozen.Bondi.DerivHBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem abs_derivHBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u r : ℝ≥0} : |derivHBarX hH u r| ≤ x / (2 * (1 + (r : ℝ)) ^ 2) :=
  XCoef.abs_derivHBarX_le hH u r

end Christodoulou.Bondi.Provider
