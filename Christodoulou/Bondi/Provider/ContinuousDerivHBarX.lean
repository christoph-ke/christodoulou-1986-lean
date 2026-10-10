module
public import Christodoulou.Frozen.Bondi.DerivHBarX
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_derivHBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivHBarX hH p.1 p.2) :=
  XCoef.continuous_derivHBarX hH

end Christodoulou.Bondi.Provider
