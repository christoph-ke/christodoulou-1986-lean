module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.LinearStepBasic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_zero {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {h₀ : C(ℝ≥0, ℝ)} {r : ℝ≥0} : linearStep hH h₀ 0 r = h₀ r :=
  XStep.linearStep_zero hH h₀ r

end Christodoulou.Bondi.Provider
