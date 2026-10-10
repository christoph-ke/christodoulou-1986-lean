module
public import Christodoulou.Frozen.Bondi.StepDelta
import Christodoulou.Bondi.StepDifference



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem stepDelta_pos_and_bound {x : ℝ} :
    0 < stepDelta x ∧ ∀ T : ℝ, 0 ≤ T → T < stepDelta x →
      T * exp (π * x ^ 2 / 12 * T) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) ≤ 1 / 2 :=
  XDiff.stepDelta_pos_and_bound x

end Christodoulou.Bondi.Provider
