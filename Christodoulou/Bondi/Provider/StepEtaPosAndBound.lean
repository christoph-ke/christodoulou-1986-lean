module
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.StepDerivBound
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem stepEta_pos_and_bound {d x : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x := by assumption) :
    0 < stepEta x d ∧ ∀ T : ℝ, 0 ≤ T → T < stepEta x d →
      stepValueBound x d T + stepDerivBound x d T < x :=
  XIt.stepEta_pos_and_bound d x hd hx

end Christodoulou.Bondi.Provider
