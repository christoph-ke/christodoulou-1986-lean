module
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.StepValueBound
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_value_bound {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    {d : ℝ}
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| ≤ d := by assumption)
    {u r : ℝ≥0} :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r| ≤ stepValueBound x d u₀ :=
  XIt.linearStep_value_bound hH data d hbound u r

end Christodoulou.Bondi.Provider
