module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.StepDerivBound
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_deriv_bound {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) := by assumption)
    {d : ℝ}
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d := by assumption)
    {u r : ℝ≥0} :
    (1 + (r : ℝ)) ^ 4 * |derivLinearStep hH data hdata u r| ≤
      stepDerivBound x d u₀ :=
  XIt.linearStep_deriv_bound hH data hdata d hbound u r

end Christodoulou.Bondi.Provider
