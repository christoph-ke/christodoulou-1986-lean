module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStepMap_memXBall {u₀ : ℝ≥0}
    {d x : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x := by assumption)
    (hT : (u₀ : ℝ) < stepEta x d := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d := by assumption)
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} :
    MemXBall u₀ x (linearStepMap hH data) :=
  XIt.linearStepMap_memXBall hd hx hT data hdata hbound hH

end Christodoulou.Bondi.Provider
