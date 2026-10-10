module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.StepDifference



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_time_bound {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by assumption)
    (hS : MemXBall u₀ x (linearStepMap hH data) := by assumption)
    {u r : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) :
    |derivWithin (fun t : ℝ => linearStep hH data t.toNNReal r) (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 :=
  XDiff.linearStep_time_bound hH data hdata hS u r hu

end Christodoulou.Bondi.Provider
