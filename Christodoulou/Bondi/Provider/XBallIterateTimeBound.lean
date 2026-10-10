module
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.StepDifference



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem xBallIterate_time_bound {u₀ : ℝ≥0}
    {d x : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x := by assumption)
    (hT : (u₀ : ℝ) < stepEta x d := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d :=
      by assumption)
    {n : ℕ}
    {u r : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) :
    |derivWithin (fun t : ℝ => (xBallIterate hd hx hT data hdata hbound n).val (t.toNNReal, r))
      (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 :=
  XDiff.xBallIterate_time_bound hd hx hT data hdata hbound n u r hu

end Christodoulou.Bondi.Provider
