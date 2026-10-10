module
public import Christodoulou.Frozen.Bondi.XBallIterate
import Christodoulou.Bondi.IterationLemma1



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem xBallIterate_rec {u₀ : ℝ≥0}
    {d x : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x := by assumption)
    (hT : (u₀ : ℝ) < stepEta x d := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d := by assumption) :
    (xBallIterate hd hx hT data hdata hbound 0).val = constantDataField data ∧
    (∀ n, (xBallIterate hd hx hT data hdata hbound (n + 1)).val =
      linearStepMap (xBallIterate hd hx hT data hdata hbound n).property data) ∧
    (∀ n r, (xBallIterate hd hx hT data hdata hbound n).val (0, r) = data r) :=
  XL1.xBallIterate_rec hd hx hT data hdata hbound

end Christodoulou.Bondi.Provider
