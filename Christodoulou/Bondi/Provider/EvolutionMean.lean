module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Frozen.Bondi.HasDerivAtMeanCurry
import Christodoulou.Frozen.Radial.HasDerivAtMean



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem evolution_mean {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption) {u : ℝ≥0} (hu : 0 < u := by assumption)
    (hu₀ : u < u₀ := by assumption) {hs : IsSlice (H.curry u)} {r : ℝ≥0}
    (hr : 0 < r := by assumption) :
    deriv (fun v : ℝ => mean (H.curry (Real.toNNReal v)) r) (u : ℝ)
        - 1 / 2 * gBar (H.curry u) hs r
          * deriv (fun s : ℝ => mean (H.curry u) (Real.toNNReal s)) (r : ℝ)
      = xi (H.curry u) hs r / (2 * (r : ℝ)) := by
  rw [(hasDerivAt_mean_curry hH u hu hu₀ hs r hr).deriv,
    (hasDerivAt_mean (H.curry u) r hr).deriv]
  have : (H.curry u) r = H (u, r) := rfl
  rw [this]
  ring

end Christodoulou.Bondi.Provider
