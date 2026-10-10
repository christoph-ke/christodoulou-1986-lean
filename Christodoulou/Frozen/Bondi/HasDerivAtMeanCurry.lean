/-
# `Christodoulou.Bondi.hasDerivAt_mean_curry`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.Provider.HasDerivAtMeanCurry



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- [P] (4.1) solved for `∂_u h̄`: `∂_u h̄ = ½ ḡ ∂_r h̄ + ξ/(2r)`, with `∂_r h̄ = (h − h̄)/r`
from (3.8), at interior points of the strip. -/
theorem hasDerivAt_mean_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (hs : IsSlice (H.curry u)) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun v : ℝ => mean (H.curry (Real.toNNReal v)) r)
      (1 / 2 * gBar (H.curry u) hs r * ((H (u, r) - mean (H.curry u) r) / (r : ℝ))
        + xi (H.curry u) hs r / (2 * (r : ℝ))) (u : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_mean_curry



end Christodoulou.Bondi

