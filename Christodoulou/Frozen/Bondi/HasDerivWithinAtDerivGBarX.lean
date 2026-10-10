/-
# `Christodoulou.Bondi.hasDerivWithinAt_derivGBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.Provider.HasDerivWithinAtDerivGBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `∂_r ḡ` is differentiable in `r` within `[0, ∞)` with derivative `deriv2GBarX`, including
the centre (one-sided); no second derivative of `H` is used. -/
theorem hasDerivWithinAt_derivGBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => derivGBarX hH u (Real.toNNReal s)) (deriv2GBarX hH u r)
      (Ici 0) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_derivGBarX



end Christodoulou.Bondi

