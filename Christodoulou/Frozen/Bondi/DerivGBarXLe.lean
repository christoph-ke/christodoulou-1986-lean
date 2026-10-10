/-
# `Christodoulou.Bondi.derivGBarX_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Bondi.Provider.DerivGBarXLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The weighted equibound of `∂_r ḡ` in terms of the radius of the `X`-ball: the bound behind
(7.60), p. 349, and "the equiboundedness of `∂ḡ_n/∂r`", p. 350. -/
theorem derivGBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : derivGBarX hH u r ≤ π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.derivGBarX_le



end Christodoulou.Bondi

