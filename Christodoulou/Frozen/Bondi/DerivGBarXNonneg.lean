/-
# `Christodoulou.Bondi.derivGBarX_nonneg`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Bondi.Provider.DerivGBarXNonneg



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `∂_r ḡ ≥ 0`: `ḡ` is nondecreasing in `r` (`ḡ ≤ g`, [P] p. 344); used for `ζ ≤ 1` and (5.8). -/
theorem derivGBarX_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : 0 ≤ derivGBarX hH u r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.derivGBarX_nonneg



end Christodoulou.Bondi

