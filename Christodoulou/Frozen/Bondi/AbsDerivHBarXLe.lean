/-
# `Christodoulou.Bondi.abs_derivHBarX_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivHBarX
import Christodoulou.Bondi.Provider.AbsDerivHBarXLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `|∂_r h̄| ≤ x/(2 (1 + r)²)` (from the `u`-unweighted form of (9.6), p. 353). -/
theorem abs_derivHBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |derivHBarX hH u r| ≤ x / (2 * (1 + (r : ℝ)) ^ 2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.abs_derivHBarX_le



end Christodoulou.Bondi

