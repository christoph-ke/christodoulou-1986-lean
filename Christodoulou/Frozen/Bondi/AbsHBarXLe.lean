/-
# `Christodoulou.Bondi.abs_hBarX_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.HBarX
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.Provider.AbsHBarXLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `|h̄| ≤ x/(1 + r)` (the `u`-unweighted form of (9.4), p. 352). -/
theorem abs_hBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |hBarX u₀ H u r| ≤ x / (1 + (r : ℝ)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.abs_hBarX_le



end Christodoulou.Bondi

