/-
# `Christodoulou.Bondi.gBarX_pos`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.Provider.GBarXPos



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `ḡ > 0` (the mean of `g > 0`). -/
theorem gBarX_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : 0 < gBarX hH u r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.gBarX_pos



end Christodoulou.Bondi

