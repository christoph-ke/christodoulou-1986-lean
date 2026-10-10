/-
# `Christodoulou.Bondi.gBarX_le_one`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.Provider.GBarXLeOne



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `ḡ ≤ 1` ([P] p. 346, before (5.3)). -/
theorem gBarX_le_one {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : gBarX hH u r ≤ 1 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.gBarX_le_one



end Christodoulou.Bondi

