/-
# `Christodoulou.Bondi.gBarX_of_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.Provider.GBarXOfLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem gBarX_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) {u : ℝ≥0}
    (hu : u ≤ u₀) (hs : IsSlice (H.curry u)) (r : ℝ≥0) :
    gBarX hH u r = gBar (H.curry u) hs r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.gBarX_of_le



end Christodoulou.Bondi

