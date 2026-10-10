/-
# `Christodoulou.Bondi.linearStepMap_apply`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStepMap
import Christodoulou.Bondi.Provider.LinearStepMapApply



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem linearStepMap_apply {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) (u r : ℝ≥0) :
    linearStepMap hH data (u, r) = linearStep hH data u r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStepMap_apply



end Christodoulou.Bondi

