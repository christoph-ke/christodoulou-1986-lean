/-
# `Christodoulou.Bondi.continuous_gBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.Provider.ContinuousGBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Joint continuity of the coefficient `ḡ(u, r)` of (5.1). -/
theorem continuous_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => gBarX hH p.1 p.2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_gBarX



end Christodoulou.Bondi

