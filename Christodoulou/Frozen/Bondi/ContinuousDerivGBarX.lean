/-
# `Christodoulou.Bondi.continuous_derivGBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Bondi.Provider.ContinuousDerivGBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Joint continuity of `∂_r ḡ(u, r)` on the quadrant, including the centre. -/
theorem continuous_derivGBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivGBarX hH p.1 p.2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_derivGBarX



end Christodoulou.Bondi

