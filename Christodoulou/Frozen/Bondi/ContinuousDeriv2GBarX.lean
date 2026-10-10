/-
# `Christodoulou.Bondi.continuous_deriv2GBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.Provider.ContinuousDeriv2GBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Joint continuity of `∂²_r ḡ` on the quadrant, including the centre. -/
theorem continuous_deriv2GBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => deriv2GBarX hH p.1 p.2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_deriv2GBarX



end Christodoulou.Bondi

