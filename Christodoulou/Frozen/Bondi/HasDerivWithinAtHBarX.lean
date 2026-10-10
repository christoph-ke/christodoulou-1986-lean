/-
# `Christodoulou.Bondi.hasDerivWithinAt_hBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivHBarX
import Christodoulou.Bondi.Provider.HasDerivWithinAtHBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `h̄` is differentiable in `r` within `[0, ∞)` with derivative `derivHBarX`, including the
centre (one-sided). -/
theorem hasDerivWithinAt_hBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => hBarX u₀ H u (Real.toNNReal s)) (derivHBarX hH u r)
      (Ici 0) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_hBarX



end Christodoulou.Bondi

