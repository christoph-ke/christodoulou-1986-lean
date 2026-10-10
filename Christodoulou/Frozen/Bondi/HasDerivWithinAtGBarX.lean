/-
# `Christodoulou.Bondi.hasDerivWithinAt_gBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Bondi.Provider.HasDerivWithinAtGBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The radial derivative of `ḡ` within `[0, ∞)`, including the centre, where it vanishes. -/
theorem hasDerivWithinAt_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => gBarX hH u (Real.toNNReal s)) (derivGBarX hH u r) (Ici 0)
      (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_gBarX



end Christodoulou.Bondi

