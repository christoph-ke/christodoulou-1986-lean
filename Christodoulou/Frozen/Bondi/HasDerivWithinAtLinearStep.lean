/-
# `Christodoulou.Bondi.hasDerivWithinAt_linearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
import Christodoulou.Bondi.Provider.HasDerivWithinAtLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem hasDerivWithinAt_linearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => linearStep hH data u (Real.toNNReal s))
      (derivLinearStep hH data hdata u r) (Ici 0) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_linearStep



end Christodoulou.Bondi

