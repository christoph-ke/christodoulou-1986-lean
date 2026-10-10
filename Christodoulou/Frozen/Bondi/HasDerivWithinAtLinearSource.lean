/-
# `Christodoulou.Bondi.hasDerivWithinAt_linearSource`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.Provider.HasDerivWithinAtLinearSource



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The radial derivative of the source `f = −a h̄` of (7.2) ([P] p. 355, after (9.16)):
`∂_r f = −(∂_r a) h̄ − a ∂_r h̄`. -/
theorem hasDerivWithinAt_linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => linearSource hH u (Real.toNNReal s))
      (-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r -
        linearCoeff hH u r * derivHBarX hH u r) (Ici 0) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_linearSource



end Christodoulou.Bondi

