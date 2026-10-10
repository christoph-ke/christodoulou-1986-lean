/-
# `Christodoulou.Bondi.abs_deriv_linearSource_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.Provider.AbsDerivLinearSourceLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `|∂_r f| ≤ 7π x³/(12 (1 + r)⁴)` for the radial derivative of the source `f = −a h̄`, written
as the explicit formula of `hasDerivWithinAt_linearSource` (the `u`-unweighted form of (9.17),
p. 356). -/
theorem abs_deriv_linearSource_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r - linearCoeff hH u r * derivHBarX hH u r| ≤
      7 * π * x ^ 3 / (12 * (1 + (r : ℝ)) ^ 4) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.abs_deriv_linearSource_le



end Christodoulou.Bondi

