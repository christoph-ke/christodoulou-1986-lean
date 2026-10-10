/-
# `Christodoulou.Bondi.abs_deriv2GBarX_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
import Christodoulou.Bondi.Provider.AbsDeriv2GBarXLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `|∂²_r ḡ| ≤ π x²/(1 + r)³` (the `u`-unweighted form of the second display of p. 356; the
identity defining `∂²_r ḡ` is the first display). -/
theorem abs_deriv2GBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |deriv2GBarX hH u r| ≤ π * x ^ 2 / (1 + (r : ℝ)) ^ 3 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.abs_deriv2GBarX_le



end Christodoulou.Bondi

