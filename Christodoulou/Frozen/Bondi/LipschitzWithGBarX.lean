/-
# `Christodoulou.Bondi.lipschitzWith_gBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Christodoulou.Bondi.Provider.LipschitzWithGBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `ḡ(u, ·)` is Lipschitz in `r` with a constant independent of `u` ([P] p. 350,
`|ḡ_n(u', χ_n) − ḡ_n(u', χ)| ≤ a y_n`). -/
theorem lipschitzWith_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) :
    LipschitzWith (Real.toNNReal (π / 6 * x ^ 2))
      (fun s : ℝ => gBarX hH u (Real.toNNReal s)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.lipschitzWith_gBarX



end Christodoulou.Bondi

