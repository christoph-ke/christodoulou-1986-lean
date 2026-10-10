/-
# `Christodoulou.Bondi.charField`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.GBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The right-hand side `−½ ḡ(u, r)` of the characteristic equation (5.1), [P] p. 345, as a total
function of real time and radius: both are clamped to `[0, ∞)` by `Real.toNNReal`, and the time is
further clamped to `[0, u₀]` inside `gBarX`. -/
@[expose] noncomputable def charField {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (t z : ℝ) : ℝ :=
  -(1 / 2) * gBarX hH (Real.toNNReal t) (Real.toNNReal z)

end Christodoulou.Bondi
