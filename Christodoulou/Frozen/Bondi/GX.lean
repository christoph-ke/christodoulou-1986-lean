/-
# `Christodoulou.Bondi.gX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.MemXBallIsSlice
public import Christodoulou.Frozen.Bondi.G



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `g(u, r)` of (3.11) for the slice `H(u, ·)`; the time is clamped to `[0, u₀]`. -/
@[expose] noncomputable def gX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : ℝ :=
  g (H.curry (min u u₀)) (hH.isSlice (min u u₀) (min_le_right u u₀)) r

end Christodoulou.Bondi
