/-
# `Christodoulou.Bondi.MemXBall.isSlice`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.Provider.MemXBallIsSlice



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Each slice of a field in the `X`-ball, `u ≤ u₀`, is in the slice class of `g` and `ḡ`. -/
theorem MemXBall.isSlice {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u : ℝ≥0) (hu : u ≤ u₀) : IsSlice (H.curry u) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.MemXBall.isSlice



end Christodoulou.Bondi

