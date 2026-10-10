/-
# `Christodoulou.Bondi.IsClassicalSolution.isSlice`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.Provider.IsClassicalSolutionIsSlice



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Each slice of a classical solution, `u ≤ u₀`, is in the slice class of `g`, `ḡ` and `ξ`. -/
theorem IsClassicalSolution.isSlice {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (u : ℝ≥0) (hu : u ≤ u₀) : IsSlice (H.curry u) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsClassicalSolution.isSlice



end Christodoulou.Bondi

