/-
# `Christodoulou.Bondi.primeWeight`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The weight 1 + r + u/2 of the space X′. -/
@[expose] noncomputable def primeWeight (u r : ℝ≥0) : ℝ := 1 + (r : ℝ) + (u : ℝ) / 2

end Christodoulou.Bondi
