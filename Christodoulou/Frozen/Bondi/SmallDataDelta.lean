/-
# `Christodoulou.Bondi.smallDataDelta`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.SmallDataG



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Δ(x₁) := sup G([0, x₁]) of the proof of Theorem 3. -/
@[expose] noncomputable def smallDataDelta (x₁ : ℝ≥0) : ℝ :=
  sSup (smallDataG '' Icc 0 (x₁ : ℝ))

end Christodoulou.Bondi
