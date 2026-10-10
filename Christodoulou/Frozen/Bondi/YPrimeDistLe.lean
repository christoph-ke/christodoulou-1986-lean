/-
# `Christodoulou.Bondi.YPrimeDistLe`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.PrimeWeight
public import Christodoulou.Frozen.Bondi.MemXBall



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The weighted Y′ distance bound (9.25) on the strip [0, T]. -/
@[expose] def YPrimeDistLe (T : ℝ≥0) (H K : C(ℝ≥0 × ℝ≥0, ℝ)) (y : ℝ) : Prop :=
  ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
    primeWeight u r ^ 3 * |H (u, r) - K (u, r)| ≤ y

end Christodoulou.Bondi
