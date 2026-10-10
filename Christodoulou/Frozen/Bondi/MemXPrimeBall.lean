/-
# `Christodoulou.Bondi.MemXPrimeBall`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.PrimeWeight



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The closed ball of radius x in X′ on the strip [0, T]: `MemXBall` regularity and the
weighted SUM bound (9.1). -/
@[expose] def MemXPrimeBall (T : ℝ≥0) (x : ℝ) (H : C(ℝ≥0 × ℝ≥0, ℝ)) : Prop :=
  MemXBall T x H ∧ ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
    primeWeight u r ^ 3 * |H (u, r)| +
      primeWeight u r ^ 4 * |radialDerivative H u r| ≤ x

end Christodoulou.Bondi
