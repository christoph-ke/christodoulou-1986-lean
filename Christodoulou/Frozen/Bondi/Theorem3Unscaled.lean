/-
# `Christodoulou.Bondi.theorem3_unscaled`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.Theorem3Unscaled



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- **Theorem 3, unscaled analytic core** ([P] p. 351; the a = 1 case, exact d of (7.4)): small
data give a global classical solution with explicit decay. The full Theorem 3 (d₀, scaling, M₁
= 0, geodesic completeness) is NOT claimed. -/
theorem theorem3_unscaled : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), initialSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ x : ℝ, 0 < x ∧
        (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∀ u r : ℝ≥0,
          |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem3_unscaled



end Christodoulou.Bondi

