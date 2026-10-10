/-
# `Christodoulou.Bondi.theorem2_printed`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.Theorem2Printed



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- [P] p. 351, Theorem 2, with the printed hypothesis ∂_r h = O(r⁻⁴) as r → ∞, uniformly in u. -/
theorem theorem2_printed {u₀ : ℝ≥0} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hHderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ))
    (hKderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative K u r| ≤ C * (r : ℝ) ^ (-4 : ℤ))
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r)) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem2_printed



end Christodoulou.Bondi

