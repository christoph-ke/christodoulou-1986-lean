/-
# `Christodoulou.Bondi.classical_difference_integral_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.ClassicalDifferenceIntegralLe



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem classical_difference_integral_le {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r))
    (v : ℝ≥0) (hv : v ≤ u₀) (φ : ℝ → ℝ) (hφ : IntervalIntegrable φ volume 0 (v : ℝ))
    (hbound : ∀ s : ℝ≥0, s ≤ v → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (s, r) - K (s, r)| ≤ φ s) (r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |H (v, r) - K (v, r)| ≤
      exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) *
        ∫ s in (0 : ℝ)..(v : ℝ), φ s :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.classical_difference_integral_le



end Christodoulou.Bondi

