module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Theorem3AnalyticProof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem3_analytic : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∃ C : ℝ, ∀ u r : ℝ≥0,
          |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
  XT3A.theorem3_analytic 

end Christodoulou.Bondi.Provider
