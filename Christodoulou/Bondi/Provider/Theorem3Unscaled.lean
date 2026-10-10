module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Theorem3UnscaledProof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem3_unscaled : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), initialSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ x : ℝ, 0 < x ∧
        (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∀ u r : ℝ≥0,
          |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
  XT3.theorem3_unscaled 

end Christodoulou.Bondi.Provider
