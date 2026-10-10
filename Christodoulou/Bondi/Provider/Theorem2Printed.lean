module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.PrintedDecay



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem2_printed {u₀ : ℝ≥0}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H := by assumption)
    (hcK : IsClassicalSolution u₀ K := by assumption)
    (hHderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) := by assumption)
    (hKderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative K u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) := by assumption)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r) := by assumption) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) :=
  XPD.theorem2_printed hcH hcK hHderiv hKderiv hdata

end Christodoulou.Bondi.Provider
