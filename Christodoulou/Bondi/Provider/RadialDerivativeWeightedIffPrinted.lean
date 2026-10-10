module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.PrintedDecay



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem radialDerivative_weighted_iff_printed {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
        |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) :=
  XPD.radialDerivative_weighted_iff_printed hH

end Christodoulou.Bondi.Provider
