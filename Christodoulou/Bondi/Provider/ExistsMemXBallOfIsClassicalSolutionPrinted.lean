module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.PrintedDecay



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem exists_memXBall_of_isClassicalSolution_printed {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) := by assumption) :
    ∃ x : ℝ, MemXBall u₀ x H :=
  XPD.exists_memXBall_of_isClassicalSolution_printed hH hderiv

end Christodoulou.Bondi.Provider
