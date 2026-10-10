module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.Theorem2Uniqueness



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem2_of_memXBall {u₀ : ℝ≥0}
    {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H := by assumption)
    (hK : MemXBall u₀ x K := by assumption)
    (hcH : IsClassicalSolution u₀ H := by assumption)
    (hcK : IsClassicalSolution u₀ K := by assumption)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r) := by assumption) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) :=
  XU2.theorem2_of_memXBall hH hK hcH hcK hdata

end Christodoulou.Bondi.Provider
