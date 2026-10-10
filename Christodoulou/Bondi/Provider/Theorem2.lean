module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.Theorem2Proof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem2 {u₀ : ℝ≥0}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H := by assumption)
    (hcK : IsClassicalSolution u₀ K := by assumption)
    (hHderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by assumption)
    (hKderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by assumption)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r) := by assumption) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) :=
  XT2.theorem2 hcH hcK hHderiv hKderiv hdata

end Christodoulou.Bondi.Provider
