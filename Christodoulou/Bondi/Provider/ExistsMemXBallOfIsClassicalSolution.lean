module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.ClassicalBridge



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem exists_memXBall_of_isClassicalSolution {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by assumption) :
    ∃ x : ℝ, MemXBall u₀ x H :=
  XCB.exists_memXBall_of_isClassicalSolution hH hderiv

end Christodoulou.Bondi.Provider
