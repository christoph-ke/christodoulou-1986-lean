module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Theorem1Proof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem1 {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption) :
    ∃ u₀ : ℝ≥0, 0 < u₀ ∧ ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), IsClassicalSolution u₀ H ∧
      (∀ r : ℝ≥0, H (0, r) = data r) ∧
      ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
          C * (1 + (r : ℝ)) ^ (-4 : ℤ) :=
  XT1.theorem1 data hdata

end Christodoulou.Bondi.Provider
