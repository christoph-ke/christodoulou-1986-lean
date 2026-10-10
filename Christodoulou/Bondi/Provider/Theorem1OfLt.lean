module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Theorem1Proof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem theorem1_of_lt {u₀ : ℝ≥0}
    {d x₁ : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x₁ := by assumption)
    (hT : (u₀ : ℝ) < stepEta x₁ d := by assumption)
    (hδ : (u₀ : ℝ) < stepDelta x₁ := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d :=
      by assumption) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), MemXBall u₀ x₁ H ∧ IsClassicalSolution u₀ H ∧
      ∀ r : ℝ≥0, H (0, r) = data r :=
  XT1.theorem1_of_lt hd hx hT hδ data hdata hbound

end Christodoulou.Bondi.Provider
