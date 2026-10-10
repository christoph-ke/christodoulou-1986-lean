/-
# `Christodoulou.Bondi.theorem1_of_lt`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.Theorem1OfLt



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Theorem 1 with explicit constants, [P] p. 349: for `2d < x₁` and `u₀ < min{η, δ}` there is
a classical solution in the closed ball of radius `x₁` in `X` taking the data. -/
theorem theorem1_of_lt {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (hδ : (u₀ : ℝ) < stepDelta x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), MemXBall u₀ x₁ H ∧ IsClassicalSolution u₀ H ∧
      ∀ r : ℝ≥0, H (0, r) = data r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem1_of_lt



end Christodoulou.Bondi

