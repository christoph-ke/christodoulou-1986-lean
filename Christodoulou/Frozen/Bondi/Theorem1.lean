/-
# `Christodoulou.Bondi.theorem1`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.Theorem1



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- **Theorem 1**, [P] p. 348: for initial data `h(0, ·) ∈ C¹[0, ∞)` with `h(0, r) = O(r⁻³)` and
`∂h/∂r(0, r) = O(r⁻⁴)` there are `u₀ > 0` and a classical solution on `[0, u₀] × [0, ∞)` taking
the data, with `h = O(r⁻³)` (part of `IsClassicalSolution`) and `∂h/∂r = O(r⁻⁴)` uniformly in
`u`. -/
theorem theorem1 (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    ∃ u₀ : ℝ≥0, 0 < u₀ ∧ ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), IsClassicalSolution u₀ H ∧
      (∀ r : ℝ≥0, H (0, r) = data r) ∧
      ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
          C * (1 + (r : ℝ)) ^ (-4 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem1



end Christodoulou.Bondi

