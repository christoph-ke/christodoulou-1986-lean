/-
# `Christodoulou.Bondi.exists_memXBall_of_isClassicalSolution`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.Provider.ExistsMemXBallOfIsClassicalSolution



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Reconstruction for [P] p.351, Theorem 2; X is (7.1), p.348. -/
theorem exists_memXBall_of_isClassicalSolution {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ)) :
    ∃ x : ℝ, MemXBall u₀ x H :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.exists_memXBall_of_isClassicalSolution



end Christodoulou.Bondi

