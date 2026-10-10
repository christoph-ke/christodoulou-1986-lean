/-
# `Christodoulou.Bondi.theorem2`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.Provider.Theorem2



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem theorem2 {u₀ : ℝ≥0} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hHderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (hKderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r)) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem2



end Christodoulou.Bondi

