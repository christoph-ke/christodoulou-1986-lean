/-
# `Christodoulou.Bondi.existsUnique_contraction_radius`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.Provider.ExistsUniqueContractionRadius



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The radius x₁ of Lemma 5: the unique positive root of s = 1. -/
theorem existsUnique_contraction_radius :
    ∃! x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.existsUnique_contraction_radius



end Christodoulou.Bondi

