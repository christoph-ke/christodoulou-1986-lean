/-
# `Christodoulou.Bondi.smallDataDelta_pos_and_witness`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Christodoulou.Bondi.Provider.SmallDataDeltaPosAndWitness



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Δ(x₁) > 0, and every 0 ≤ d < δ(x₁) admits 0 < x < x₁ with d ≤ G(x). -/
theorem smallDataDelta_pos_and_witness (x₁ : ℝ≥0) (hx₁ : 0 < x₁) :
    0 < smallDataDelta x₁ ∧ ∀ d : ℝ, 0 ≤ d → d < smallDataDelta x₁ →
      ∃ x : ℝ, 0 < x ∧ x < x₁ ∧ d ≤ smallDataG x :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.smallDataDelta_pos_and_witness



end Christodoulou.Bondi

