/-
# `Christodoulou.Bondi.smallDataDelta_characterization`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Christodoulou.Bondi.Provider.SmallDataDeltaCharacterization



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Δ(x₁) is an attained maximum of G on [0, x₁]. -/
theorem smallDataDelta_characterization (x₁ : ℝ≥0) :
    ∃ z ∈ Icc 0 (x₁ : ℝ), smallDataDelta x₁ = smallDataG z ∧
      ∀ x ∈ Icc 0 (x₁ : ℝ), smallDataG x ≤ smallDataDelta x₁ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.smallDataDelta_characterization



end Christodoulou.Bondi

