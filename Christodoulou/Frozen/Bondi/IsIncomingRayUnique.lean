/-
# `Christodoulou.Bondi.IsIncomingRay.unique`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
import Christodoulou.Bondi.Provider.IsIncomingRayUnique



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem IsIncomingRay.unique {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {r₀ : ℝ≥0} {u₁ u₂ : ℝ} {χ₁ χ₂ : ℝ → ℝ}
    (h₁ : IsIncomingRay hH r₀ u₁ χ₁) (h₂ : IsIncomingRay hH r₀ u₂ χ₂) :
    u₁ = u₂ ∧ EqOn χ₁ χ₂ (Icc 0 u₁) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsIncomingRay.unique



end Christodoulou.Bondi

