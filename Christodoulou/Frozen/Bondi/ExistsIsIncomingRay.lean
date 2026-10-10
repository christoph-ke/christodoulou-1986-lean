/-
# `Christodoulou.Bondi.exists_isIncomingRay`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
import Christodoulou.Bondi.Provider.ExistsIsIncomingRay



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem exists_isIncomingRay {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r₀ : ℝ≥0) :
    ∃ u₁ : ℝ, ∃ χ : ℝ → ℝ, IsIncomingRay hH r₀ u₁ χ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.exists_isIncomingRay



end Christodoulou.Bondi

