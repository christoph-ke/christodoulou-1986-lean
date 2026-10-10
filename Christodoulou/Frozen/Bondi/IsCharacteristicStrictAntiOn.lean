/-
# `Christodoulou.Bondi.IsCharacteristic.strictAntiOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.Provider.IsCharacteristicStrictAntiOn



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- A characteristic decreases strictly in time on `[0, u₁]` (since `ḡ > 0`). -/
theorem IsCharacteristic.strictAntiOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) : StrictAntiOn χ (Icc 0 (u₁ : ℝ)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.strictAntiOn



end Christodoulou.Bondi

