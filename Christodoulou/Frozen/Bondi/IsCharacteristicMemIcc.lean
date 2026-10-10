/-
# `Christodoulou.Bondi.IsCharacteristic.mem_Icc`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.Provider.IsCharacteristicMemIcc



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The characteristic stays in the physical domain: `r₁ ≤ χ(t) ≤ r₁ + (u₁ − t)/2` on `[0, u₁]`
(from `0 < ḡ ≤ 1`; the upper bound at `t = 0` is (5.3), p. 346). -/
theorem IsCharacteristic.mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t ∈ Icc (r₁ : ℝ) (r₁ + ((u₁ : ℝ) - t) / 2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.mem_Icc



end Christodoulou.Bondi

