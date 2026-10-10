/-
# `Christodoulou.Bondi.IsCharacteristic.eq_sub_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.IsCharacteristicEqSubIntegral



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- (5.2), p. 346, from the initial point `r₀ = χ(0)`:
`χ(t) = r₀ − ½ ∫₀^t ḡ(u, χ(u)) du`. -/
theorem IsCharacteristic.eq_sub_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t = χ 0 - 1 / 2 * ∫ s in (0 : ℝ)..t, gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.eq_sub_integral



end Christodoulou.Bondi

