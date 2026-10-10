/-
# `Christodoulou.Bondi.IsCharacteristic.eq_add_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.IsCharacteristicEqAddIntegral



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The integral form of (5.1) from the terminal point ([P] p. 354:
`r(u) = r₁ + ½ ∫_u^{u₁} ḡ(u', r(u')) du'`), with the coefficient of the slice at time `s`. -/
theorem IsCharacteristic.eq_add_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t = r₁ + 1 / 2 * ∫ s in t..(u₁ : ℝ), gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.eq_add_integral



end Christodoulou.Bondi

