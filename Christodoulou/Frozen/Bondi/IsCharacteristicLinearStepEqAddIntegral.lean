/-
# `Christodoulou.Bondi.IsCharacteristic.linearStep_eq_add_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.IsCharacteristicLinearStepEqAddIntegral



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- (7.2) in integral form along characteristics (cf. [P] p. 351, "in the integral sense"). -/
theorem IsCharacteristic.linearStep_eq_add_integral {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0}
    {χ : ℝ → ℝ} (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) =
      h₀ (Real.toNNReal (χ 0)) +
        ∫ s in (0 : ℝ)..t,
          (linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s)) *
              linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)) +
            linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s))) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.linearStep_eq_add_integral



end Christodoulou.Bondi

