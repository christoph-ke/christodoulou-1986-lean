/-
# `Christodoulou.Bondi.IsCharacteristic.linearStep_eq`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.IsCharacteristicLinearStepEq



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- (7.20), p. 355, along an arbitrary characteristic: at every point `(t, χ(t))` of a
characteristic `χ` through `(u₁, r₁)`, the linear step is given by the formula integrated along
`χ` from `r₀ = χ(0)`. -/
theorem IsCharacteristic.linearStep_eq {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) =
      h₀ (Real.toNNReal (χ 0)) *
          exp (∫ s in (0 : ℝ)..t, linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s))) +
        ∫ s in (0 : ℝ)..t,
          exp (∫ τ in s..t, linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ))) *
            linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.linearStep_eq



end Christodoulou.Bondi

