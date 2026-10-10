/-
# `Christodoulou.Bondi.IsCharacteristic.hasDerivWithinAt_linearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.IsCharacteristicHasDerivWithinAtLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem IsCharacteristic.hasDerivWithinAt_linearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0}
    {χ : ℝ → ℝ} (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    HasDerivWithinAt (fun s : ℝ => linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)))
      (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
          linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) +
        linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
      (Icc 0 (u₁ : ℝ)) t :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.hasDerivWithinAt_linearStep



end Christodoulou.Bondi

