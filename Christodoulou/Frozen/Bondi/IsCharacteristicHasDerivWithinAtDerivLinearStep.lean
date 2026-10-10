/-
# `Christodoulou.Bondi.IsCharacteristic.hasDerivWithinAt_derivLinearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.Provider.IsCharacteristicHasDerivWithinAtDerivLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem IsCharacteristic.hasDerivWithinAt_derivLinearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    HasDerivWithinAt
      (fun s : ℝ => derivLinearStep hH data hdata (Real.toNNReal s) (Real.toNNReal (χ s)))
      (2 * linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
          derivLinearStep hH data hdata (Real.toNNReal t) (Real.toNNReal (χ t)) +
        (1 / 2 * deriv2GBarX hH (Real.toNNReal t) (Real.toNNReal (χ t))) *
          linearStep hH data (Real.toNNReal t) (Real.toNNReal (χ t)) +
        (-(1 / 2 * deriv2GBarX hH (Real.toNNReal t) (Real.toNNReal (χ t))) *
            hBarX u₀ H (Real.toNNReal t) (Real.toNNReal (χ t)) -
          linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
            derivHBarX hH (Real.toNNReal t) (Real.toNNReal (χ t))))
      (Icc 0 (u₁ : ℝ)) t :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsCharacteristic.hasDerivWithinAt_derivLinearStep



end Christodoulou.Bondi

