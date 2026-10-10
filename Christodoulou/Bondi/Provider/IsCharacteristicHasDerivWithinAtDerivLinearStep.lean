module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.LinearStepTransport



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.hasDerivWithinAt_derivLinearStep {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {u₁ : Icc (0 : ℝ) u₀}
    {r₁ : ℝ≥0}
    {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) := by assumption)
    {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
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
  XTr.hasDerivWithinAt_derivLinearStep hχ data hdata ht

end Christodoulou.Bondi.Provider
