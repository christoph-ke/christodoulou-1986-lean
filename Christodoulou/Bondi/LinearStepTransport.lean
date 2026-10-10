module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicRestrict
import Christodoulou.Frozen.Bondi.IsCharacteristicEqOnCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicHasDerivWithinAtLinearStep
import Christodoulou.Bondi.LinearStepBasic
import Christodoulou.Bondi.LinearODE
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

namespace XTr

private theorem derivLinearStep_of_val {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) (w : Icc (0 : ℝ) u₀)
    (hw : (w : ℝ) = ((min u u₀ : ℝ≥0) : ℝ)) :
    derivLinearStep hH data hdata u r =
      LinODE.duhamel
        (fun s => 2 * linearCoeff hH s.toNNReal (characteristic hH w r s).toNNReal)
        (fun s =>
          (1 / 2 * deriv2GBarX hH s.toNNReal (characteristic hH w r s).toNNReal) *
              linearStep hH data s.toNNReal (characteristic hH w r s).toNNReal +
            (-(1 / 2 * deriv2GBarX hH s.toNNReal (characteristic hH w r s).toNNReal) *
                hBarX u₀ H s.toNNReal (characteristic hH w r s).toNNReal -
              linearCoeff hH s.toNNReal (characteristic hH w r s).toNNReal *
                derivHBarX hH s.toNNReal (characteristic hH w r s).toNNReal))
        (derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0)
          (characteristic hH w r 0)) w := by
  obtain ⟨w, hw0⟩ := w
  simp only at hw
  subst hw
  simp only [derivLinearStep, LinODE.duhamel, intervalIntegral.integral_const_mul,
    NNReal.coe_min]

private theorem derivLinearStep_eq {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    derivLinearStep hH data hdata t.toNNReal (χ t).toNNReal =
      LinODE.duhamel
        (fun s => 2 * linearCoeff hH s.toNNReal (χ s).toNNReal)
        (fun s =>
          (1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal) *
              linearStep hH data s.toNNReal (χ s).toNNReal +
            (-(1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal) *
                hBarX u₀ H s.toNNReal (χ s).toNNReal -
              linearCoeff hH s.toNNReal (χ s).toNNReal *
                derivHBarX hH s.toNNReal (χ s).toNNReal))
        (derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)) t := by
  have htu : t ≤ (u₀ : ℝ) := ht.2.trans u₁.2.2
  have hw : ((⟨t, ht.1, htu⟩ : Icc (0 : ℝ) u₀) : ℝ) =
      ((min t.toNNReal u₀ : ℝ≥0) : ℝ) := by
    have hle : t.toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr htu
    rw [min_eq_left hle, Real.coe_toNNReal _ ht.1]
  rw [derivLinearStep_of_val hH data hdata _ _ _ hw, LinODE.duhamel, LinODE.duhamel]
  have heq := (hχ.restrict ht).eqOn_characteristic
  have h0 : characteristic hH ⟨t, ht.1, htu⟩ (χ t).toNNReal 0 = χ 0 :=
    (heq ⟨le_rfl, ht.1⟩).symm
  dsimp only
  rw [h0]
  congr 1
  · congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    simp only [← heq hs]
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [← heq hs]
    congr 2
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hs.2] at hτ
    simp only [← heq ⟨hs.1.trans hτ.1, hτ.2⟩]


theorem hasDerivWithinAt_derivLinearStep {u₀ : ℝ≥0} {x : ℝ}
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
      (Icc 0 (u₁ : ℝ)) t := by
  have hp : ContinuousOn (fun s : ℝ => (s.toNNReal, (χ s).toNNReal))
      (Icc 0 (u₁ : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn (HasDerivWithinAt.continuousOn hχ.2))
  have hS := HasDerivWithinAt.continuousOn
    (fun s hs => hχ.hasDerivWithinAt_linearStep data (t := s) hs)
  have ha : ContinuousOn (fun s => 2 * linearCoeff hH s.toNNReal (χ s).toNNReal)
      (Icc 0 (u₁ : ℝ)) :=
    continuousOn_const.mul (XStep.continuousOn_linearCoeff hχ)
  have hf : ContinuousOn (fun s =>
      (1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal) *
          linearStep hH data s.toNNReal (χ s).toNNReal +
        (-(1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal) *
            hBarX u₀ H s.toNNReal (χ s).toNNReal -
          linearCoeff hH s.toNNReal (χ s).toNNReal *
            derivHBarX hH s.toNNReal (χ s).toNNReal)) (Icc 0 (u₁ : ℝ)) :=
    (((XCoef.continuous_deriv_linearCoeff hH).comp_continuousOn hp).mul hS).add
      ((XCoef.continuous_deriv_linearSource hH).comp_continuousOn hp)
  have hd := LinODE.duhamel_deriv ha hf
    (derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)) ht
  rw [← derivLinearStep_eq hχ data hdata ht] at hd
  have hd' := hd.congr (fun s hs => derivLinearStep_eq hχ data hdata hs)
    (derivLinearStep_eq hχ data hdata ht)
  simpa only [add_assoc] using hd'

end XTr

end Christodoulou.Bondi
