module
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicEqOnCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Radial.MeanBasic

/-!
# Continuity and restriction for the linear step

The clamped radial mean is jointly continuous by averaging over the unit interval.
The linear coefficient and source are therefore continuous along every characteristic.
Restriction and uniqueness of characteristics give the defining formula along any such curve.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- Joint continuity of the clamped mean `h̄(u, r)`. -/
theorem XStep.continuous_hBarX (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => hBarX u₀ H p.1 p.2) := by
  simp only [hBarX]
  simp_rw [Christodoulou.Radial.mean_eq_integral_unitInterval]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact H.continuous.comp
    (((continuous_fst.comp continuous_fst).min continuous_const).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)))

/-- The linear coefficient is continuous along a characteristic. -/
theorem XStep.continuousOn_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) :
    ContinuousOn (fun s : ℝ => linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s)))
      (Icc 0 (u₁ : ℝ)) := by
  have hp : ContinuousOn (fun s : ℝ => (s.toNNReal, (χ s).toNNReal)) (Icc 0 (u₁ : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn (HasDerivWithinAt.continuousOn hχ.2))
  exact continuousOn_const.mul ((continuous_derivGBarX hH).comp_continuousOn hp)

/-- The linear source is continuous along a characteristic. -/
theorem XStep.continuousOn_linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) :
    ContinuousOn (fun s : ℝ => linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s)))
      (Icc 0 (u₁ : ℝ)) := by
  have hp : ContinuousOn (fun s : ℝ => (s.toNNReal, (χ s).toNNReal)) (Icc 0 (u₁ : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn (HasDerivWithinAt.continuousOn hχ.2))
  exact (continuousOn_linearCoeff hχ).neg.mul
    ((continuous_hBarX u₀ H).comp_continuousOn hp)

/-- Restriction to an earlier terminal time preserves the characteristic equation. -/
theorem XStep.restrict {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    IsCharacteristic hH ⟨t, ht.1, ht.2.trans u₁.2.2⟩ (Real.toNNReal (χ t)) χ := by
  refine ⟨(Real.coe_toNNReal _ (r₁.coe_nonneg.trans (hχ.mem_Icc ht).1)).symm, ?_⟩
  intro s hs
  exact (hχ.2 s ⟨hs.1, hs.2.trans ht.2⟩).mono (Icc_subset_Icc_right ht.2)

/-- The defining formula with any terminal-time witness. -/
private theorem linearStep_of_val {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) (u r : ℝ≥0) (w : Icc (0 : ℝ) u₀)
    (hw : (w : ℝ) = ((min u u₀ : ℝ≥0) : ℝ)) :
    linearStep hH h₀ u r =
      h₀ (Real.toNNReal (characteristic hH w r 0)) *
        exp (∫ s in (0 : ℝ)..(w : ℝ),
          linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH w r s))) +
      ∫ s in (0 : ℝ)..(w : ℝ),
        exp (∫ τ in s..(w : ℝ),
          linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (characteristic hH w r τ))) *
          linearSource hH (Real.toNNReal s) (Real.toNNReal (characteristic hH w r s)) := by
  obtain ⟨w, hw0⟩ := w
  simp only at hw
  subst hw
  rfl

/-- The linear step takes the prescribed initial data at time zero. -/
theorem XStep.linearStep_zero {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) (r : ℝ≥0) : linearStep hH h₀ 0 r = h₀ r := by
  have hc := (isCharacteristic_characteristic hH ⟨0, le_rfl, u₀.2⟩ r).1
  rw [linearStep_of_val hH h₀ 0 r ⟨0, le_rfl, u₀.2⟩ (by simp)]
  simp only [intervalIntegral.integral_same, Real.exp_zero, mul_one, add_zero]
  simp only at hc
  rw [hc, Real.toNNReal_coe]

/-- The defining formula for the linear step along every characteristic. -/
theorem XStep.linearStep_eq {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) =
      h₀ (Real.toNNReal (χ 0)) *
          exp (∫ s in (0 : ℝ)..t, linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s))) +
        ∫ s in (0 : ℝ)..t,
          exp (∫ τ in s..t, linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ))) *
            linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s)) := by
  have htu : t ≤ (u₀ : ℝ) := ht.2.trans u₁.2.2
  have hw : ((⟨t, ht.1, htu⟩ : Icc (0 : ℝ) u₀) : ℝ) =
      ((min t.toNNReal u₀ : ℝ≥0) : ℝ) := by
    have : t.toNNReal ≤ u₀ := by
      rw [Real.toNNReal_le_iff_le_coe]; exact htu
    rw [min_eq_left this, Real.coe_toNNReal _ ht.1]
  rw [linearStep_of_val hH h₀ _ _ _ hw]
  have heq := (restrict hχ ht).eqOn_characteristic
  simp only
  have h0 : characteristic hH ⟨t, ht.1, htu⟩ (χ t).toNNReal 0 = χ 0 :=
    (heq ⟨le_rfl, ht.1⟩).symm
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
    simp only
    rw [← heq hs]
    congr 2
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hs.2] at hτ
    simp only [← heq ⟨hs.1.trans hτ.1, hτ.2⟩]

end Christodoulou.Bondi
