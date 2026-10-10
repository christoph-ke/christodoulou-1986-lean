module
public import Christodoulou.Bondi.BondiMass
public import Christodoulou.Bondi.GBarBasic
public import Christodoulou.Frozen.Bondi.BondiMassSpec
public import Christodoulou.Frozen.Bondi.GLeOne
public import Christodoulou.Frozen.Bondi.TendstoGAtTop
public import Christodoulou.Frozen.Bondi.IntegrableOnTail
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The radial mass tail and the integral formula for Bondi mass

The slice-minus-mean bound gives an inverse-square bound on the metric deficit. Hence
its radial boundary term vanishes and the deficit is integrable. Passing to the limit
in the local mass identity proves equation (4.7) on the slice class.
-/

public section

open Set MeasureTheory Filter Topology Real Asymptotics
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

namespace XMT

/-- The exponential definition bounds the metric deficit by its tail exponent. -/
lemma one_sub_g_le_tail (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    1 - g h hh r ≤ 4 * π *
      ∫ s in Ioi (r : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 / s := by
  have he := Real.add_one_le_exp (-(4 * π) *
    ∫ s in Ioi (r : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 / s)
  unfold g
  linarith

/-- Explicit inverse-square bound, for any global slice-minus-mean constant. -/
lemma one_sub_g_le_inv_sq (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s : ℝ≥0, |h s - mean h s| ≤ C * (1 + (s : ℝ))⁻¹)
    (r : ℝ≥0) (hr : 0 < r) :
    1 - g h hh r ≤ (2 * π * C^2) * (r : ℝ)^(-2 : ℤ) := by
  have hr' : 0 < (r : ℝ) := hr
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hr').const_mul (C^2)
  have hb' : ∀ s ∈ Ioi (r : ℝ),
      (h s.toNNReal - mean h s.toNNReal)^2 / s ≤ C^2 * s^(-3 : ℝ) := by
    intro s hs
    have hs0 : 0 < s := hr'.trans hs
    have hd := hb s.toNNReal
    rw [Real.coe_toNNReal s hs0.le] at hd
    have hd' : |h s.toNNReal - mean h s.toNNReal| ≤ C * s⁻¹ := by
      apply hd.trans
      gcongr
      linarith
    have hp : (h s.toNNReal - mean h s.toNNReal)^2 ≤ (C * s⁻¹)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd' 2
    calc (h s.toNNReal - mean h s.toNNReal)^2 / s ≤ (C * s⁻¹)^2 / s :=
        div_le_div_of_nonneg_right hp hs0.le
      _ = C^2 * s^(-3 : ℝ) := by
        rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        simp only [zpow_neg, zpow_ofNat]
        field_simp
  have ht : (∫ s in Ioi (r : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 / s) ≤
      C^2 * ((r : ℝ)^(-2 : ℤ) / 2) := by
    calc _ ≤ ∫ s in Ioi (r : ℝ), C^2 * s^(-3 : ℝ) :=
        setIntegral_mono_on (integrableOn_tail h hh r) hi measurableSet_Ioi hb'
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hr']
        norm_num
  exact (one_sub_g_le_tail h hh r).trans (by
    calc 4 * π * _ ≤ 4 * π * (C^2 * ((r : ℝ)^(-2 : ℤ) / 2)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring)

/-- The mean identity, including the centre. -/
lemma mul_gBar_eq_integral (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    (r : ℝ) * gBar h hh r = ∫ s in (0 : ℝ)..(r : ℝ), g h hh s.toNNReal := by
  by_cases hr : r = 0
  · subst r; simp
  · rw [gBar_eq_integral h hh r (pos_iff_ne_zero.mpr hr)]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    field_simp

/-- The local mass as the integral of the metric deficit minus its boundary term. -/
lemma mass_eq_integral_one_sub_g_sub (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    mass h hh r = (1 / (2 * g h hh r)) *
      ((∫ s in (0 : ℝ)..(r : ℝ), (1 - g h hh s.toNNReal)) -
        (r : ℝ) * (1 - g h hh r)) := by
  have hc : IntervalIntegrable (fun s : ℝ => g h hh s.toNNReal) volume 0 (r : ℝ) :=
    ((continuous_g h hh).comp continuous_real_toNNReal).intervalIntegrable 0 (r : ℝ)
  rw [intervalIntegral.integral_sub (intervalIntegrable_const) hc]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [← mul_gBar_eq_integral]
  unfold mass
  field_simp [(g_pos h hh r).ne']
  ring

/-- The radial boundary deficit tends to zero on every decaying slice. -/
theorem tendsto_mul_one_sub_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    Tendsto (fun r : ℝ≥0 => (r : ℝ) * (1 - g h hh r)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := XBM.abs_sub_mean_le h hh
  have hz : Tendsto (fun r : ℝ≥0 => (2 * π * C^2) * (r : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (NNReal.tendsto_coe_atTop.2 tendsto_id)).const_mul (2 * π * C^2)
  apply squeeze_zero' (Eventually.of_forall fun r =>
    mul_nonneg r.coe_nonneg (sub_nonneg.mpr (g_le_one h hh r))) _ hz
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
  calc (r : ℝ) * (1 - g h hh r) ≤ (r : ℝ) * ((2 * π * C^2) * (r : ℝ)^(-2 : ℤ)) :=
      mul_le_mul_of_nonneg_left (one_sub_g_le_inv_sq h hh hC hb r hr) r.coe_nonneg
    _ = (2 * π * C^2) * (r : ℝ)⁻¹ := by
      have hr' : (r : ℝ) ≠ 0 := ne_of_gt (show 0 < (r : ℝ) from hr)
      simp only [zpow_neg, zpow_ofNat]
      field_simp

/-- Integrability of the deficit, proved using continuity at the centre and the tail bound. -/
lemma integrableOn_one_sub_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IntegrableOn (fun s : ℝ => 1 - g h hh s.toNNReal) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := XBM.abs_sub_mean_le h hh
  have ho : (fun s : ℝ => 1 - g h hh s.toNNReal) =O[atTop]
      (fun s : ℝ => s^(-2 : ℝ)) := by
    refine IsBigO.of_bound (2 * π * C^2) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (g_le_one h hh _)),
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs _)]
    have ht := one_sub_g_le_inv_sq h hh hC hb s.toNNReal (Real.toNNReal_pos.mpr hs)
    rw [Real.coe_toNNReal s hs.le] at ht
    simpa only [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] using ht
  have hc : Continuous (fun s : ℝ => 1 - g h hh s.toNNReal) :=
    continuous_const.sub ((continuous_g h hh).comp continuous_real_toNNReal)
  exact (hc.continuousOn.locallyIntegrableOn measurableSet_Ici
    |>.integrableOn_of_isBigO_atTop ho
    (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))).mono_set Ioi_subset_Ici_self

/-- Equation (4.7): the Bondi mass is half the integrable metric deficit. -/
theorem bondiMass_eq_integral_one_sub_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IntegrableOn (fun s : ℝ => 1 - g h hh s.toNNReal) (Ioi 0) ∧
      bondiMass h hh = 1 / 2 * ∫ s in Ioi (0 : ℝ), (1 - g h hh s.toNNReal) := by
  have hi := integrableOn_one_sub_g h hh
  refine ⟨hi, ?_⟩
  have hInt := intervalIntegral_tendsto_integral_Ioi 0 hi
    (NNReal.tendsto_coe_atTop.mpr (tendsto_id : Tendsto (fun r : ℝ≥0 => r) atTop atTop))
  have hlim : Tendsto (mass h hh) atTop
      (𝓝 (1 / 2 * ∫ s in Ioi (0 : ℝ), (1 - g h hh s.toNNReal))) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).div
      ((tendsto_g_atTop h hh).const_mul 2) (by norm_num : 2 * (1 : ℝ) ≠ 0)).mul
      (hInt.sub (tendsto_mul_one_sub_g h hh))
    simpa only [Pi.div_apply, id_eq, mul_one, sub_zero,
      ← mass_eq_integral_one_sub_g_sub] using ht
  exact tendsto_nhds_unique (bondiMass_spec h hh).2.1 hlim

end XMT

end Christodoulou.Bondi
