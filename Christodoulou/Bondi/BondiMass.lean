module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.MassEqIntegral
public import Christodoulou.Frozen.Bondi.MonotoneMass
public import Christodoulou.Frozen.Bondi.MassNonneg
public import Christodoulou.Frozen.Bondi.GBarLeG
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.ContinuousG
public import Christodoulou.Bondi.GBarBasic
public import Christodoulou.Frozen.Radial.Mean
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Christodoulou.Frozen.Radial.ContinuousMean
public import Christodoulou.Radial.MeanBasic
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics



public section

open Set Real Filter Topology MeasureTheory Asymptotics
open scoped NNReal

namespace Christodoulou.Bondi

open Christodoulou.Radial

namespace XBM

/-- The slice itself is integrable on the nonnegative half-line. -/
theorem integrableOn_slice (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IntegrableOn (fun s : ℝ => h s.toNNReal) (Ici 0) := by
  have ho : (fun s : ℝ => h s.toNNReal) =O[atTop] (fun s : ℝ => s ^ (-3 : ℝ)) := by
    refine hh.2.congr' (by rfl) ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  exact ((h.continuous.comp continuous_real_toNNReal).continuousOn.locallyIntegrableOn
    measurableSet_Ici).integrableOn_of_isBigO_atTop ho
      (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))

/-- The absolute integral of a slice bounds its mean by `K/r`. -/
theorem abs_mean_le_integral (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    |mean h r| ≤ (∫ s in Ici (0 : ℝ), |h s.toNNReal|) * (r : ℝ)⁻¹ := by
  have hr' : 0 < (r : ℝ) := hr
  rw [mean_eq_integral h r hr, abs_mul, abs_inv, abs_of_pos hr', mul_comm]
  gcongr
  calc |∫ s in (0 : ℝ)..(r : ℝ), h s.toNNReal| ≤
      ∫ s in (0 : ℝ)..(r : ℝ), |h s.toNNReal| :=
        intervalIntegral.abs_integral_le_integral_abs hr'.le
    _ = ∫ s in Ioc (0 : ℝ) (r : ℝ), |h s.toNNReal| :=
        intervalIntegral.integral_of_le hr'.le
    _ ≤ ∫ s in Ici (0 : ℝ), |h s.toNNReal| :=
        setIntegral_mono_set (integrableOn_slice h hh).abs
          (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall fun _ ht => ht.1.le)

/-- A reusable tail bound for the difference of a slice and its mean. -/
theorem abs_sub_mean_eventually_le (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in atTop,
      |h s.toNNReal - mean h s.toNNReal| ≤ C * s⁻¹ := by
  obtain ⟨c, hc⟩ := hh.2.bound
  let K := ∫ s in Ici (0 : ℝ), |h s.toNNReal|
  have hK : 0 ≤ K := integral_nonneg fun _ => abs_nonneg _
  refine ⟨|c| + K, add_nonneg (abs_nonneg _) hK, ?_⟩
  filter_upwards [hc, eventually_ge_atTop 1] with s hs hs1
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hp : 0 < s ^ (-3 : ℤ) := zpow_pos hs0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at hs
  have hp1 : s ^ (-3 : ℤ) ≤ s⁻¹ := by
    rw [← Real.rpow_intCast, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hH : |h s.toNNReal| ≤ |c| * s⁻¹ :=
    hs.trans ((mul_le_mul_of_nonneg_right (le_abs_self c) hp.le).trans
      (mul_le_mul_of_nonneg_left hp1 (abs_nonneg c)))
  have hM := abs_mean_le_integral h hh s.toNNReal (Real.toNNReal_pos.2 hs0)
  rw [Real.coe_toNNReal s hs0.le] at hM
  calc |h s.toNNReal - mean h s.toNNReal| ≤ |h s.toNNReal| + |mean h s.toNNReal| := abs_sub _ _
    _ ≤ |c| * s⁻¹ + K * s⁻¹ := add_le_add hH hM
    _ = (|c| + K) * s⁻¹ := by ring

/-- Public global slice bound, including the centre: `|h-hBar| ≤ C/(1+r)`. -/
theorem abs_sub_mean_le (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0,
      |h r - mean h r| ≤ C * (1 + (r : ℝ))⁻¹ := by
  obtain ⟨C, hC, hb⟩ := abs_sub_mean_eventually_le h hh
  obtain ⟨R, hR⟩ := eventually_atTop.1 hb
  let R' := max R 1
  have hcont : Continuous (fun s : ℝ => (1+s) * (h s.toNNReal - mean h s.toNNReal)) :=
    (continuous_const.add continuous_id).mul
      ((h.continuous.comp continuous_real_toNNReal).sub
        ((continuous_mean h).comp continuous_real_toNNReal))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn : ContinuousOn _ (Icc (0 : ℝ) R'))
  refine ⟨max |B| (2*C), (abs_nonneg B).trans (le_max_left _ _), ?_⟩
  intro r
  have hs0 := r.coe_nonneg
  have hs1 : 0 < 1+(r : ℝ) := by linarith
  have hw : (1+(r : ℝ)) * |h r - mean h r| ≤ max |B| (2*C) := by
    by_cases hr : (r : ℝ) ≤ R'
    · have hb' := hB (r : ℝ) ⟨hs0, hr⟩
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hs1, Real.toNNReal_coe] at hb'
      exact hb'.trans ((le_abs_self B).trans (le_max_left _ _))
    · have hr' : R' ≤ (r : ℝ) := (not_le.1 hr).le
      have hsr : 1 ≤ (r : ℝ) := (le_max_right R 1).trans hr'
      have hsp : 0 < (r : ℝ) := zero_lt_one.trans_le hsr
      have ht := hR (r : ℝ) ((le_max_left R 1).trans hr')
      simp only [Real.toNNReal_coe] at ht
      calc (1+(r : ℝ)) * |h r - mean h r| ≤ (1+(r : ℝ)) * (C * (r : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left ht hs1.le
        _ ≤ 2*C := by
          have hfrac : (1+(r : ℝ)) * (r : ℝ)⁻¹ ≤ 2 := by
            rw [← div_eq_mul_inv, div_le_iff₀ hsp]
            linarith
          nlinarith only [mul_le_mul_of_nonneg_left hfrac hC]
        _ ≤ max |B| (2*C) := le_max_right _ _
  rw [← div_eq_mul_inv, le_div_iff₀ hs1]
  simpa only [mul_comm] using hw

/-- Squared slice-minus-mean is integrable on the full radial half-line. -/
theorem integrableOn_sq_sub_mean (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IntegrableOn (fun s : ℝ => (h s.toNNReal - mean h s.toNNReal)^2) (Ici 0) := by
  obtain ⟨C, hC, hb⟩ := abs_sub_mean_eventually_le h hh
  have ho : (fun s : ℝ => (h s.toNNReal - mean h s.toNNReal)^2) =O[atTop]
      (fun s : ℝ => s ^ (-2 : ℝ)) := by
    refine IsBigO.of_bound (C^2) ?_
    filter_upwards [hb, eventually_gt_atTop 0] with s hs hs0
    rw [Real.norm_eq_abs, abs_pow, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    calc |h s.toNNReal - mean h s.toNNReal|^2 ≤ (C * s⁻¹)^2 := by gcongr
      _ = C^2 * s ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        simp only [zpow_neg, zpow_ofNat]
        ring
  exact ((((h.continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean h).comp continuous_real_toNNReal)).pow 2).continuousOn.locallyIntegrableOn
      measurableSet_Ici).integrableOn_of_isBigO_atTop ho
        (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))

/-- (4.5) bounded by the integrable square, since `gBar/g ≤ 1`. -/
theorem mass_le_integral_sq (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    mass h hh r ≤ 2 * π * ∫ s in Ici (0 : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 := by
  have hc : Continuous (fun s : ℝ => (h s.toNNReal - mean h s.toNNReal)^2) :=
    ((h.continuous.comp continuous_real_toNNReal).sub
      ((continuous_mean h).comp continuous_real_toNNReal)).pow 2
  have hf : Continuous (fun s : ℝ => gBar h hh s.toNNReal / g h hh s.toNNReal *
      (h s.toNNReal - mean h s.toNNReal)^2) :=
    (((continuous_gBar h hh).comp continuous_real_toNNReal).div
      ((continuous_g h hh).comp continuous_real_toNNReal) fun _ => (g_pos h hh _).ne').mul hc
  rw [mass_eq_integral]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) pi_pos.le)
  calc (∫ s in (0 : ℝ)..(r : ℝ), gBar h hh s.toNNReal / g h hh s.toNNReal *
      (h s.toNNReal - mean h s.toNNReal)^2) ≤
      ∫ s in (0 : ℝ)..(r : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 := by
        apply intervalIntegral.integral_mono_on r.coe_nonneg (hf.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)
        intro s hs
        exact mul_le_of_le_one_left (sq_nonneg _)
          ((div_le_one (g_pos h hh _)).2 (gBar_le_g h hh _))
    _ = ∫ s in Ioc (0 : ℝ) (r : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 :=
      intervalIntegral.integral_of_le r.coe_nonneg
    _ ≤ ∫ s in Ici (0 : ℝ), (h s.toNNReal - mean h s.toNNReal)^2 :=
      setIntegral_mono_set (integrableOn_sq_sub_mean h hh)
        (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ ht => ht.1.le)

/-- The mass is bounded, tends to the Bondi mass, and has a nonnegative limit. -/
theorem bondiMass_spec (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    BddAbove (Set.range (mass h hh)) ∧
      Tendsto (mass h hh) atTop (𝓝 (bondiMass h hh)) ∧ 0 ≤ bondiMass h hh := by
  have hb : BddAbove (Set.range (mass h hh)) :=
    ⟨2 * π * ∫ s in Ici (0 : ℝ), (h s.toNNReal - mean h s.toNNReal)^2,
      by rintro _ ⟨r, rfl⟩; exact mass_le_integral_sq h hh r⟩
  refine ⟨hb, ?_, ?_⟩
  · exact tendsto_atTop_ciSup (monotone_mass h hh) hb
  · exact (mass_nonneg h hh 0).trans (le_csSup hb ⟨0, rfl⟩)

end XBM

end Christodoulou.Bondi
