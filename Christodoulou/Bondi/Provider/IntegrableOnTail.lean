module
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Christodoulou.Frozen.Radial.MeanEqIntegral
import Christodoulou.Frozen.Radial.ContinuousMean
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.RCLike



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi.Tail
open Christodoulou.Radial

variable (h : C(ℝ≥0, ℝ))

/-- The real lift of the slice. -/
@[expose] noncomputable def H : ℝ → ℝ := fun s => h (Real.toNNReal s)
/-- The real lift of its mean. -/
@[expose] noncomputable def M : ℝ → ℝ := fun s => mean h (Real.toNNReal s)
/-- The integrand of (3.11). -/
@[expose] noncomputable def F : ℝ → ℝ := fun s => (H h s - M h s) ^ 2 / s

theorem continuous_H : Continuous (H h) := h.continuous.comp continuous_real_toNNReal
theorem continuous_M : Continuous (M h) :=
  (continuous_mean h).comp continuous_real_toNNReal

theorem measurable_F : Measurable (F h) :=
  (((continuous_H h).sub (continuous_M h)).pow 2).measurable.div measurable_id

theorem continuousOn_F : ContinuousOn (F h) (Ioi 0) :=
  (((continuous_H h).sub (continuous_M h)).pow 2).continuousOn.div continuousOn_id
    fun _ hs => (ne_of_gt hs)

/-- For `s > 0`, `M s = s⁻¹ ∫₀ˢ H`. -/
theorem M_eq (s : ℝ) (hs : 0 < s) : M h s = s⁻¹ * ∫ t in (0 : ℝ)..s, H h t := by
  have := mean_eq_integral h (Real.toNNReal s) (Real.toNNReal_pos.2 hs)
  rw [Real.coe_toNNReal s hs.le] at this
  exact this

/-- `H s − M s = s⁻¹ ∫₀ˢ (H s − H t) dt` for `s > 0`. -/
theorem sub_M_eq (s : ℝ) (hs : 0 < s) :
    H h s - M h s = s⁻¹ * ∫ t in (0 : ℝ)..s, (H h s - H h t) := by
  rw [M_eq h s hs, intervalIntegral.integral_sub intervalIntegrable_const
    ((continuous_H h).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

/-- Centre estimate: a Lipschitz bound on `[0, 1]` gives `|H s − M s| ≤ K s` on `(0, 1]`. -/
theorem abs_sub_M_le (K : ℝ≥0) (hK : LipschitzOnWith K (H h) (Icc 0 1)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : |H h s - M h s| ≤ K * s := by
  rw [sub_M_eq h s hs.1, abs_mul, abs_inv, abs_of_pos hs.1]
  have hb : ‖∫ t in (0 : ℝ)..s, (H h s - H h t)‖ ≤ (K * s) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hs.1.le] at ht
    have hd := hK.dist_le_mul s ⟨hs.1.le, hs.2⟩ t ⟨ht.1.le, ht.2.trans hs.2⟩
    have hst : |s - t| = s - t := abs_of_nonneg (by linarith [ht.2])
    rw [Real.dist_eq, Real.dist_eq, hst] at hd
    rw [Real.norm_eq_abs]
    calc |H h s - H h t| ≤ K * (s - t) := hd
      _ ≤ K * s := by gcongr; linarith [ht.1]
  rw [sub_zero, abs_of_pos hs.1] at hb
  rw [Real.norm_eq_abs] at hb
  calc s⁻¹ * |∫ t in (0 : ℝ)..s, (H h s - H h t)| ≤ s⁻¹ * (K * s * s) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hs.1.le)
    _ = K * s := by field_simp

theorem integrableOn_F_Ioc (hh : IsSlice h) : IntegrableOn (F h) (Ioc 0 1) := by
  obtain ⟨K, hK⟩ := (hh.1.mono Icc_subset_Ici_self).exists_lipschitzOnWith one_ne_zero
    (convex_Icc 0 1) isCompact_Icc
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) measure_Ioc_lt_top.ne
    (measurable_F h).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have h1 := abs_sub_M_le h K hK s hs
  rw [Real.norm_eq_abs, F, abs_div, abs_of_pos hs.1, abs_pow, div_le_iff₀ hs.1]
  calc |H h s - M h s| ^ 2 ≤ (K * s) ^ 2 := by gcongr
    _ = (K : ℝ) ^ 2 * s * s := by ring
    _ ≤ (K : ℝ) ^ 2 * s := by
        have : (K : ℝ) ^ 2 * s ≥ 0 := mul_nonneg (sq_nonneg _) hs.1.le
        nlinarith [hs.2, hs.1]

/-- `H = O(s⁻³)` turned into a real-power bound. -/
theorem isBigO_H_rpow (hh : IsSlice h) : H h =O[atTop] fun s : ℝ => s ^ (-3 : ℝ) := by
  refine hh.2.congr' (by rfl) ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]

theorem integrableOn_H (hh : IsSlice h) : IntegrableOn (H h) (Ici 0) :=
  ((continuous_H h).continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    (isBigO_H_rpow h hh) (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))

/-- `|M s| ≤ K / s` for `s > 0`, with `K = ∫_{[0,∞)} |H|`. -/
theorem abs_M_le (hh : IsSlice h) (s : ℝ) (hs : 0 < s) :
    |M h s| ≤ (∫ t in Ici (0 : ℝ), |H h t|) * s⁻¹ := by
  rw [M_eq h s hs, abs_mul, abs_inv, abs_of_pos hs, mul_comm]
  gcongr
  calc |∫ t in (0 : ℝ)..s, H h t| ≤ ∫ t in (0 : ℝ)..s, |H h t| :=
        intervalIntegral.abs_integral_le_integral_abs hs.le
    _ = ∫ t in Ioc 0 s, |H h t| := intervalIntegral.integral_of_le hs.le
    _ ≤ ∫ t in Ici (0 : ℝ), |H h t| :=
        setIntegral_mono_set (integrableOn_H h hh).abs
          (Eventually.of_forall fun t => abs_nonneg _)
          (Eventually.of_forall Ioc_subset_Icc_self |>.mono fun t ht => by
            exact fun h' => (Icc_subset_Ici_self (ht h')))

/-- At infinity the integrand of (3.11) is `O(s⁻³)`. -/
theorem isBigO_F (hh : IsSlice h) : F h =O[atTop] fun s : ℝ => s ^ (-3 : ℝ) := by
  obtain ⟨c, hc⟩ := (isBigO_H_rpow h hh).bound
  set K := ∫ t in Ici (0 : ℝ), |H h t|
  refine IsBigO.of_bound ((|c| + K) ^ 2) ?_
  filter_upwards [hc, eventually_ge_atTop 1] with s hs1 hs2
  have spos : 0 < s := by linarith
  have hr3 : 0 < s ^ (-3 : ℝ) := Real.rpow_pos_of_pos spos _
  have hle : s ^ (-3 : ℝ) ≤ s⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hs2 (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr3] at hs1
  have hH : |H h s| ≤ |c| * s⁻¹ :=
    calc |H h s| ≤ c * s ^ (-3 : ℝ) := hs1
      _ ≤ |c| * s ^ (-3 : ℝ) := by gcongr; exact le_abs_self c
      _ ≤ |c| * s⁻¹ := by gcongr
  have hM := abs_M_le h hh s spos
  have hdiff : |H h s - M h s| ≤ (|c| + K) * s⁻¹ :=
    calc |H h s - M h s| ≤ |H h s| + |M h s| := abs_sub _ _
      _ ≤ |c| * s⁻¹ + K * s⁻¹ := add_le_add hH hM
      _ = (|c| + K) * s⁻¹ := by ring
  have h3 : s ^ (-3 : ℝ) = (s ^ 3)⁻¹ := by
    rw [Real.rpow_neg spos.le]
    norm_cast
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr3, F, abs_div, abs_pow, abs_of_pos spos,
    h3]
  calc |H h s - M h s| ^ 2 / s ≤ ((|c| + K) * s⁻¹) ^ 2 / s := by gcongr
    _ = (|c| + K) ^ 2 * (s ^ 3)⁻¹ := by field_simp

theorem integrableOn_F_Ici_one (hh : IsSlice h) : IntegrableOn (F h) (Ici 1) := by
  have hsub : Ici (1 : ℝ) ⊆ Ioi 0 := fun _ hs => mem_Ioi.2 (lt_of_lt_of_le one_pos (mem_Ici.1 hs))
  exact (((continuousOn_F h).mono hsub).locallyIntegrableOn measurableSet_Ici
    ).integrableOn_of_isBigO_atTop (isBigO_F h hh)
    (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))

theorem integrableOn_F_Ioi (hh : IsSlice h) : IntegrableOn (F h) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_F_Ioc h hh).union
    ((integrableOn_F_Ici_one h hh).mono_set Ioi_subset_Ici_self)

end Christodoulou.Bondi.Tail

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial

/-- Well-definedness of (3.11), graph root `P.3.11.tail`: the integrand is integrable on
`(0, ∞)` (`#integrable-pos`), hence on every `(r, ∞)` with `r ≥ 0`. -/
theorem integrableOn_tail {h : C(ℝ≥0, ℝ)} (hh : IsSlice h := by assumption) {r : ℝ≥0} :
    IntegrableOn (fun s : ℝ => (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 / s)
      (Ioi (r : ℝ)) :=
  (Tail.integrableOn_F_Ioi h hh).mono_set (Ioi_subset_Ioi r.2)

end Christodoulou.Bondi.Provider
