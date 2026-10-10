module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Christodoulou.Frozen.Radial.ContinuousMean
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

private theorem continuous_lift (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ × ℝ => H (Real.toNNReal p.1, Real.toNNReal p.2)) :=
  H.continuous.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk
    (continuous_real_toNNReal.comp continuous_snd))

private theorem continuous_mean_curry (H : C(ℝ≥0 × ℝ≥0, ℝ)) {s : ℝ} (hs : 0 < s) :
    Continuous (fun v : ℝ => mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)) := by
  have heq (v : ℝ) := mean_eq_integral (H.curry (Real.toNNReal v))
    (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
  simp only [Real.coe_toNNReal _ hs.le] at heq
  simp_rw [heq]
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_lift H) 0 s)

private theorem exists_radial_lipschitz {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) :
    ∃ K : ℝ≥0, ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
      |H (Real.toNNReal v, Real.toNNReal s) - H (Real.toNNReal v, Real.toNNReal t)|
        ≤ K * |s - t| := by
  have hc := hH.1.mono (show Icc 0 (u₀ : ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆
      Icc 0 (u₀ : ℝ) ×ˢ Ici 0 from fun _ hp => ⟨hp.1, hp.2.1⟩)
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith one_ne_zero
    (convex_Icc _ _ |>.prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  refine ⟨K, fun v hv s hs t ht => ?_⟩
  simpa [Real.dist_eq, Prod.dist_eq] using hK.dist_le_mul (x := (v, s))
    (y := (v, t)) ⟨hv, hs⟩ ⟨hv, ht⟩

private theorem sub_mean_le {f : C(ℝ≥0, ℝ)} {s A : ℝ} (hs : 0 < s)
    (hA : ∀ t ∈ Icc 0 s, |f (Real.toNNReal s) - f (Real.toNNReal t)| ≤ A) :
    |f (Real.toNNReal s) - mean f (Real.toNNReal s)| ≤ A := by
  have hf : Continuous (fun t : ℝ => f (Real.toNNReal t)) :=
    f.continuous.comp continuous_real_toNNReal
  rw [mean_eq_integral f _ (Real.toNNReal_pos.mpr hs), Real.coe_toNNReal _ hs.le]
  have heq : f (Real.toNNReal s) - s⁻¹ * ∫ t in (0 : ℝ)..s, f (Real.toNNReal t) =
      s⁻¹ * ∫ t in (0 : ℝ)..s, (f (Real.toNNReal s) - f (Real.toNNReal t)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hf.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    field_simp
  rw [heq, abs_mul, abs_inv, abs_of_pos hs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := A) (f := fun t => f (Real.toNNReal s) - f (Real.toNNReal t))
    (fun t ht => by
      rw [uIoc_of_le hs.le] at ht
      exact (Real.norm_eq_abs _).trans_le (hA t ⟨ht.1.le, ht.2⟩))
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs] at hb
  calc
    s⁻¹ * |∫ t in (0 : ℝ)..s, (f (Real.toNNReal s) - f (Real.toNNReal t))|
        ≤ s⁻¹ * (A * s) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)
    _ = A := by field_simp

private theorem exists_integral_bound {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ t : ℝ, 0 ≤ t →
      |H (Real.toNNReal v, Real.toNNReal t)| ≤ C * (1 + t) ^ (-3 : ℤ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ s : ℝ, 0 < s →
      |∫ t in (0 : ℝ)..s, H (Real.toNNReal v, Real.toNNReal t)| ≤ B := by
  let w : ℝ → ℝ := fun t => C * (1 + t) ^ (-3 : ℤ)
  have hw : IntegrableOn w (Ioi 0) := by
    have hi := integrableOn_add_rpow_Ioi_of_lt
      (a := (-3 : ℝ)) (c := 0) (m := 1) (by norm_num) (by norm_num)
    change Integrable (fun t : ℝ => C * (1 + t) ^ (-3 : ℤ)) (volume.restrict (Ioi 0))
    convert hi.const_mul C using 1
    ext t
    rw [← Real.rpow_intCast]
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    rw [add_comm]
  have hwpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ w t := by
    intro t ht
    exact mul_nonneg hC (zpow_nonneg (by linarith [mem_Ioi.mp ht]) _)
  refine ⟨∫ t in Ioi 0, w t, integral_nonneg_of_ae
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hwpos t ht), ?_⟩
  intro v hv s hs
  have hf : Continuous (fun t : ℝ => H (Real.toNNReal v, Real.toNNReal t)) :=
    (continuous_lift H).comp (continuous_const.prodMk continuous_id)
  calc
    |∫ t in (0 : ℝ)..s, H (Real.toNNReal v, Real.toNNReal t)|
        ≤ ∫ t in Ioc 0 s, |H (Real.toNNReal v, Real.toNNReal t)| := by
      simpa only [intervalIntegral.integral_of_le hs.le, Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := fun t =>
          H (Real.toNNReal v, Real.toNNReal t)) hs.le
    _ ≤ ∫ t in Ioc 0 s, w t := by
      apply setIntegral_mono_on (hf.abs.intervalIntegrable 0 s).1
        (hw.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
      exact fun t ht => hdec v hv t ht.1.le
    _ ≤ ∫ t in Ioi 0, w t := setIntegral_mono_set hw
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hwpos t ht)
      Ioc_subset_Ioi_self.eventuallySubset

private theorem integrand_small_bound {f : C(ℝ≥0, ℝ)} {s K : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (h : |f (Real.toNNReal s) - mean f (Real.toNNReal s)| ≤ K * s) :
    ‖(f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 / s‖ ≤ K ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hs.le)]
  have hsq : (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 ≤ (K * s) ^ 2 :=
    by simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK hs.le)).mpr h
  apply (div_le_iff₀ hs).mpr
  calc
    (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 ≤ (K * s) ^ 2 := hsq
    _ ≤ K ^ 2 * s := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
      nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hs1)]

private theorem integrand_large_bound {f : C(ℝ≥0, ℝ)} {s D : ℝ}
    (hs : 0 < s) (hD : 0 ≤ D)
    (h : |f (Real.toNNReal s) - mean f (Real.toNNReal s)| ≤ D / s) :
    ‖(f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 / s‖
      ≤ D ^ 2 * s ^ (-3 : ℤ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hs.le)]
  calc
    (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 / s
        ≤ (D / s) ^ 2 / s := by
      apply div_le_div_of_nonneg_right _ hs.le
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg hD hs.le)).mpr h
    _ = D ^ 2 * s ^ (-3 : ℤ) := by
      simp only [zpow_neg, zpow_ofNat]
      field_simp

private theorem exists_tail_majorant {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) :
    ∃ b : ℝ → ℝ, Integrable b ∧ ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ s : ℝ, 0 < s →
      ‖(H (Real.toNNReal v, Real.toNNReal s)
        - mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)) ^ 2 / s‖ ≤ b s := by
  obtain ⟨C, hC⟩ := hH.2.1
  have hC0 : 0 ≤ C := by
    have hz := hC 0 (by positivity) 0
    simp only [NNReal.coe_zero, add_zero, one_zpow, mul_one] at hz
    exact (abs_nonneg _).trans hz
  have hdec : ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ t : ℝ, 0 ≤ t →
      |H (Real.toNNReal v, Real.toNNReal t)| ≤ C * (1 + t) ^ (-3 : ℤ) := by
    intro v hv t ht
    have hv' : Real.toNNReal v ≤ u₀ := by
      exact_mod_cast (show (Real.toNNReal v : ℝ) ≤ (u₀ : ℝ) by
        simpa only [Real.coe_toNNReal _ hv.1] using hv.2)
    simpa only [Real.coe_toNNReal _ ht] using hC (Real.toNNReal v) hv' (Real.toNNReal t)
  obtain ⟨B, hB0, hB⟩ := exists_integral_bound hC0 hdec
  obtain ⟨K, hK⟩ := exists_radial_lipschitz hH
  let b₀ : ℝ → ℝ := (Ioc (0 : ℝ) 1).indicator (fun _ => (K : ℝ) ^ 2)
  let bTail : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun s => (C + B) ^ 2 * s ^ (-3 : ℤ))
  have hi₀ : Integrable b₀ :=
    (integrableOn_const (s := Ioc (0 : ℝ) 1) (C := (K : ℝ) ^ 2)
      measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
  have hiTail : Integrable bTail := by
    have hi := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (c := 1)
      (by norm_num) (by norm_num)
    have hi' : IntegrableOn (fun s : ℝ => (C + B) ^ 2 * s ^ (-3 : ℤ)) (Ioi 1) := by
      change Integrable _ _
      simpa only [Real.rpow_neg_ofNat] using hi.const_mul ((C + B) ^ 2)
    exact hi'.integrable_indicator measurableSet_Ioi
  refine ⟨fun s => b₀ s + bTail s, hi₀.add hiTail, ?_⟩
  intro v hv s hs
  dsimp only
  by_cases hs1 : s ≤ 1
  · have hb : b₀ s + bTail s = (K : ℝ) ^ 2 := by
      simp [b₀, bTail, hs, hs1, not_lt.mpr hs1]
    rw [hb]
    apply integrand_small_bound (f := H.curry (Real.toNNReal v)) hs hs1 K.coe_nonneg
    apply sub_mean_le hs
    intro t ht
    calc
      |H.curry (Real.toNNReal v) (Real.toNNReal s)
          - H.curry (Real.toNNReal v) (Real.toNNReal t)|
          ≤ (K : ℝ) * |s - t| := hK v hv s ⟨hs.le, hs1⟩ t ⟨ht.1, ht.2.trans hs1⟩
      _ ≤ K * s := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
        exact mul_le_mul_of_nonneg_left (sub_le_self _ ht.1) K.coe_nonneg
  · have hs1' : 1 < s := lt_of_not_ge hs1
    have hb : b₀ s + bTail s = (C + B) ^ 2 * s ^ (-3 : ℤ) := by
      simp [b₀, bTail, hs1, hs1']
    rw [hb]
    apply integrand_large_bound (f := H.curry (Real.toNNReal v)) hs (add_nonneg hC0 hB0)
    have hh : |H (Real.toNNReal v, Real.toNNReal s)| ≤ C / s := by
      calc
        |H (Real.toNNReal v, Real.toNNReal s)| ≤ C * (1 + s) ^ (-3 : ℤ) :=
          hdec v hv s hs.le
        _ ≤ C * (1 + s) ^ (-1 : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact zpow_le_zpow_right₀ (by linarith) (by norm_num)
        _ ≤ C / s := by
          rw [zpow_neg_one, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hs (by linarith)) hC0
    have hm : |mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)| ≤ B / s := by
      rw [mean_eq_integral _ _ (Real.toNNReal_pos.mpr hs), Real.coe_toNNReal _ hs.le,
        abs_mul, abs_inv, abs_of_pos hs]
      calc
        s⁻¹ * |∫ t in (0 : ℝ)..s, H.curry (Real.toNNReal v) (Real.toNNReal t)|
            ≤ s⁻¹ * B := mul_le_mul_of_nonneg_left (hB v hv s hs) (inv_nonneg.mpr hs.le)
        _ = B / s := by rw [div_eq_mul_inv, mul_comm]
    exact (abs_sub _ _).trans ((add_le_add hh hm).trans_eq (add_div C B s).symm)


theorem continuousOn_tail_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (r : ℝ≥0) :
    ContinuousOn
      (fun v : ℝ => ∫ s in Ioi (r : ℝ),
        (H (Real.toNNReal v, Real.toNNReal s)
          - mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)) ^ 2 / s)
      (Icc 0 (u₀ : ℝ)) := by
  obtain ⟨b, hb, hbound⟩ := exists_tail_majorant hH
  apply continuousOn_of_dominated (bound := b)
  · intro v _
    have hc : Continuous (fun s : ℝ => H (Real.toNNReal v, Real.toNNReal s)) :=
      (continuous_lift H).comp (continuous_const.prodMk continuous_id)
    have hm : Continuous (fun s : ℝ =>
        mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)) :=
      (continuous_mean _).comp continuous_real_toNNReal
    exact (((hc.sub hm).pow 2).continuousOn.div continuousOn_id
      (fun s hs => ne_of_gt (r.coe_nonneg.trans_lt hs))).aestronglyMeasurable measurableSet_Ioi
  · intro v hv
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs => hbound v hv s (r.coe_nonneg.trans_lt hs))
  · exact hb.integrableOn
  · apply (ae_restrict_mem measurableSet_Ioi).mono
    intro s hs
    have hc : Continuous (fun v : ℝ => H (Real.toNNReal v, Real.toNNReal s)) :=
      (continuous_lift H).comp (continuous_id.prodMk continuous_const)
    have hm := continuous_mean_curry H (r.coe_nonneg.trans_lt hs)
    exact (((hc.sub hm).pow 2).div_const s).continuousOn

end Christodoulou.Bondi
