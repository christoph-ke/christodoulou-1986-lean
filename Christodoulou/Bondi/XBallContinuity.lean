module
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Frozen.Bondi.IntegrableOnTail
import Christodoulou.Frozen.Radial.ContinuousMean
import Christodoulou.Radial.MeanBasic
import Christodoulou.Radial.MeanC1
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint continuity of the metric coefficients in the X-ball

The weighted field bound and the radial derivative bound give a common integrable majorant
for the tail defining `g`. Dominated convergence handles its moving lower endpoint, including
zero. Averaging over the unit interval then gives joint continuity of `ḡ`.
-/

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

private theorem exists_tail_majorant {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    ∃ b : ℝ → ℝ, Integrable b ∧ ∀ v ∈ Icc 0 (u₀ : ℝ), ∀ s : ℝ, 0 < s →
      ‖(H (Real.toNNReal v, Real.toNNReal s)
        - mean (H.curry (Real.toNNReal v)) (Real.toNNReal s)) ^ 2 / s‖ ≤ b s := by
  let C := x
  have hC (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
      |H (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-3 : ℤ) := by
    have hb := hH.2.2 u hu r
    have hw : 0 < (1 + (r : ℝ)) ^ 3 := by positivity
    have hle : (1 + (r : ℝ)) ^ 3 * |H (u, r)| ≤ C :=
      (le_add_of_nonneg_right (by positivity)).trans hb
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
    exact (le_div_iff₀ hw).2 (by simpa only [mul_comm] using hle)
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
  let K : ℝ≥0 := ⟨C, hC0⟩
  have hK (v : ℝ) (hv : v ∈ Icc 0 (u₀ : ℝ)) :
      LipschitzOnWith K (fun s : ℝ => H (Real.toNNReal v, Real.toNNReal s)) (Ici 0) := by
    have hv' : Real.toNNReal v ≤ u₀ := by
      exact_mod_cast (show (Real.toNNReal v : ℝ) ≤ (u₀ : ℝ) by
        simpa only [Real.coe_toNNReal _ hv.1] using hv.2)
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_derivWithin_le
      ((hH.1 _ hv').differentiableOn one_ne_zero)
    intro s hs
    change 0 ≤ s at hs
    have hb := hH.2.2 _ hv' (Real.toNNReal s)
    rw [Real.coe_toNNReal _ hs] at hb
    have hw : (1 : ℝ) ≤ (1 + s) ^ 4 := one_le_pow₀ (by linarith)
    have hd : |derivWithin (fun t : ℝ => H (Real.toNNReal v, Real.toNNReal t))
        (Ici 0) s| ≤ C := by
      calc
        _ ≤ (1 + s) ^ 4 * |derivWithin
            (fun t : ℝ => H (Real.toNNReal v, Real.toNNReal t)) (Ici 0) s| :=
          le_mul_of_one_le_left (abs_nonneg _) hw
        _ ≤ C := (le_add_of_nonneg_left (by positivity)).trans hb
    exact_mod_cast (show ‖derivWithin
      (fun t : ℝ => H (Real.toNNReal v, Real.toNNReal t)) (Ici 0) s‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hd)
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
    exact abs_sub_mean_le _ ((hK v hv).mono Icc_subset_Ici_self) ⟨hs.le, hs1⟩
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

private theorem continuous_tail {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => ∫ s in Ioi (p.2 : ℝ),
      (H (min p.1 u₀, Real.toNNReal s)
        - mean (H.curry (min p.1 u₀)) (Real.toNNReal s)) ^ 2 / s) := by
  classical
  obtain ⟨b, hb, hbound⟩ := exists_tail_majorant hH
  let F (p : ℝ≥0 × ℝ≥0) (s : ℝ) := (Ioi (p.2 : ℝ)).indicator
    (fun s => (H (min p.1 u₀, Real.toNNReal s)
      - mean (H.curry (min p.1 u₀)) (Real.toNNReal s)) ^ 2 / s) s
  have heq (p : ℝ≥0 × ℝ≥0) : (∫ s, F p s) = ∫ s in Ioi (p.2 : ℝ),
      (H (min p.1 u₀, Real.toNNReal s)
        - mean (H.curry (min p.1 u₀)) (Real.toNNReal s)) ^ 2 / s :=
    integral_indicator measurableSet_Ioi
  simp_rw [← heq]
  apply continuous_iff_continuousAt.2
  intro p₀
  apply continuousAt_of_dominated (bound := fun s => ‖b s‖)
  · apply Filter.Eventually.of_forall
    intro p
    have hi := integrableOn_tail _ (hH.isSlice _ (min_le_right p.1 u₀)) p.2
    exact (hi.integrable_indicator measurableSet_Ioi).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro p
    apply Filter.Eventually.of_forall
    intro s
    by_cases hs : (p.2 : ℝ) < s
    · have hu : ((min p.1 u₀ : ℝ≥0) : ℝ) ∈ Icc 0 (u₀ : ℝ) :=
        ⟨(min p.1 u₀).coe_nonneg, by exact_mod_cast min_le_right p.1 u₀⟩
      have hd := hbound _ hu s (p.2.coe_nonneg.trans_lt hs)
      simpa only [F, indicator_of_mem (show s ∈ Ioi (p.2 : ℝ) from hs),
        Real.toNNReal_coe, Real.norm_eq_abs] using
        hd.trans (le_abs_self (b s))
    · simp only [F, indicator_of_notMem (show s ∉ Ioi (p.2 : ℝ) from hs), norm_zero]
      exact norm_nonneg _
  · exact hb.norm
  · filter_upwards [volume.ae_ne (p₀.2 : ℝ)] with s hs
    have hr : Continuous (fun p : ℝ≥0 × ℝ≥0 => (p.2 : ℝ)) :=
      NNReal.continuous_coe.comp continuous_snd
    rcases lt_or_gt_of_ne hs with hs | hs
    · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hr.continuousAt.eventually (lt_mem_nhds hs))] with p hp
      exact indicator_of_notMem (show s ∉ Ioi (p.2 : ℝ) from not_lt.mpr hp.le) _
    · have hs0 : 0 < s := p₀.2.coe_nonneg.trans_lt hs
      have hu : Continuous (fun p : ℝ≥0 × ℝ≥0 => min p.1 u₀) :=
        continuous_fst.min continuous_const
      have hh := H.continuous.comp (hu.prodMk (continuous_const (y := Real.toNNReal s)))
      have hm : Continuous (fun p : ℝ≥0 × ℝ≥0 =>
          mean (H.curry (min p.1 u₀)) (Real.toNNReal s)) := by
        simpa only [Function.comp_def, Real.toNNReal_coe] using
          (continuous_mean_curry H hs0).comp (NNReal.continuous_coe.comp hu)
      apply ((((hh.sub hm).pow 2).div_const s).continuousAt).congr_of_eventuallyEq
      filter_upwards [(hr.continuousAt.eventually (gt_mem_nhds hs))] with p hp
      exact indicator_of_mem (show s ∈ Ioi (p.2 : ℝ) from hp) _

/-- Joint continuity of `g(u, r)` (helper, not an anchor). -/
theorem continuous_gX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => gX hH p.1 p.2) := by
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_tail hH))

/-- Joint continuity of `ḡ(u, r)` (helper used by the provider of the anchor
`continuous_gBarX`). -/
theorem XBall.continuous_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) : Continuous (fun p : ℝ≥0 × ℝ≥0 => gBarX hH p.1 p.2) := by
  have heq (p : ℝ≥0 × ℝ≥0) : gBarX hH p.1 p.2 =
      ∫ t in (0 : ℝ)..1, gX hH p.1 (Real.toNNReal ((p.2 : ℝ) * t)) :=
    mean_eq_integral_unitInterval _ _
  simp_rw [heq]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_gX hH).comp
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)))

end Christodoulou.Bondi
