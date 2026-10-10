module

public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.HasDerivAtMass
public import Christodoulou.Frozen.Bondi.Xi
public import Christodoulou.Frozen.Bondi.HasDerivAtXi
public import Christodoulou.Frozen.Bondi.IntervalIntegrableXi
public import Christodoulou.Frozen.Bondi.HasDerivAtMeanCurry
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.GBar
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.GLeOne
public import Christodoulou.Frozen.Bondi.GBarLeG
public import Christodoulou.Frozen.Bondi.ContinuousG
public import Christodoulou.Frozen.Bondi.IntegrableOnTail
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.MemXBallIsSlice
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.HBarX
public import Christodoulou.Frozen.Bondi.ExistsMemXBallOfIsClassicalSolution
public import Christodoulou.Frozen.Radial.HasDerivAtMean
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Frozen.Radial.ContinuousMean
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Christodoulou.Bondi.GBarBasic
public import Christodoulou.Bondi.GBasic
public import Christodoulou.Bondi.XiBasic
public import Christodoulou.Bondi.CoefficientRegularity
public import Christodoulou.Analysis.StripDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Evolution of the mass

The uniform integrable majorant for the time derivative of the tail integrand permits
differentiation of `g` and `gBar`. A radial flux identity, with its integration constant
fixed at the regular centre, then gives both forms of the mass evolution law (4.6).
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi

open Christodoulou.Radial Christodoulou.Analysis

namespace XME

private noncomputable def timeH (T : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u s : ℝ) : ℝ :=
  fderivWithin ℝ (fun p : ℝ × ℝ => H (p.1.toNNReal, p.2.toNNReal))
    (Icc 0 (T : ℝ) ×ˢ Ici 0) (u, s) (1, 0)

private noncomputable def timeMean (T : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u s : ℝ) : ℝ :=
  s⁻¹ * ∫ t in (0 : ℝ)..s, timeH T H u t

private noncomputable def timeTail (T : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u s : ℝ) : ℝ :=
  2 * (H (u.toNNReal, s.toNNReal) - mean (H.curry u.toNNReal) s.toNNReal) *
    (timeH T H u s - timeMean T H u s) / s

private theorem hasDerivAt_H_time {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ))
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun v : ℝ => H (v.toNNReal, s.toNNReal)) (timeH T H u s) u :=
  hasDerivAt_fst_of_contDiffOn hH.1 hu hs

private theorem continuousOn_timeH {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) :
    ContinuousOn (timeH T H u) (Ici 0) := by
  exact (continuousOn_fderivWithin_apply_of_contDiffOn hH.1 (hu.1.trans hu.2) (1, 0)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun s hs => ⟨⟨hu.1.le, hu.2.le⟩, hs⟩)

private theorem hasDerivAt_mean_time {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ))
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun v : ℝ => mean (H.curry v.toNNReal) s.toNNReal)
      (timeMean T H u s) u := by
  have hd := (hasDerivAt_intervalIntegral_fst_of_contDiffOn hH.1 hu hs.le).const_mul s⁻¹
  convert hd using 1
  · ext v
    rw [mean_eq_integral _ _ (Real.toNNReal_pos.mpr hs), Real.coe_toNNReal _ hs.le]
    rfl
  · rfl

private theorem hasDerivAt_tailIntegrand_time {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ))
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun v : ℝ => tailIntegrand (H.curry v.toNNReal) s)
      (timeTail T H u s) u := by
  convert (((hasDerivAt_H_time hH hu hs.le).sub
    (hasDerivAt_mean_time hH hu hs)).pow 2).div_const s using 1 <;>
    simp [tailIntegrand, timeTail, pow_one, mul_assoc]

private theorem timeH_eq {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) (u : ℝ≥0) (hu : 0 < u) (huT : u < T)
    (hs : IsSlice (H.curry u)) (r : ℝ≥0) (hr : 0 < r) :
    timeH T H u r = 1 / 2 * gBar (H.curry u) hs r * radialDerivative H u r +
      (g (H.curry u) hs r - gBar (H.curry u) hs r) *
        (H (u, r) - mean (H.curry u) r) / (2 * (r : ℝ)) := by
  have hd := hasDerivAt_H_time hH (u := (u : ℝ)) (s := (r : ℝ)) ⟨hu, huT⟩ r.coe_nonneg
  simp only [Real.toNNReal_coe] at hd
  have he := hH.2.2 u hu huT hs r hr
  rw [hd.deriv] at he
  have hdr : radialDerivative H u r =
      deriv (fun s : ℝ => H (u, s.toNNReal)) (r : ℝ) :=
    derivWithin_of_mem_nhds (Ici_mem_nhds (show (0 : ℝ) < r from hr))
  rw [hdr]
  linarith

private theorem timeMean_eq {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) (u : ℝ≥0) (hu : 0 < u) (huT : u < T)
    (hs : IsSlice (H.curry u)) (r : ℝ≥0) (hr : 0 < r) :
    timeMean T H u r =
      1 / 2 * gBar (H.curry u) hs r * ((H (u, r) - mean (H.curry u) r) / (r : ℝ)) +
        xi (H.curry u) hs r / (2 * (r : ℝ)) := by
  have hd := hasDerivAt_mean_time hH (u := (u : ℝ)) ⟨hu, huT⟩ (show (0 : ℝ) < r from hr)
  simp only [Real.toNNReal_coe] at hd
  exact hd.unique (hasDerivAt_mean_curry hH u hu huT hs r hr)

/-- The derivative of the radial flux eliminates both squared terms in (4.6). -/
private theorem hasDerivAt_flux {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) (u : ℝ≥0) (hu : 0 < u) (huT : u < T)
    (hs : IsSlice (H.curry u)) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ =>
      gBar (H.curry u) hs s.toNNReal ^ 2 *
        (H (u, s.toNNReal) - mean (H.curry u) s.toNNReal) ^ 2 -
      xi (H.curry u) hs s.toNNReal ^ 2)
      (4 * gBar (H.curry u) hs r * (H (u, r) - mean (H.curry u) r) *
        (timeH T H u r - timeMean T H u r)) (r : ℝ) := by
  have dH := hasDerivAt_snd_of_contDiffOn hH.1 (u := (u : ℝ)) (s := (r : ℝ))
    ⟨hu, huT⟩ (show (0 : ℝ) < r from hr)
  simp only [Real.toNNReal_coe] at dH
  have hdr : radialDerivative H u r =
      fderivWithin ℝ (fun p : ℝ × ℝ => H (p.1.toNNReal, p.2.toNNReal))
        (Icc 0 (T : ℝ) ×ˢ Ici 0) ((u : ℝ), (r : ℝ)) (0, 1) := by
    exact (derivWithin_of_mem_nhds (Ici_mem_nhds (show (0 : ℝ) < r from hr))).trans dH.deriv
  have dA := dH.sub (hasDerivAt_mean (H.curry u) r hr)
  have hd := (((hasDerivAt_gBar (H.curry u) hs r hr).pow 2).mul (dA.pow 2)).sub
    ((hasDerivAt_xi (H.curry u) hs r hr).pow 2)
  convert hd using 1
  rw [timeH_eq hH u hu huT hs r hr, timeMean_eq hH u hu huT hs r hr, hdr]
  simp only [Pi.sub_apply, Pi.pow_apply, Real.toNNReal_coe, ContinuousMap.curry_apply]
  ring

/-- Exact reduction of the printed evolution law to the time derivative and (4.4). -/
private theorem evolution_mass_of_hasDerivAt (H : C(ℝ≥0 × ℝ≥0, ℝ))
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) (u r : ℝ≥0) (hr : 0 < r)
    (hdu : HasDerivAt (fun v : ℝ => mass (H.curry v.toNNReal) (hs v.toNNReal) r)
      (1 / 2 * gBar (H.curry u) (hs u) r *
        (2 * π * (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r) *
          (H (u, r) - mean (H.curry u) r) ^ 2) -
        π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2) (u : ℝ)) :
    deriv (fun v : ℝ => mass (H.curry v.toNNReal) (hs v.toNNReal) r) (u : ℝ) -
      1 / 2 * gBar (H.curry u) (hs u) r *
        deriv (fun s : ℝ => mass (H.curry u) (hs u) s.toNNReal) (r : ℝ) =
      -(π / g (H.curry u) (hs u) r) * xi (H.curry u) (hs u) r ^ 2 := by
  rw [hdu.deriv, (hasDerivAt_mass (H.curry u) (hs u) r hr).deriv]
  simp only [ContinuousMap.curry_apply]
  ring

private theorem ball_nonneg {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall T x H) : 0 ≤ x := by
  have hb := hX.2.2 0 (by positivity) 0
  simp only [NNReal.coe_zero, add_zero, one_pow, one_mul] at hb
  exact (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hb

private theorem gap_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall T x H) (u : ℝ≥0) (hu : u ≤ T) (r : ℝ≥0) :
    |H (u, r) - mean (H.curry u) r| ≤ x * (r : ℝ) / (1 + (r : ℝ)) ^ 2 := by
  have hb := XCoef.abs_sub_hBarX_le hX u r
  simp only [hBarX, min_eq_left hu] at hb
  apply hb.trans
  exact div_le_div_of_nonneg_left (mul_nonneg (ball_nonneg hX) r.coe_nonneg)
    (by positivity) (by nlinarith [sq_nonneg (1 + (r : ℝ))])

private theorem radial_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall T x H) (u : ℝ≥0) (hu : u ≤ T) (r : ℝ≥0) :
    |radialDerivative H u r| ≤ x := by
  have hb := hX.2.2 u hu r
  change (1 + (r : ℝ)) ^ 3 * |H (u, r)| +
    (1 + (r : ℝ)) ^ 4 * |radialDerivative H u r| ≤ x at hb
  have hw : 1 ≤ (1 + (r : ℝ)) ^ 4 := one_le_pow₀ (by linarith [r.coe_nonneg])
  have hp : 0 ≤ (1 + (r : ℝ)) ^ 3 * |H (u, r)| := by positivity
  nlinarith [abs_nonneg (radialDerivative H u r)]

private theorem timeH_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u s : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (hs : 0 < s) :
    |timeH T H u s| ≤ x := by
  let v := u.toNNReal
  let r := s.toNNReal
  have hv : 0 < v := Real.toNNReal_pos.mpr hu.1
  have hvT : v < T := by exact_mod_cast (show (v : ℝ) < T by simpa [v, hu.1.le] using hu.2)
  have hr : 0 < r := Real.toNNReal_pos.mpr hs
  have hvc : (v : ℝ) = u := Real.coe_toNNReal _ hu.1.le
  have hrc : (r : ℝ) = s := Real.coe_toNNReal _ hs.le
  let hh := hH.isSlice v hvT.le
  have hx := ball_nonneg hX
  have hg : |g (H.curry v) hh r - gBar (H.curry v) hh r| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (gBar_le_g _ hh r))]
    linarith [g_le_one (H.curry v) hh r, gBar_pos (H.curry v) hh r]
  have hb : |gBar (H.curry v) hh r| ≤ 1 := by
    rw [abs_of_pos (gBar_pos _ hh r)]
    exact (gBar_le_g _ hh r).trans (g_le_one _ hh r)
  have hA : |H (v, r) - mean (H.curry v) r| ≤ x * s := by
    have ha := gap_bound hX v hvT.le r
    rw [hrc] at ha
    apply ha.trans
    exact div_le_self (mul_nonneg (ball_nonneg hX) hs.le) (one_le_pow₀ (by linarith))
  rw [← hvc, ← hrc, timeH_eq hH v hv hvT hh r hr, hrc]
  calc
    _ ≤ |1 / 2 * gBar (H.curry v) hh r * radialDerivative H v r| +
        |(g (H.curry v) hh r - gBar (H.curry v) hh r) *
          (H (v, r) - mean (H.curry v) r) / (2 * s)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * 1 * x + 1 * (x * s) / (2 * s) := by
      simp only [abs_mul, abs_div, abs_of_pos hs,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_one]
      gcongr
      exact radial_bound hX v hvT.le r
    _ = x := by field_simp; ring

private theorem timeMean_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u s : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (hs : 0 < s) :
    |timeMean T H u s| ≤ x := by
  rw [timeMean, abs_mul, abs_inv, abs_of_pos hs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := x) (f := timeH T H u) (fun t ht => by
      rw [uIoc_of_le hs.le] at ht
      simpa only [Real.norm_eq_abs] using timeH_bound hH hX hu ht.1)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs] at hb
  calc
    _ ≤ s⁻¹ * (x * s) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)
    _ = x := by field_simp

private theorem timeTail_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u s : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (hs : 0 < s) :
    ‖timeTail T H u s‖ ≤ 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ) := by
  have hx := ball_nonneg hX
  have hv : u.toNNReal ≤ T := by
    exact_mod_cast (show (u.toNNReal : ℝ) ≤ T by simpa [hu.1.le] using hu.2.le)
  have ha := gap_bound hX u.toNNReal hv s.toNNReal
  rw [Real.coe_toNNReal _ hs.le] at ha
  have hd : |timeH T H u s - timeMean T H u s| ≤ 2 * x := by
    exact (abs_sub _ _).trans (by linarith [timeH_bound hH hX hu hs, timeMean_bound hH hX hu hs])
  rw [timeTail, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_pos hs]
  calc
    _ ≤ 2 * (x * s / (1 + s) ^ 2) * (2 * x) / s := by gcongr
    _ = 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ) := by
      simp only [zpow_neg, zpow_ofNat]
      field_simp
      ring

private theorem continuousOn_timeMean {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) :
    ContinuousOn (timeMean T H u) (Ioi 0) := by
  intro s hs
  have hc := continuousOn_timeH hH hu
  have hi : IntervalIntegrable (timeH T H u) volume 0 s :=
    (hc.mono (by rw [uIcc_of_le hs.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    ((hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi _ hs)
    (hc.continuousAt (Ici_mem_nhds hs))
  exact ((continuousAt_inv₀ hs.ne').mul hd.continuousAt).continuousWithinAt

private theorem continuousOn_timeTail {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) :
    ContinuousOn (timeTail T H u) (Ioi 0) := by
  have hA : Continuous (fun s : ℝ =>
      H (u.toNNReal, s.toNNReal) - mean (H.curry u.toNNReal) s.toNNReal) :=
    ((H.curry u.toNNReal).continuous.comp continuous_real_toNNReal).sub
      ((continuous_mean _).comp continuous_real_toNNReal)
  exact ((continuousOn_const.mul hA.continuousOn).mul
    (((continuousOn_timeH hH hu).mono Ioi_subset_Ici_self).sub
      (continuousOn_timeMean hH hu))).div continuousOn_id (fun _ hs => hs.ne')

private theorem majorant_integrable (x : ℝ) :
    IntegrableOn (fun s : ℝ => 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ)) (Ioi 0) := by
  have hi := integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : ℝ)) (c := 0) (m := 1) (by norm_num) (by norm_num)
  change Integrable (fun s : ℝ => 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ)) (volume.restrict (Ioi 0))
  convert hi.const_mul (4 * x ^ 2) using 1
  ext s
  rw [← Real.rpow_intCast]
  norm_num only [Int.cast_neg, Int.cast_ofNat]
  rw [add_comm]

private theorem timeTail_integrable {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) : IntegrableOn (timeTail T H u) (Ioi 0) := by
  apply (majorant_integrable x).mono'
    ((continuousOn_timeTail hH hu).aestronglyMeasurable measurableSet_Ioi)
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => timeTail_bound hH hX hu hs)

private noncomputable def logTime (T : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ) : ℝ :=
  -(4 * π) * ∫ s in Ioi r, timeTail T H u s

private theorem hasDerivAt_g_time {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (r : ℝ≥0) :
    HasDerivAt (fun v : ℝ => g (H.curry v.toNNReal) (hs v.toNNReal) r)
      (g (H.curry u.toNNReal) (hs u.toNNReal) r * logTime T H u r) u := by
  have hsub : Ioi (r : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi r.coe_nonneg
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (r : ℝ)))
    (F := fun v s => tailIntegrand (H.curry v.toNNReal) s)
    (F' := timeTail T H) (bound := fun s => 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ))
    (s := Ioo 0 (T : ℝ)) (Ioo_mem_nhds hu.1 hu.2)
    (Eventually.of_forall (fun v =>
      (measurable_tailIntegrand (H.curry v.toNNReal)).aestronglyMeasurable))
    (integrableOn_tail (H.curry u.toNNReal) (hs u.toNNReal) r)
    (((continuousOn_timeTail hH hu).mono hsub).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun s hs v hv => timeTail_bound hH hX hv (hsub hs)))
    ((majorant_integrable x).mono_set hsub)
    ((ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs v hv => hasDerivAt_tailIntegrand_time hH hv (hsub hs)))).2
  convert (hd.const_mul (-(4 * π))).exp using 1 <;> rfl

private theorem tail_split {f : ℝ → ℝ} (hi : IntegrableOn f (Ioi 0)) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi r, f s = (∫ s in Ioi (0 : ℝ), f s) - ∫ s in (0 : ℝ)..r, f s := by
  rw [intervalIntegral.integral_of_le hr, eq_sub_iff_add_eq, add_comm,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hr)),
    Ioc_union_Ioi_eq_Ioi hr]

private theorem continuousOn_logTime {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (R : ℝ≥0) :
    ContinuousOn (logTime T H u) (Icc 0 (R : ℝ)) := by
  have hi := timeTail_integrable hH hX hu
  have hi' : IntegrableOn (timeTail T H u) (uIcc 0 (R : ℝ)) := by
    rw [uIcc_of_le R.coe_nonneg, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hi.mono_set Ioc_subset_Ioi_self
  have hc := intervalIntegral.continuousOn_primitive_interval hi'
  rw [uIcc_of_le R.coe_nonneg] at hc
  apply ((continuousOn_const (c := -(4 * π))).mul
    ((continuousOn_const (c := ∫ s in Ioi (0 : ℝ), timeTail T H u s)).sub hc)).congr
  intro r hr
  exact congrArg (fun z => -(4 * π) * z) (tail_split hi hr.1)

private theorem hasDerivAt_logTime {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (logTime T H u) (4 * π * timeTail T H u r) r := by
  have hi := timeTail_integrable hH hX hu
  have hc := continuousOn_timeTail hH hu
  have hi' : IntervalIntegrable (timeTail T H u) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hd := intervalIntegral.integral_hasDerivAt_right hi'
    (hc.stronglyMeasurableAtFilter isOpen_Ioi _ hr) (hc.continuousAt (Ioi_mem_nhds hr))
  have hd' := ((hd.const_sub (∫ s in Ioi (0 : ℝ), timeTail T H u s)).const_mul (-(4 * π)))
  have he : logTime T H u =ᶠ[𝓝 r] fun t =>
      -(4 * π) * ((∫ s in Ioi (0 : ℝ), timeTail T H u s) -
        ∫ s in (0 : ℝ)..t, timeTail T H u s) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact congrArg (fun z => -(4 * π) * z) (tail_split hi ht.le)
  convert hd'.congr_of_eventuallyEq he using 1
  ring

private theorem logTime_bound {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    |logTime T H u r| ≤ 4 * π * ∫ s in Ioi (0 : ℝ), 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ) := by
  have hi := majorant_integrable x
  have hb := norm_integral_le_of_norm_le (hi.mono_set (Ioi_subset_Ioi hr))
    ((ae_restrict_mem measurableSet_Ioi).mono
      (fun s hs => timeTail_bound hH hX hu (hr.trans_lt hs)))
  have hm : (∫ s in Ioi r, 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ)) ≤
      ∫ s in Ioi (0 : ℝ), 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ) := by
    apply setIntegral_mono_set hi _ (Ioi_subset_Ioi hr).eventuallySubset
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by positivity)
  rw [logTime, abs_mul, abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (hb.trans hm)) (by positivity)

private theorem hasDerivAt_gBar_time {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    {u : ℝ} (hu : u ∈ Ioo 0 (T : ℝ)) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun v : ℝ => gBar (H.curry v.toNNReal) (hs v.toNNReal) r)
      ((r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ),
        g (H.curry u.toNNReal) (hs u.toNNReal) s.toNNReal * logTime T H u s) u := by
  let K := 4 * π * ∫ s in Ioi (0 : ℝ), 4 * x ^ 2 * (1 + s) ^ (-2 : ℤ)
  have hc (v : ℝ) : Continuous (fun s : ℝ => g (H.curry v.toNNReal) (hs v.toNNReal) s.toNNReal) :=
    (continuous_g _ _).comp continuous_real_toNNReal
  have hdC : ContinuousOn (fun s : ℝ =>
      g (H.curry u.toNNReal) (hs u.toNNReal) s.toNNReal * logTime T H u s) (uIcc 0 (r : ℝ)) := by
    rw [uIcc_of_le r.coe_nonneg]
    exact (hc u).continuousOn.mul (continuousOn_logTime hH hX hu r)
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun v s => g (H.curry v.toNNReal) (hs v.toNNReal) s.toNNReal)
    (F' := fun v s => g (H.curry v.toNNReal) (hs v.toNNReal) s.toNNReal * logTime T H v s)
    (bound := fun _ => K) (s := Ioo 0 (T : ℝ)) (Ioo_mem_nhds hu.1 hu.2)
    (Eventually.of_forall (fun v => (hc v).aestronglyMeasurable))
    ((hc u).intervalIntegrable 0 (r : ℝ))
    (intervalIntegrable_iff.mp (hdC.intervalIntegrable (μ := volume))).aestronglyMeasurable
    ?_ intervalIntegrable_const ?_).2
  · have hd' := hd.const_mul (r : ℝ)⁻¹
    convert hd' using 1
    ext v
    exact gBar_eq_integral _ _ r hr
  · filter_upwards with s hs' v hv
    rw [uIoc_of_le r.coe_nonneg] at hs'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (g_pos _ _ _)]
    calc
      _ ≤ 1 * |logTime T H v s| := mul_le_mul_of_nonneg_right (g_le_one _ _ _) (abs_nonneg _)
      _ ≤ K := by simpa only [one_mul] using logTime_bound hH hX hv hs'.1.le
  · filter_upwards with s hs' v hv
    rw [uIoc_of_le r.coe_nonneg] at hs'
    simpa only [Real.coe_toNNReal _ hs'.1.le] using hasDerivAt_g_time hH hX hs hv s.toNNReal

/-- Continuity of ξ at the centre follows from its already sealed integrability. -/
private theorem continuousOn_xi_real (h : C(ℝ≥0, ℝ)) (hs : IsSlice h) (R : ℝ≥0) :
    ContinuousOn (fun s : ℝ => xi h hs s.toNNReal) (Icc 0 (R : ℝ)) := by
  have hi : IntegrableOn (fun s : ℝ => gBar h hs s.toNNReal *
      (h s.toNNReal - mean h s.toNNReal) / s) (uIcc 0 (R : ℝ)) := by
    rw [uIcc_of_le R.coe_nonneg, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le R.coe_nonneg).mp
      (intervalIntegrable_xi h hs R)
  have hc := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le R.coe_nonneg] at hc
  exact hc.congr (fun s hs' => by simp only [xi, Real.coe_toNNReal _ hs'.1])

/-- The finite radial identity which closes the mass calculation. -/
private theorem integrated_flux {T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hH : IsClassicalSolution T H) (hX : MemXBall T x H)
    (u : ℝ≥0) (hu : 0 < u) (huT : u < T) (hs : IsSlice (H.curry u))
    (r : ℝ≥0) (hr : 0 < r) :
    (r : ℝ) * gBar (H.curry u) hs r * logTime T H u r -
      (∫ s in (0 : ℝ)..(r : ℝ), g (H.curry u) hs s.toNNReal * logTime T H u s) =
        2 * π * (gBar (H.curry u) hs r ^ 2 * (H (u, r) - mean (H.curry u) r) ^ 2 -
          xi (H.curry u) hs r ^ 2) := by
  let B : ℝ → ℝ := fun s => gBar (H.curry u) hs s.toNNReal
  let A : ℝ → ℝ := fun s => H (u, s.toNNReal) - mean (H.curry u) s.toNNReal
  let X : ℝ → ℝ := fun s => xi (H.curry u) hs s.toNNReal
  let Q := logTime T H (u : ℝ)
  let J : ℝ → ℝ := fun s => g (H.curry u) hs s.toNNReal * Q s
  let F : ℝ → ℝ := fun s => s * B s * Q s - (∫ t in (0 : ℝ)..s, J t) -
    2 * π * (B s ^ 2 * A s ^ 2 - X s ^ 2)
  have huI : (u : ℝ) ∈ Ioo 0 (T : ℝ) := ⟨hu, huT⟩
  have hB : Continuous B := (continuous_gBar _ hs).comp continuous_real_toNNReal
  have hA : Continuous A := ((H.curry u).continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean _).comp continuous_real_toNNReal)
  have hXc := continuousOn_xi_real (H.curry u) hs r
  have hQ := continuousOn_logTime hH hX huI r
  have hJ : ContinuousOn J (Icc 0 (r : ℝ)) :=
    ((continuous_g _ hs).comp continuous_real_toNNReal).continuousOn.mul hQ
  have hJi : IntegrableOn J (uIcc 0 (r : ℝ)) := by
    rw [uIcc_of_le r.coe_nonneg]
    exact hJ.integrableOn_compact isCompact_Icc
  have hPc := intervalIntegral.continuousOn_primitive_interval hJi
  rw [uIcc_of_le r.coe_nonneg] at hPc
  have hFc : ContinuousOn F (Icc 0 (r : ℝ)) :=
    (((continuousOn_id.mul hB.continuousOn).mul hQ).sub hPc).sub
      (continuousOn_const.mul (((hB.pow 2).mul (hA.pow 2)).continuousOn.sub (hXc.pow 2)))
  have hFd : ∀ s ∈ Ioo 0 (r : ℝ), HasDerivAt F 0 s := by
    intro s hs'
    have hs0 := hs'.1
    let t := s.toNNReal
    have ht : 0 < t := Real.toNNReal_pos.mpr hs0
    have htc : (t : ℝ) = s := Real.coe_toNNReal _ hs0.le
    have dB := hasDerivAt_gBar (H.curry u) hs t ht
    rw [htc] at dB
    have dQ := hasDerivAt_logTime hH hX huI hs0
    have dP : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z, J t) (J s) s :=
      intervalIntegral.integral_hasDerivAt_right
        (hJ.mono (by
          rw [uIcc_of_le hs0.le]
          exact Icc_subset_Icc le_rfl hs'.2.le)).intervalIntegrable
        ((hJ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo _ hs')
        (hJ.continuousAt (Icc_mem_nhds hs'.1 hs'.2))
    have dW := hasDerivAt_flux hH u hu huT hs t ht
    rw [htc] at dW
    have hd := ((((hasDerivAt_id s).mul dB).mul dQ).sub dP).sub (dW.const_mul (2 * π))
    convert hd using 1
    · rfl
    · dsimp [B, A, X, Q, J]
      rw [timeTail]
      simp only [Real.toNNReal_coe]
      dsimp only [t]
      field_simp [hs0.ne']
      ring
  have hF0 : F 0 = 0 := by simp [F, B, A, X, xi_zero, mean_zero]
  obtain ⟨s, hs', hd⟩ := exists_hasDerivAt_eq_slope F (fun _ => (0 : ℝ))
    (show (0 : ℝ) < r from hr) hFc hFd
  have hFr : F r = 0 := by
    rw [hF0, sub_zero, sub_zero] at hd
    exact (div_eq_zero_iff.mp hd.symm).resolve_right (ne_of_gt (show (0 : ℝ) < r from hr))
  dsimp [F, B, A, X, Q] at hFr
  simp only [Real.toNNReal_coe] at hFr
  exact sub_eq_zero.mp hFr

/-- The interior time derivative of the mass, in the solved form of (4.6). -/
theorem hasDerivAt_mass_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun v : ℝ => mass (H.curry (Real.toNNReal v)) (hs (Real.toNNReal v)) r)
      (1 / 2 * gBar (H.curry u) (hs u) r
          * (2 * π * (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r)
            * (H (u, r) - mean (H.curry u) r) ^ 2)
        - π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2) (u : ℝ) := by
  obtain ⟨x, hX⟩ := exists_memXBall_of_isClassicalSolution hH ⟨C, hd⟩
  have huI : (u : ℝ) ∈ Ioo 0 (u₀ : ℝ) := ⟨hu, hu₀⟩
  have dG := hasDerivAt_g_time hH hX hs huI r
  have dB := hasDerivAt_gBar_time hH hX hs huI r hr
  simp only [Real.toNNReal_coe] at dG dB
  have hg := (g_pos (H.curry u) (hs u) r).ne'
  have hflux := integrated_flux hH hX u hu hu₀ (hs u) r hr
  have dM := ((dB.div dG (by simpa only [Real.toNNReal_coe] using hg)).const_sub 1).const_mul
    ((r : ℝ) / 2)
  convert dM using 1
  · rfl
  · simp only [Real.toNNReal_coe]
    calc
      _ = (π / g (H.curry u) (hs u) r) *
          (gBar (H.curry u) (hs u) r ^ 2 * (H (u, r) - mean (H.curry u) r) ^ 2 -
            xi (H.curry u) (hs u) r ^ 2) := by ring
      _ = ((r : ℝ) * gBar (H.curry u) (hs u) r * logTime u₀ H u r -
          (∫ s in (0 : ℝ)..(r : ℝ), g (H.curry u) (hs u) s.toNNReal * logTime u₀ H u s)) /
          (2 * g (H.curry u) (hs u) r) := by rw [hflux]; ring
      _ = _ := by
        field_simp [hg, ne_of_gt (show (0 : ℝ) < r from hr)]
        ring

/-- The mass evolution law (4.6), with the transport derivative written explicitly. -/
theorem evolution_mass {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (r : ℝ≥0) (hr : 0 < r) :
    deriv (fun v : ℝ => mass (H.curry (Real.toNNReal v)) (hs (Real.toNNReal v)) r) (u : ℝ)
        - 1 / 2 * gBar (H.curry u) (hs u) r
          * deriv (fun s : ℝ => mass (H.curry u) (hs u) (Real.toNNReal s)) (r : ℝ)
      = -(π / g (H.curry u) (hs u) r) * xi (H.curry u) (hs u) r ^ 2 := by
  exact evolution_mass_of_hasDerivAt H hs u r hr
    (hasDerivAt_mass_curry hH hs hd u hu hu₀ r hr)

end XME

end Christodoulou.Bondi
