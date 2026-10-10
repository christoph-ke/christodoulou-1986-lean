module
public import Christodoulou.Bondi.CoefficientRegularity
public import Christodoulou.Frozen.Bondi.HasDerivWithinAtCharacteristic
import Christodoulou.Frozen.Bondi.AbsDeriv2GBarXLe
import Christodoulou.Frozen.Bondi.HasDerivWithinAtHBarX
import Christodoulou.Frozen.Bondi.HasDerivWithinAtDerivGBarX
import Christodoulou.Frozen.Bondi.GLeOne
import Christodoulou.Frozen.Bondi.GPos
import Christodoulou.Frozen.Bondi.HasDerivAtG
import Christodoulou.Bondi.XBallContinuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Radial estimates for the derivative equicontinuity argument

The bounds in this file include the centre. The characteristic estimate retains the
elapsed time, as needed when iterating the derivative modulus inequality.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XEq

/-- A nonempty X-ball has nonnegative radius. -/
theorem x_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) : 0 ≤ x := by
  have hb := hH.2.2 0 bot_le 0
  simp only [NNReal.coe_zero, add_zero, one_pow, one_mul] at hb
  exact (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hb

/-- The unweighted value and radial derivative are bounded by the X-ball radius. -/
theorem value_deriv_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    |H (u, r)| ≤ x ∧
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤ x := by
  have hw (n : ℕ) : 1 ≤ (1 + (r : ℝ)) ^ n :=
    one_le_pow₀ (le_add_of_nonneg_right r.coe_nonneg)
  have hb := hH.2.2 u hu r
  constructor
  · exact (le_mul_of_one_le_left (abs_nonneg _) (hw 3)).trans
      ((le_add_of_nonneg_right (by positivity)).trans hb)
  · exact (le_mul_of_one_le_left (abs_nonneg _) (hw 4)).trans
      ((le_add_of_nonneg_left (by positivity)).trans hb)

/-- The averaged radial derivative is bounded uniformly, including at zero. -/
theorem abs_derivHBarX_le_uniform {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |derivHBarX hH u r| ≤ x / 2 := by
  refine (XCoef.abs_derivHBarX_le hH u r).trans ?_
  apply div_le_div_of_nonneg_left (x_nonneg hH) (by norm_num)
  have : 1 ≤ (1 + (r : ℝ)) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right r.coe_nonneg)
  linarith

/-- The radial coefficient derivative has the uniform bound used in Lemma 3. -/
theorem abs_half_deriv2GBarX_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |1 / 2 * deriv2GBarX hH u r| ≤ π * x ^ 2 / 2 := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hb : |deriv2GBarX hH u r| ≤ π * x ^ 2 := by
    refine (abs_deriv2GBarX_le hH u r).trans ?_
    exact div_le_self (by positivity) (one_le_pow₀ (le_add_of_nonneg_right r.coe_nonneg))
  linarith

/-- Each field in the ball is radially Lipschitz on every physical time slice. -/
theorem abs_sub_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) (r r' : ℝ≥0) :
    |H (u, r) - H (u, r')| ≤ x * |(r : ℝ) - r'| := by
  have hd := (hH.1 u hu).differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hb := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_derivWithin_le hd
    (fun s hs => by
      rw [Real.norm_eq_abs]
      simpa only [Real.coe_toNNReal _ hs] using (value_deriv_le hH u hu s.toNNReal).2)
    r'.coe_nonneg r.coe_nonneg
  simpa only [Real.norm_eq_abs, Real.toNNReal_coe] using hb

/-- The mean is radially Lipschitz with half the field bound. -/
theorem abs_hBarX_sub_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r r' : ℝ≥0) :
    |hBarX u₀ H u r - hBarX u₀ H u r'| ≤ x / 2 * |(r : ℝ) - r'| := by
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) := hasDerivWithinAt_hBarX hH u s.toNNReal
  have hb := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => by simpa only [Real.coe_toNNReal _ hs] using hd s hs)
    (fun s _ => by simpa only [Real.norm_eq_abs] using
      abs_derivHBarX_le_uniform hH u s.toNNReal) r'.coe_nonneg r.coe_nonneg
  simpa only [Real.norm_eq_abs, Real.toNNReal_coe] using hb

/-- The coefficient is radially Lipschitz with its uniform first derivative bound. -/
theorem abs_linearCoeff_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r r' : ℝ≥0) :
    |linearCoeff hH u r - linearCoeff hH u r'| ≤
      π * x ^ 2 / 2 * |(r : ℝ) - r'| := by
  have hb := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => XCoef.hasDerivWithinAt_linearCoeff_real hH u s hs)
    (fun s _ => by simpa only [Real.norm_eq_abs] using
      abs_half_deriv2GBarX_le hH u s.toNNReal) r'.coe_nonneg r.coe_nonneg
  simpa only [Real.norm_eq_abs, Real.toNNReal_coe] using hb

/-- Backward characteristics spread by the exponential of the elapsed time. -/
theorem characteristic_sub_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (t : Icc (0 : ℝ) u₀) (r r' : ℝ≥0) {s : ℝ}
    (hs : s ∈ Icc 0 (t : ℝ)) :
    |characteristic hH t r s - characteristic hH t r' s| ≤
      exp (π / 12 * x ^ 2 * ((t : ℝ) - s)) * |(r : ℝ) - r'| := by
  have hd (z : ℝ) (hz : z ∈ Ici (0 : ℝ)) :=
    hasDerivWithinAt_characteristic hH t z.toNNReal hs
  have hb (z : ℝ) (_hz : z ∈ Ici (0 : ℝ)) :
      ‖exp (∫ v in s..(t : ℝ),
        linearCoeff hH v.toNNReal (characteristic hH t z.toNNReal v).toNNReal)‖ ≤
        exp (π / 12 * x ^ 2 * ((t : ℝ) - s)) := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := (t : ℝ))
      (f := fun v => linearCoeff hH v.toNNReal
        (characteristic hH t z.toNNReal v).toNNReal)
      (C := π / 12 * x ^ 2) (fun v _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (XCoef.linearCoeff_nonneg hH _ _)]
        exact XCoef.linearCoeff_le_uniform hH _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hi
    exact (le_abs_self _).trans hi
  have hh := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => by simpa only [Real.coe_toNNReal _ hz] using hd z hz)
    hb r'.coe_nonneg r.coe_nonneg
  simpa only [Real.norm_eq_abs, Real.toNNReal_coe] using hh

private lemma continuous_radial_deriv {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) :
    ContinuousOn (fun r : ℝ => derivWithin
      (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r) (Ici 0) :=
  (hH.1 u hu).continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)

/-- The centre-safe mean formula transfers any radial derivative modulus with factor one half. -/
theorem abs_derivHBarX_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀)
    {ρ ω : ℝ}
    (hq : ∀ r r' : ℝ≥0, |(r : ℝ) - r'| ≤ ρ →
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r -
        derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r'| ≤ ω)
    (r r' : ℝ≥0) (hr : |(r : ℝ) - r'| ≤ ρ) :
    |derivHBarX hH u r - derivHBarX hH u r'| ≤ ω / 2 := by
  let q := fun r : ℝ => derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r
  have hc (z : ℝ≥0) : ContinuousOn (fun t : ℝ => t * q ((z : ℝ) * t)) (Icc 0 1) := by
    apply continuousOn_id.mul
    exact (continuous_radial_deriv hH u hu).comp
      (continuous_const.mul continuous_id).continuousOn
      (fun t ht => mul_nonneg z.coe_nonneg ht.1)
  rw [XCoef.derivHBarX_eq_integral, XCoef.derivHBarX_eq_integral, min_eq_left hu,
    ← intervalIntegral.integral_sub
      ((hc r).intervalIntegrable_of_Icc zero_le_one)
      ((hc r').intervalIntegrable_of_Icc zero_le_one)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun t => t * q ((r : ℝ) * t) - t * q ((r' : ℝ) * t))
    (g := fun t => t * ω) zero_le_one
    (Filter.Eventually.of_forall fun t ht => by
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1.le]
      apply mul_le_mul_of_nonneg_left _ ht.1.le
      have hrt : |((r : ℝ) * t).toNNReal -
          (((r' : ℝ) * t).toNNReal : ℝ)| ≤ ρ := by
        rw [Real.coe_toNNReal _ (mul_nonneg r.coe_nonneg ht.1.le),
          Real.coe_toNNReal _ (mul_nonneg r'.coe_nonneg ht.1.le),
          ← sub_mul, abs_mul, abs_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_right (abs_nonneg _) ht.2).trans hr
      simpa only [Real.coe_toNNReal _ (mul_nonneg r.coe_nonneg ht.1.le),
        Real.coe_toNNReal _ (mul_nonneg r'.coe_nonneg ht.1.le)] using
        hq (((r : ℝ) * t).toNNReal) (((r' : ℝ) * t).toNNReal) hrt)
    ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
  norm_num [Real.norm_eq_abs, intervalIntegral.integral_mul_const, integral_id] at hi
  linarith only [hi]

private lemma hasDerivAt_gX_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gX hH u t.toNNReal)
      (4 * π * s * gX hH u s.toNNReal * derivHBarX hH u s.toNNReal ^ 2) s := by
  have hd := hasDerivAt_g (H.curry (min u u₀)) (hH.isSlice _ (min_le_right u u₀))
    s.toNNReal (Real.toNNReal_pos.mpr hs)
  rw [Real.coe_toNNReal s hs.le] at hd
  convert hd using 1
  · rfl
  · simp only [derivHBarX, ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hs)),
      Real.coe_toNNReal s hs.le, gX, hBarX, ContinuousMap.curry_apply]
    field_simp

/-- The metric coefficient is radially Lipschitz, with a constant independent of the slice. -/
theorem abs_gX_sub_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r r' : ℝ≥0) :
    |gX hH u r - gX hH u r'| ≤ π * x ^ 2 * |(r : ℝ) - r'| := by
  have hx := x_nonneg hH
  have hb (s : ℝ) (hs : 0 < s) :
      ‖4 * π * s * gX hH u s.toNNReal * derivHBarX hH u s.toNNReal ^ 2‖ ≤
        π * x ^ 2 := by
    have hg0 : 0 ≤ gX hH u s.toNNReal :=
      (g_pos _ (hH.isSlice _ (min_le_right u u₀)) _).le
    have hg1 : gX hH u s.toNNReal ≤ 1 :=
      g_le_one _ (hH.isSlice _ (min_le_right u u₀)) _
    have hβ := XCoef.abs_derivHBarX_le hH u s.toNNReal
    rw [Real.coe_toNNReal _ hs.le] at hβ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 4 * π * s * 1 * (x / (2 * (1 + s) ^ 2)) ^ 2 := by
        have hb2 : derivHBarX hH u s.toNNReal ^ 2 ≤ (x / (2 * (1 + s) ^ 2)) ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hβ
        exact mul_le_mul (mul_le_mul_of_nonneg_left hg1 (by positivity)) hb2
          (sq_nonneg _) (by positivity)
      _ = π * x ^ 2 * (s / (1 + s) ^ 4) := by field_simp; ring
      _ ≤ π * x ^ 2 * 1 := by
        gcongr
        apply (div_le_one (by positivity)).mpr
        have hp : 1 + s ≤ (1 + s) ^ 4 :=
          le_self_pow₀ (by linarith) (by norm_num)
        linarith
      _ = _ := mul_one _
  have hl : LipschitzOnWith (Real.toNNReal (π * x ^ 2))
      (fun s : ℝ => gX hH u s.toNNReal) (Ioi 0) := by
    apply (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hasDerivAt_gX_pos hH u s hs).hasDerivWithinAt)
    intro s hs
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal _ (mul_nonneg pi_pos.le (sq_nonneg x))] using hb s hs
  have hc : Continuous (fun s : ℝ => gX hH u s.toNNReal) :=
    (continuous_gX hH).comp (continuous_const.prodMk continuous_real_toNNReal)
  have hl' := hl.closure hc.continuousOn
  rw [closure_Ioi] at hl'
  have hh := hl'.dist_le_mul (r : ℝ) r.coe_nonneg (r' : ℝ) r'.coe_nonneg
  simpa only [Real.dist_eq, Real.toNNReal_coe,
    Real.coe_toNNReal _ (mul_nonneg pi_pos.le (sq_nonneg x))] using hh

private lemma abs_metric_beta_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀)
    {ρ ω : ℝ}
    (hq : ∀ r r' : ℝ≥0, |(r : ℝ) - r'| ≤ ρ →
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r -
        derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r'| ≤ ω)
    (r r' : ℝ≥0) (hr : |(r : ℝ) - r'| ≤ ρ) :
    |gX hH u r * derivHBarX hH u r ^ 2 -
      gX hH u r' * derivHBarX hH u r' ^ 2| ≤ π * x ^ 4 / 4 * ρ + x / 2 * ω := by
  have hx := x_nonneg hH
  have hρ := (abs_nonneg _).trans hr
  have hω := (abs_nonneg _).trans (hq r r' hr)
  have hg : |gX hH u r'| ≤ 1 := by
    rw [gX, abs_of_pos (g_pos _ (hH.isSlice _ (min_le_right u u₀)) _)]
    exact g_le_one _ (hH.isSlice _ (min_le_right u u₀)) _
  have hgdiff := (abs_gX_sub_le hH u r r').trans
    (mul_le_mul_of_nonneg_left hr (by positivity))
  have hβ := abs_derivHBarX_le_uniform hH u r
  have hβ' := abs_derivHBarX_le_uniform hH u r'
  have hβdiff := abs_derivHBarX_sub_le hH u hu hq r r' hr
  calc
    _ = |(gX hH u r - gX hH u r') * derivHBarX hH u r ^ 2 +
        gX hH u r' * (derivHBarX hH u r - derivHBarX hH u r') *
          (derivHBarX hH u r + derivHBarX hH u r')| := by congr 1; ring
    _ ≤ |gX hH u r - gX hH u r'| * |derivHBarX hH u r| ^ 2 +
        |gX hH u r'| * |derivHBarX hH u r - derivHBarX hH u r'| *
          (|derivHBarX hH u r| + |derivHBarX hH u r'|) := by
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_pow]
      gcongr
      exact abs_add_le _ _
    _ ≤ (π * x ^ 2 * ρ) * (x / 2) ^ 2 + 1 * (ω / 2) * (x / 2 + x / 2) := by
      gcongr
    _ = _ := by ring

/-- The nonsingular second-metric formula transfers the derivative modulus to `a_r`. -/
theorem abs_half_deriv2GBarX_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀)
    {ρ ω : ℝ}
    (hq : ∀ r r' : ℝ≥0, |(r : ℝ) - r'| ≤ ρ →
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r -
        derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r'| ≤ ω)
    (r r' : ℝ≥0) (hr : |(r : ℝ) - r'| ≤ ρ) :
    |1 / 2 * deriv2GBarX hH u r - 1 / 2 * deriv2GBarX hH u r'| ≤
      5 * π ^ 2 * x ^ 4 / 6 * ρ + 5 * π * x / 3 * ω := by
  let F := fun z : ℝ≥0 => gX hH u z * derivHBarX hH u z ^ 2
  let K := π * x ^ 4 / 4 * ρ + x / 2 * ω
  have hc : Continuous F :=
    ((continuous_gX hH).comp (continuous_const.prodMk continuous_id)).mul
      (((XCoef.continuous_derivHBarX hH).comp
        (continuous_const.prodMk continuous_id)).pow 2)
  have hi (z : ℝ≥0) : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * F ((z : ℝ) * t).toNNReal) volume 0 1 :=
    ((continuous_id.pow 2).mul (hc.comp (continuous_real_toNNReal.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 1
  have hF := abs_metric_beta_sub_le hH u hu hq r r' hr
  have hI : |(∫ t in (0 : ℝ)..1, t ^ 2 * F ((r : ℝ) * t).toNNReal) -
      ∫ t in (0 : ℝ)..1, t ^ 2 * F ((r' : ℝ) * t).toNNReal| ≤ K / 3 := by
    rw [← intervalIntegral.integral_sub (hi r) (hi r')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0 : ℝ)) (b := 1)
      (f := fun t => t ^ 2 * F ((r : ℝ) * t).toNNReal -
        t ^ 2 * F ((r' : ℝ) * t).toNNReal)
      (g := fun t => t ^ 2 * K) zero_le_one
      (Filter.Eventually.of_forall fun t ht => by
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
        apply abs_metric_beta_sub_le hH u hu hq
        rw [Real.coe_toNNReal _ (mul_nonneg r.coe_nonneg ht.1.le),
          Real.coe_toNNReal _ (mul_nonneg r'.coe_nonneg ht.1.le),
          ← sub_mul, abs_mul, abs_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_right (abs_nonneg _) ht.2).trans hr)
      (((continuous_id.pow 2).mul continuous_const).intervalIntegrable 0 1)
    norm_num [intervalIntegral.integral_mul_const, integral_pow, Real.norm_eq_abs] at hb
    linarith only [hb]
  have heq (z : ℝ≥0) : 1 / 2 * deriv2GBarX hH u z =
      -4 * π * (∫ t in (0 : ℝ)..1, t ^ 2 * F ((z : ℝ) * t).toNNReal) +
        2 * π * F z := by
    rw [XCoef.deriv2GBarX_eq_integral]
    simp only [F, mul_assoc]
    ring
  rw [heq r, heq r']
  calc
    _ = |(-4 * π) * ((∫ t in (0 : ℝ)..1, t ^ 2 * F ((r : ℝ) * t).toNNReal) -
          ∫ t in (0 : ℝ)..1, t ^ 2 * F ((r' : ℝ) * t).toNNReal) +
        (2 * π) * (F r - F r')| := by congr 1; ring
    _ ≤ (4 * π) * |(∫ t in (0 : ℝ)..1, t ^ 2 * F ((r : ℝ) * t).toNNReal) -
          ∫ t in (0 : ℝ)..1, t ^ 2 * F ((r' : ℝ) * t).toNNReal| +
        (2 * π) * |F r - F r'| := by
      have hh := abs_add_le
        ((-4 * π) * ((∫ t in (0 : ℝ)..1, t ^ 2 * F ((r : ℝ) * t).toNNReal) -
          ∫ t in (0 : ℝ)..1, t ^ 2 * F ((r' : ℝ) * t).toNNReal))
        ((2 * π) * (F r - F r'))
      simpa [abs_mul, abs_of_pos pi_pos] using hh
    _ ≤ (4 * π) * (K / 3) + (2 * π) * K := by
      gcongr
    _ = _ := by dsimp only [K]; ring

end XEq
end Christodoulou.Bondi
