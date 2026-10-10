module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.CoefficientRegularity
import Christodoulou.Radial.MeanBasic
import Christodoulou.Bondi.XBallContinuity
import Christodoulou.Frozen.Bondi.GLeOne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Christodoulou.Bondi.GBasic
import Christodoulou.Bondi.GBarBasic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Lipschitz dependence of the Bondi coefficients on the field

The local estimates (9.30), (9.31), (9.33), and (9.34) follow from the weighted
field difference, the radial mean, and the centre-inclusive integral cancellation.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial Filter Topology XCoef

namespace XLip

-- A general continuous radial mean estimate; no derivative assumption on f.
private theorem mean_decay (f : C(ℝ≥0, ℝ)) {c : ℝ}
    (hf : ∀ r : ℝ≥0, |f r| ≤ c / (1 + (r : ℝ)) ^ 2) (r : ℝ≥0) :
    |mean f r| ≤ c / (1 + (r : ℝ)) := by
  by_cases hr : r = 0
  · subst r
    simpa [mean_zero] using hf 0
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let F := fun s : ℝ => ∫ t in (0 : ℝ)..s, lift f t
  let B := fun s : ℝ => c * s / (1 + s)
  have hF : Continuous F := intervalIntegral.continuous_primitive
    (continuous_lift f).intervalIntegrable 0
  have hB : ContinuousOn B (Ici 0) :=
    (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.add continuousOn_id) (fun s hs => by
        have : 0 ≤ s := hs; dsimp; positivity)
  have hdB (s : ℝ) (hs : 0 < s) : HasDerivAt B (c / (1 + s) ^ 2) s := by
    convert ((hasDerivAt_id s).const_mul c).div ((hasDerivAt_id s).const_add 1)
      (by dsimp; positivity) using 1
    · rfl
    · dsimp; ring
  have hb (s : ℝ) (hs : 0 < s) : |lift f s| ≤ c / (1 + s) ^ 2 := by
    simpa [lift, Real.coe_toNNReal s hs.le] using hf s.toNNReal
  have hle (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : σ * F r ≤ B r := by
    have hm : MonotoneOn (fun s => B s - σ * F s) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (hB.sub (continuousOn_const.mul hF.continuousOn))
        (f' := fun s => c / (1 + s) ^ 2 - σ * lift f s)
      · intro s hs
        rw [interior_Ici] at hs
        exact ((hdB s hs).sub ((hasDerivAt_integral_lift f s).const_mul σ)).hasDerivWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rcases hσ with rfl | rfl
        · have := (le_abs_self (lift f s)).trans (hb s hs); linarith
        · have := (neg_le_abs (lift f s)).trans (hb s hs); linarith
    have h := hm (by simp) r.coe_nonneg r.coe_nonneg
    simpa [F, B] using h
  have ha : |F r| ≤ B r := abs_le.mpr ⟨by linarith [hle (-1) (Or.inr rfl)],
    by simpa using hle 1 (Or.inl rfl)⟩
  change |∫ t in (0 : ℝ)..(r : ℝ), lift f t| ≤ c * (r : ℝ) / (1 + (r : ℝ)) at ha
  rw [← coe_mul_mean, abs_mul, abs_of_pos hrp] at ha
  apply (mul_le_mul_iff_right₀ hrp).mp
  convert ha using 1
  ring

private theorem exp_nonpos_lipschitz {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |exp a - exp b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := exp) (f' := exp) (C := 1)
    (fun s _ => (hasDerivAt_exp s).hasDerivWithinAt)
    (fun s hs => by simpa [Real.norm_eq_abs, abs_of_pos (exp_pos s)] using
      (exp_le_one_iff.mpr hs)) (convex_Iic (0 : ℝ)) hb ha
  simpa [Real.norm_eq_abs] using h

variable {u₀ : ℝ≥0} {x y : ℝ} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}

private theorem hBar_difference (_hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y) (u r : ℝ≥0) :
    |hBarX u₀ H u r - hBarX u₀ K u r| ≤ y / (1 + (r : ℝ)) := by
  let f := H.curry (min u u₀) - K.curry (min u u₀)
  have hf (s : ℝ≥0) : |f s| ≤ y / (1 + (s : ℝ)) ^ 2 := by
    have hw := hY (min u u₀) (min_le_right u u₀) s
    have hp : (1 + (s : ℝ)) ^ 2 ≤ (1 + (s : ℝ)) ^ 3 :=
      pow_le_pow_right₀ (by linarith [s.coe_nonneg]) (by norm_num)
    apply (le_div_iff₀ (by positivity)).mpr
    change |H (min u u₀, s) - K (min u u₀, s)| * _ ≤ y
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans hw
  have h := mean_decay f hf r
  have he : mean f r = hBarX u₀ H u r - hBarX u₀ K u r := by
    have hHi : IntervalIntegrable
        (fun t : ℝ => H (min u u₀, ((r : ℝ) * t).toNNReal)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact (H.curry (min u u₀)).continuous.comp
        (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))
    have hKi : IntervalIntegrable
        (fun t : ℝ => K (min u u₀, ((r : ℝ) * t).toNNReal)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact (K.curry (min u u₀)).continuous.comp
        (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))
    simp only [hBarX, mean_eq_integral_unitInterval]
    exact intervalIntegral.integral_sub hHi hKi
  rwa [he] at h

private theorem residual_bound (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |H (min u u₀, r) - hBarX u₀ H u r| ≤ x * (r : ℝ) / (2 * (1 + (r : ℝ)) ^ 2) := by
  by_cases hr : r = 0
  · subst r; simp [hBarX, mean_zero]
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have h := abs_derivHBarX_le hH u r
  rw [derivHBarX, ite_eq_right hr, abs_div, abs_of_pos hrp] at h
  apply (div_le_iff₀ hrp).mp at h
  convert h using 1
  ring


private theorem tail_difference_pointwise (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u : ℝ≥0) {s : ℝ} (hs : 0 < s) :
    |tailIntegrand (H.curry (min u u₀)) s - tailIntegrand (K.curry (min u u₀)) s| ≤
      2 * x * y / (1 + s) ^ 3 := by
  let a := H (min u u₀, s.toNNReal) - hBarX u₀ H u s.toNNReal
  let b := K (min u u₀, s.toNNReal) - hBarX u₀ K u s.toNNReal
  have ha : |a| ≤ x * s / (2 * (1 + s) ^ 2) := by
    simpa [a, Real.coe_toNNReal s hs.le] using residual_bound hH u s.toNNReal
  have hb : |b| ≤ x * s / (2 * (1 + s) ^ 2) := by
    simpa [b, Real.coe_toNNReal s hs.le] using residual_bound hK u s.toNNReal
  have hab : |a + b| ≤ x * s / (1 + s) ^ 2 := by
    calc
      _ ≤ |a| + |b| := abs_add_le _ _
      _ ≤ x * s / (2 * (1 + s) ^ 2) + x * s / (2 * (1 + s) ^ 2) := add_le_add ha hb
      _ = _ := by
        field_simp
        ring
  have hD : |H (min u u₀, s.toNNReal) - K (min u u₀, s.toNNReal)| ≤ y / (1 + s) := by
    have hw := hY (min u u₀) (min_le_right u u₀) s.toNNReal
    rw [Real.coe_toNNReal s hs.le] at hw
    have hp : 1 + s ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg s]
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans hw
  have hbar : |hBarX u₀ H u s.toNNReal - hBarX u₀ K u s.toNNReal| ≤ y / (1 + s) := by
    simpa [Real.coe_toNNReal s hs.le] using hBar_difference hy hY u s.toNNReal
  have hd : |a - b| ≤ 2 * y / (1 + s) := by
    calc
      _ = |(H (min u u₀, s.toNNReal) - K (min u u₀, s.toNNReal)) -
          (hBarX u₀ H u s.toNNReal - hBarX u₀ K u s.toNNReal)| := by congr 1; dsimp [a, b]; ring
      _ ≤ _ := by
        simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le
          (H (min u u₀, s.toNNReal) - K (min u u₀, s.toNNReal))
          (-(hBarX u₀ H u s.toNNReal - hBarX u₀ K u s.toNNReal)))
      _ ≤ y / (1 + s) + y / (1 + s) := add_le_add hD hbar
      _ = _ := by ring
  change |a ^ 2 / s - b ^ 2 / s| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hs]
  have he : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [he, abs_mul]
  calc
    _ ≤ (2 * y / (1 + s)) * (x * s / (1 + s) ^ 2) / s := by
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul hd hab (abs_nonneg _) (by positivity)
    _ = _ := by field_simp

private theorem tail_majorant (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℝ≥0) :
    IntegrableOn (fun s : ℝ => 2 * x * y / (1 + s) ^ 3) (Ioi (r : ℝ)) ∧
    (∫ s in Ioi (r : ℝ), 2 * x * y / (1 + s) ^ 3) = x * y / (1 + (r : ℝ)) ^ 2 := by
  let F := fun s : ℝ => -(x * y) / (1 + s) ^ 2
  have hd (s : ℝ) (hs : s ∈ Ici (r : ℝ)) :
      HasDerivAt F (2 * x * y / (1 + s) ^ 3) s := by
    have hs0 : 0 ≤ s := r.coe_nonneg.trans hs
    convert (hasDerivAt_const s (-(x * y))).div
      (((hasDerivAt_id s).const_add 1).pow 2) (by dsimp; positivity) using 1
    · rfl
    · dsimp
      field_simp
      ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun s : ℝ => (1 + s)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h := (hi.pow 2).const_mul (-(x * y))
    simpa [F, div_eq_mul_inv, inv_pow] using h
  have hp (s : ℝ) (hs : s ∈ Ioi (r : ℝ)) : 0 ≤ 2 * x * y / (1 + s) ^ 3 := by
    have : 0 ≤ s := r.coe_nonneg.trans hs.le
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp ht, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp ht
  simpa [F, neg_div, neg_neg] using h

/-- Local u-unweighted analogue of [P] (9.30), with time clamping and r=0 included. -/
private theorem gX_difference (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) :
    |gX hH u r - gX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ^ 2 := by
  have hx : 0 ≤ x := le_trans (by positivity) (hH.2.2 0 (by positivity) 0)
  let f := H.curry (min u u₀)
  let k := K.curry (min u u₀)
  let A := ∫ s in Ioi (r : ℝ), tailIntegrand f s
  let B := ∫ s in Ioi (r : ℝ), tailIntegrand k s
  have hA : 0 ≤ A := setIntegral_Ioi_nonneg f r
  have hB : 0 ≤ B := setIntegral_Ioi_nonneg k r
  have hi : |A - B| ≤ x * y / (1 + (r : ℝ)) ^ 2 := by
    dsimp [A, B]
    rw [← integral_sub
      (integrable_tailIntegrand f (hH.isSlice _ (min_le_right u u₀))).integrableOn
      (integrable_tailIntegrand k (hK.isSlice _ (min_le_right u u₀))).integrableOn]
    have hm := tail_majorant hx hy r
    have hn := norm_integral_le_of_norm_le hm.1 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs]
      exact tail_difference_pointwise hH hK hy hY u (r.coe_nonneg.trans_lt hs))
    rw [Real.norm_eq_abs, hm.2] at hn
    exact hn
  change |exp (-(4 * π) * A) - exp (-(4 * π) * B)| ≤ _
  calc
    _ ≤ |-(4 * π) * A - -(4 * π) * B| := exp_nonpos_lipschitz
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hA)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hB)
    _ = (4 * π) * |A - B| := by rw [← mul_sub, abs_mul]; simp [abs_of_nonneg pi_pos.le]
    _ ≤ (4 * π) * (x * y / (1 + (r : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

private theorem mean_sub (f k : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    mean (f - k) r = mean f r - mean k r := by
  have hf : IntervalIntegrable (fun t : ℝ => f (((r : ℝ) * t).toNNReal)) volume 0 1 :=
    (f.continuous.comp (continuous_real_toNNReal.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  have hk : IntervalIntegrable (fun t : ℝ => k (((r : ℝ) * t).toNNReal)) volume 0 1 :=
    (k.continuous.comp (continuous_real_toNNReal.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  simp only [mean_eq_integral_unitInterval]
  exact intervalIntegral.integral_sub hf hk

/-- Local u-unweighted analogue of [P] (9.31), also including the centre. -/
private theorem gBarX_difference (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) :
    |gBarX hH u r - gBarX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) := by
  let f := gMap (H.curry (min u u₀)) (hH.isSlice _ (min_le_right u u₀))
  let k := gMap (K.curry (min u u₀)) (hK.isSlice _ (min_le_right u u₀))
  change |mean f r - mean k r| ≤ _
  rw [← mean_sub]
  apply mean_decay
  intro s
  exact gX_difference hH hK hy hY u s


/-- The cancellation behind local (9.33); no lower radial cutoff. -/
private theorem weighted_integral (r : ℝ) (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r, s / (1 + s) ^ 3) = r ^ 2 / (2 * (1 + r) ^ 2) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 r) :
      HasDerivAt (fun t : ℝ => t ^ 2 / (2 * (1 + t) ^ 2)) (s / (1 + s) ^ 3) s := by
    have hn : 1 + s ≠ 0 := by linarith [hs.1]
    convert ((hasDerivAt_id s).pow 2).div
      ((((hasDerivAt_id s).const_add 1).pow 2).const_mul 2)
      (by positivity : 2 * (1 + s) ^ 2 ≠ 0) using 1
    · ext t
      simp only [Pi.pow_apply, Pi.div_apply, id_eq]
    · dsimp
      field_simp
      ring
  have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 3) (Icc 0 r) := by
    exact continuousOn_id.div (continuousOn_const.add continuousOn_id |>.pow 3)
      (fun s hs => pow_ne_zero 3 (by linarith [hs.1]))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := r) (fun s hs => hd s (by simpa only [uIcc_of_le hr] using hs))
    (hc.intervalIntegrable_of_Icc hr)
  simpa using he

/-- Centre is specified, never inferred by cancellation of r=0. -/
private theorem mean_deriv_difference_bound (C : ℝ) (hC : 0 ≤ C) (D V : ℝ → ℝ)
    (hzero : V 0 = 0)
    (hformula : ∀ r > 0, V r = (∫ s in (0 : ℝ)..r, s * D s) / r ^ 2)
    (hD : ∀ s ≥ 0, |D s| ≤ C / (1 + s) ^ 3)
    (r : ℝ) (hr : 0 ≤ r) : |V r| ≤ C / (2 * (1 + r) ^ 2) := by
  rcases eq_or_lt_of_le hr with he | hp
  · subst r
    simp only [hzero, abs_zero, add_zero, one_pow, mul_one]
    positivity
  rw [hformula r hp, abs_div, abs_of_nonneg (sq_nonneg r)]
  have hc : ContinuousOn (fun s : ℝ => C * (s / (1 + s) ^ 3)) (Icc 0 r) := by
    exact continuousOn_const.mul (continuousOn_id.div
      (continuousOn_const.add continuousOn_id |>.pow 3)
      (fun s hs => pow_ne_zero 3 (by linarith [hs.1])))
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr
    (Filter.Eventually.of_forall (fun s (hs : s ∈ Ioc 0 r) =>
      show ‖s * D s‖ ≤ C * (s / (1 + s) ^ 3) by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs.1]
      calc
        s * |D s| ≤ s * (C / (1 + s) ^ 3) := mul_le_mul_of_nonneg_left (hD s hs.1.le) hs.1.le
        _ = _ := by ring))
    (hc.intervalIntegrable_of_Icc hr)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, weighted_integral r hr] at hi
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  calc
    |∫ s in (0 : ℝ)..r, s * D s| ≤ C * (r ^ 2 / (2 * (1 + r) ^ 2)) := hi
    _ = C / (2 * (1 + r) ^ 2) * r ^ 2 := by ring

private noncomputable def metricDerivative (hH : MemXBall u₀ x H) (u : ℝ≥0)
    (s : ℝ) : ℝ :=
  4 * π * s * gX hH u s.toNNReal * derivHBarX hH u s.toNNReal ^ 2

private theorem continuous_metricDerivative (hH : MemXBall u₀ x H) (u : ℝ≥0) :
    Continuous (metricDerivative hH u) := by
  exact ((continuous_const.mul continuous_id).mul
    ((continuous_gX hH).comp (continuous_const.prodMk continuous_real_toNNReal))).mul
    (((continuous_derivHBarX hH).comp
      (continuous_const.prodMk continuous_real_toNNReal)).pow 2)

private theorem metricDerivative_eq (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    metricDerivative hH u s = 4 * π * gX hH u s.toNNReal *
      tailIntegrand (H.curry (min u u₀)) s := by
  simp only [metricDerivative, derivHBarX,
    ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hs)),
    Real.coe_toNNReal s hs.le, tailIntegrand, hBarX, ContinuousMap.curry_apply]
  field_simp

private theorem hasDerivAt_gX (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gX hH u t.toNNReal) (metricDerivative hH u s) s := by
  rw [metricDerivative_eq hH u hs]
  have hd := hasDerivAt_g (H.curry (min u u₀))
    (hH.isSlice _ (min_le_right u u₀)) s.toNNReal (Real.toNNReal_pos.mpr hs)
  rw [Real.coe_toNNReal s hs.le] at hd
  convert hd using 1
  · rfl
  · dsimp only [tailIntegrand, gX]
    ring

private theorem derivGBarX_integral (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {r : ℝ} (hr : 0 < r) :
    derivGBarX hH u r.toNNReal =
      (∫ s in (0 : ℝ)..r, s * metricDerivative hH u s) / r ^ 2 := by
  let f := gMap (H.curry (min u u₀)) (hH.isSlice _ (min_le_right u u₀))
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => t * (f t.toNNReal - mean f t.toNNReal))
        (s * metricDerivative hH u s) s := by
    have hm := hasDerivAt_mean f s.toNNReal (Real.toNNReal_pos.mpr hs)
    rw [Real.coe_toNNReal s hs.le] at hm
    convert (hasDerivAt_id s).mul ((hasDerivAt_gX hH u hs).sub hm) using 1
    · rfl
    · dsimp [f, gMap, gX]
      field_simp
      ring
  have hc : Continuous (fun t : ℝ => t * (f t.toNNReal - mean f t.toNNReal)) :=
    continuous_id.mul ((f.continuous.comp continuous_real_toNNReal).sub
      ((continuous_mean f).comp continuous_real_toNNReal))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.le
    hc.continuousOn (fun s hs => hd s hs.1)
    ((continuous_id.mul (continuous_metricDerivative hH u)).intervalIntegrable 0 r)
  simp only [zero_mul, sub_zero] at hi
  rw [hi, derivGBarX, ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hr)),
    Real.coe_toNNReal r hr.le]
  change (gX hH u r.toNNReal - gBarX hH u r.toNNReal) / r =
    r * (gX hH u r.toNNReal - gBarX hH u r.toNNReal) / r ^ 2
  field_simp

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |a - c| * |d| := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

private theorem tail_bound (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    |tailIntegrand (H.curry (min u u₀)) s| ≤ x ^ 2 / (4 * (1 + s)) := by
  have hx : 0 ≤ x := le_trans (by positivity) (hH.2.2 0 (by positivity) 0)
  have hb := residual_bound hH u s.toNNReal
  rw [Real.coe_toNNReal s hs.le] at hb
  have hw : 0 < 1 + s := by positivity
  have hpow : s ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg s]
  change |(H (min u u₀, s.toNNReal) - hBarX u₀ H u s.toNNReal) ^ 2 / s| ≤ _
  rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hs]
  calc
    _ ≤ (x * s / (2 * (1 + s) ^ 2)) ^ 2 / s := by
      apply div_le_div_of_nonneg_right _ hs.le
      calc
        _ = |H (min u u₀, s.toNNReal) - hBarX u₀ H u s.toNNReal| ^ 2 :=
          (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = x ^ 2 * s / (4 * (1 + s) ^ 4) := by field_simp; ring
    _ ≤ x ^ 2 * (1 + s) ^ 3 / (4 * (1 + s) ^ 4) := by gcongr
    _ = _ := by field_simp

private theorem metricDerivative_difference (hH : MemXBall u₀ x H)
    (hK : MemXBall u₀ x K) (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    |metricDerivative hH u s - metricDerivative hK u s| ≤
      4 * π * x * (2 + π * x ^ 2) * y / (1 + s) ^ 3 := by
  have hx : 0 ≤ x := le_trans (by positivity) (hH.2.2 0 (by positivity) 0)
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp only [metricDerivative, mul_zero, zero_mul, sub_self, abs_zero]
    positivity
  rw [metricDerivative_eq hH u hs, metricDerivative_eq hK u hs,
    mul_assoc (4 * π), mul_assoc (4 * π), ← mul_sub, abs_mul,
    abs_of_pos (by positivity : 0 < 4 * π)]
  have hg : |gX hH u s.toNNReal| ≤ 1 := by
    rw [gX, abs_of_pos (g_pos _ _ _)]
    exact g_le_one _ _ _
  have hdiff := gX_difference hH hK hy hY u s.toNNReal
  rw [Real.coe_toNNReal s hs.le] at hdiff
  calc
    _ ≤ (4 * π) * (|gX hH u s.toNNReal| *
        |tailIntegrand (H.curry (min u u₀)) s -
          tailIntegrand (K.curry (min u u₀)) s| +
        |gX hH u s.toNNReal - gX hK u s.toNNReal| *
          |tailIntegrand (K.curry (min u u₀)) s|) := by
      exact mul_le_mul_of_nonneg_left (abs_mul_sub_mul_le _ _ _ _) (by positivity)
    _ ≤ (4 * π) * (1 * (2 * x * y / (1 + s) ^ 3) +
        (4 * π * x * y / (1 + s) ^ 2) * (x ^ 2 / (4 * (1 + s)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul hg (tail_difference_pointwise hH hK hy hY u hs)
          (abs_nonneg _) (by norm_num))
        (mul_le_mul hdiff (tail_bound hK u hs) (abs_nonneg _) (by positivity))
    _ = _ := by field_simp

private theorem derivGBarX_difference (hH : MemXBall u₀ x H)
    (hK : MemXBall u₀ x K) (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) :
    |derivGBarX hH u r - derivGBarX hK u r| ≤
      2 * π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2 := by
  have hx : 0 ≤ x := le_trans (by positivity) (hH.2.2 0 (by positivity) 0)
  have hi := mean_deriv_difference_bound (4 * π * x * (2 + π * x ^ 2) * y)
    (by positivity)
    (fun s => metricDerivative hH u s - metricDerivative hK u s)
    (fun s => derivGBarX hH u s.toNNReal - derivGBarX hK u s.toNNReal)
    (by simp only [Real.toNNReal_zero, derivGBarX, ite_true, sub_self])
    (by
      intro s hs
      rw [derivGBarX_integral hH u hs, derivGBarX_integral hK u hs, ← sub_div,
        ← intervalIntegral.integral_sub
          (f := fun t : ℝ => t * metricDerivative hH u t)
          (g := fun t : ℝ => t * metricDerivative hK u t)
          ((continuous_id.mul (continuous_metricDerivative hH u)).intervalIntegrable 0 s)
          ((continuous_id.mul (continuous_metricDerivative hK u)).intervalIntegrable 0 s)]
      congr 2
      ext t
      ring)
    (metricDerivative_difference hH hK hy hY u) (r : ℝ) r.coe_nonneg
  rw [Real.toNNReal_coe] at hi
  convert hi using 1
  field_simp
  ring

private theorem linearSource_difference (hH : MemXBall u₀ x H)
    (hK : MemXBall u₀ x K) (hy : 0 ≤ y)
    (hY : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) :
    |linearSource hH u r - linearSource hK u r| ≤
      π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 3 := by
  have hx : 0 ≤ x := le_trans (by positivity) (hH.2.2 0 (by positivity) 0)
  have hr := r.coe_nonneg
  have hw : 0 < 1 + (r : ℝ) := by positivity
  have hcoeff : |linearCoeff hH u r| ≤ π * x ^ 2 / (6 * (1 + (r : ℝ)) ^ 2) := by
    rw [abs_of_nonneg (linearCoeff_nonneg hH u r)]
    calc
      _ ≤ π / 6 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 :=
        linearCoeff_le hH u r
      _ ≤ π / 6 * x ^ 2 * (1 + (r : ℝ)) / (1 + (r : ℝ)) ^ 3 := by gcongr; linarith
      _ = _ := by field_simp
  have hcd : |linearCoeff hH u r - linearCoeff hK u r| ≤
      π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2 := by
    simp only [linearCoeff, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ (1 / 2) *
          (2 * π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (derivGBarX_difference hH hK hy hY u r) (by norm_num)
      _ = _ := by ring
  change |-(linearCoeff hH u r) * hBarX u₀ H u r -
    -(linearCoeff hK u r) * hBarX u₀ K u r| ≤ _
  have hc := abs_mul_sub_mul_le (-(linearCoeff hH u r)) (hBarX u₀ H u r)
    (-(linearCoeff hK u r)) (hBarX u₀ K u r)
  simp only [abs_neg, neg_sub_neg] at hc
  rw [abs_sub_comm (linearCoeff hK u r) (linearCoeff hH u r)] at hc
  calc
    _ ≤ |linearCoeff hH u r| * |hBarX u₀ H u r - hBarX u₀ K u r| +
        |linearCoeff hH u r - linearCoeff hK u r| * |hBarX u₀ K u r| := hc
    _ ≤ (π * x ^ 2 / (6 * (1 + (r : ℝ)) ^ 2)) * (y / (1 + (r : ℝ))) +
        (π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2) *
          (x / (1 + (r : ℝ))) := by
      exact add_le_add
        (mul_le_mul hcoeff (hBar_difference hy hY u r) (abs_nonneg _) (by positivity))
        (mul_le_mul hcd (abs_hBarX_le hK u r) (abs_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

/-- The local weighted field bound controls the mean, metric coefficients, and source,
including their prescribed centre values. -/
theorem coefficient_y_lipschitz {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K) {y : ℝ}
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) :
    |hBarX u₀ H u r - hBarX u₀ K u r| ≤ y / (1 + (r : ℝ)) ∧
    |gX hH u r - gX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ^ 2 ∧
    |gBarX hH u r - gBarX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ∧
    |derivGBarX hH u r - derivGBarX hK u r| ≤
      2 * π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2 ∧
    |linearSource hH u r - linearSource hK u r| ≤
      π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 3 :=
  by
    have hy₀ : 0 ≤ y := (mul_nonneg (by positivity) (abs_nonneg _)).trans
      (hy 0 (by positivity) 0)
    exact ⟨hBar_difference hy₀ hy u r, gX_difference hH hK hy₀ hy u r,
      gBarX_difference hH hK hy₀ hy u r, derivGBarX_difference hH hK hy₀ hy u r,
      linearSource_difference hH hK hy₀ hy u r⟩

end XLip
end Christodoulou.Bondi
