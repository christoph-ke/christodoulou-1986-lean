module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.WeightedCoefficients
import Christodoulou.Frozen.Bondi.LinearStepDifferenceIntegral
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicEqAddIntegral
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.ContinuousGBarX
import Christodoulou.Bondi.CoefficientRegularity
import Christodoulou.Frozen.Bondi.ContinuousDerivHBarX
import Christodoulou.Radial.MeanBasic
import Christodoulou.Bondi.XBallContinuity
import Christodoulou.Frozen.Bondi.GLeOne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Christodoulou.Bondi.GBasic
import Christodoulou.Bondi.GBarBasic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
open MeasureTheory Christodoulou.Radial

namespace XWL

-- A general continuous radial mean estimate; no derivative assumption on f.
private theorem mean_decay (f : C(ℝ≥0, ℝ)) {b c : ℝ} (hb : 0 < b)
    (hf : ∀ r : ℝ≥0, |f r| ≤ c / (b + (r : ℝ)) ^ 2) (r : ℝ≥0) :
    |mean f r| ≤ c / (b * (b + (r : ℝ))) := by
  by_cases hr : r = 0
  · subst r
    simpa [mean_zero, pow_two] using hf 0
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let F := fun s : ℝ => ∫ t in (0 : ℝ)..s, lift f t
  let B := fun s : ℝ => c * s / (b * (b + s))
  have hF : Continuous F := intervalIntegral.continuous_primitive
    (continuous_lift f).intervalIntegrable 0
  have hB : ContinuousOn B (Ici 0) :=
    (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.mul (continuousOn_const.add continuousOn_id)) (fun s hs => by
        have : 0 ≤ s := hs; dsimp; positivity)
  have hdB (s : ℝ) (hs : 0 < s) : HasDerivAt B (c / (b + s) ^ 2) s := by
    convert ((hasDerivAt_id s).const_mul c).div (((hasDerivAt_id s).const_add b).const_mul b)
      (by dsimp; positivity) using 1
    · rfl
    · dsimp; field_simp; ring
  have hb (s : ℝ) (hs : 0 < s) : |lift f s| ≤ c / (b + s) ^ 2 := by
    simpa [lift, Real.coe_toNNReal s hs.le] using hf s.toNNReal
  have hle (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : σ * F r ≤ B r := by
    have hm : MonotoneOn (fun s => B s - σ * F s) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (hB.sub (continuousOn_const.mul hF.continuousOn))
        (f' := fun s => c / (b + s) ^ 2 - σ * lift f s)
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
  change |∫ t in (0 : ℝ)..(r : ℝ), lift f t| ≤ c * (r : ℝ) / (b * (b + (r : ℝ))) at ha
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

private noncomputable abbrev base (T u : ℝ≥0) : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2

private lemma base_pos (T u : ℝ≥0) : 0 < base T u := by positivity

private lemma base_one (T u : ℝ≥0) : 1 ≤ base T u := by
  dsimp [base]
  linarith only [(min u T).coe_nonneg]

variable {u₀ : ℝ≥0} {x y : ℝ} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}

private theorem hBar_difference (_hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y) (u r : ℝ≥0) :
    |hBarX u₀ H u r - hBarX u₀ K u r| ≤
      y / (base u₀ u ^ 2 * (base u₀ u + (r : ℝ))) := by
  let b := base u₀ u
  have bp : 0 < b := base_pos _ _
  let f := H.curry (min u u₀) - K.curry (min u u₀)
  have hf (t : ℝ≥0) : |f t| ≤ (y / b) / (b + (t : ℝ)) ^ 2 := by
    have hw := hY (min u u₀) (min_le_right u u₀) t
    have he : primeWeight (min u u₀) t = b + (t : ℝ) := by
      dsimp [primeWeight, b, base]
      ring
    rw [he] at hw
    have ht := t.coe_nonneg
    have hp : b * (b + (t : ℝ)) ^ 2 ≤ (b + (t : ℝ)) ^ 3 := by
      nlinarith only [mul_nonneg ht (sq_nonneg (b + (t : ℝ)))]
    have hle := (mul_le_mul_of_nonneg_right hp
      (abs_nonneg (H (min u u₀, t) - K (min u u₀, t)))).trans hw
    change |H (min u u₀, t) - K (min u u₀, t)| ≤ _
    rw [div_div]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hle
  have h := mean_decay f bp hf r
  have he : mean f r = hBarX u₀ H u r - hBarX u₀ K u r := by
    have hHi : IntervalIntegrable
        (fun t : ℝ => H (min u u₀, ((r : ℝ) * t).toNNReal)) volume 0 1 :=
      ((H.curry (min u u₀)).continuous.comp
        (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    have hKi : IntervalIntegrable
        (fun t : ℝ => K (min u u₀, ((r : ℝ) * t).toNNReal)) volume 0 1 :=
      ((K.curry (min u u₀)).continuous.comp
        (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    simp only [hBarX, mean_eq_integral_unitInterval]
    exact intervalIntegral.integral_sub hHi hKi
  rw [he] at h
  convert h using 1
  field_simp
  ring

private theorem residual_bound (hH : MemXPrimeBall u₀ x H) (u r : ℝ≥0) :
    |H (min u u₀, r) - hBarX u₀ H u r| ≤
      x * (r : ℝ) / (2 * base u₀ u ^ 2 * (base u₀ u + (r : ℝ)) ^ 2) :=
  XWC.abs_sub_hBarX_le hH u r

private theorem tail_difference_pointwise (hH : MemXPrimeBall u₀ x H)
    (hK : MemXPrimeBall u₀ x K) (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y) (u : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    |tailIntegrand (H.curry (min u u₀)) t - tailIntegrand (K.curry (min u u₀)) t| ≤
      2 * x * y / (base u₀ u ^ 4 * (base u₀ u + t) ^ 3) := by
  let b := base u₀ u
  have bp : 0 < b := base_pos _ _
  let a := H (min u u₀, t.toNNReal) - hBarX u₀ H u t.toNNReal
  let c := K (min u u₀, t.toNNReal) - hBarX u₀ K u t.toNNReal
  have ha : |a| ≤ x * t / (2 * b ^ 2 * (b + t) ^ 2) := by
    simpa only [a, Real.coe_toNNReal t ht.le] using residual_bound hH u t.toNNReal
  have hc : |c| ≤ x * t / (2 * b ^ 2 * (b + t) ^ 2) := by
    simpa only [c, Real.coe_toNNReal t ht.le] using residual_bound hK u t.toNNReal
  have hac : |a + c| ≤ x * t / (b ^ 2 * (b + t) ^ 2) := by
    calc
      _ ≤ |a| + |c| := abs_add_le _ _
      _ ≤ _ := add_le_add ha hc
      _ = _ := by field_simp; ring
  have hD : |H (min u u₀, t.toNNReal) - K (min u u₀, t.toNNReal)| ≤
      y / (b ^ 2 * (b + t)) := by
    have hw := hY (min u u₀) (min_le_right u u₀) t.toNNReal
    have he : primeWeight (min u u₀) t.toNNReal = b + t := by
      dsimp only [primeWeight, b, base]
      rw [Real.coe_toNNReal t ht.le]
      ring
    rw [he] at hw
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ |H (min u u₀, t.toNNReal) - K (min u u₀, t.toNNReal)| * (b + t) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hbt : b ≤ b + t := by linarith only [ht]
        calc
          _ = b ^ 2 * (b + t) := rfl
          _ ≤ (b + t) ^ 2 * (b + t) := by gcongr
          _ = _ := by ring
      _ ≤ y := by simpa only [mul_comm] using hw
  have hbar : |hBarX u₀ H u t.toNNReal - hBarX u₀ K u t.toNNReal| ≤
      y / (b ^ 2 * (b + t)) := by
    simpa only [Real.coe_toNNReal t ht.le] using hBar_difference hy hY u t.toNNReal
  have hd : |a - c| ≤ 2 * y / (b ^ 2 * (b + t)) := by
    calc
      _ = |(H (min u u₀, t.toNNReal) - K (min u u₀, t.toNNReal)) -
          (hBarX u₀ H u t.toNNReal - hBarX u₀ K u t.toNNReal)| := by
        congr 1
        dsimp [a, c]
        ring
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add hD hbar
      _ = _ := by ring
  change |a ^ 2 / t - c ^ 2 / t| ≤ _
  rw [← sub_div, abs_div, abs_of_pos ht]
  have he : a ^ 2 - c ^ 2 = (a - c) * (a + c) := by ring
  rw [he, abs_mul]
  calc
    _ ≤ (2 * y / (b ^ 2 * (b + t))) * (x * t / (b ^ 2 * (b + t) ^ 2)) / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      exact mul_le_mul hd hac (abs_nonneg _) (by positivity)
    _ = _ := by change _ = 2 * x * y / (b ^ 4 * (b + t) ^ 3); field_simp

private theorem tail_majorant (b : ℝ) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℝ≥0) :
    IntegrableOn (fun s : ℝ => 2 * x * y / (b ^ 4 * (b + s) ^ 3)) (Ioi (r : ℝ)) ∧
    (∫ s in Ioi (r : ℝ), 2 * x * y / (b ^ 4 * (b + s) ^ 3)) =
      x * y / (b ^ 4 * (b + (r : ℝ)) ^ 2) := by
  let F := fun s : ℝ => -(x * y / b ^ 4) / (b + s) ^ 2
  have hd (s : ℝ) (hs : s ∈ Ici (r : ℝ)) :
      HasDerivAt F (2 * x * y / (b ^ 4 * (b + s) ^ 3)) s := by
    have hs0 : 0 ≤ s := r.coe_nonneg.trans hs
    convert (hasDerivAt_const s (-(x * y / b ^ 4))).div
      (((hasDerivAt_id s).const_add b).pow 2) (by dsimp; positivity) using 1
    · rfl
    · dsimp
      field_simp
      ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun s : ℝ => (b + s)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop b tendsto_id)
    have h := (hi.pow 2).const_mul (-(x * y / b ^ 4))
    simpa [F, div_eq_mul_inv, inv_pow] using h
  have hp (s : ℝ) (hs : s ∈ Ioi (r : ℝ)) : 0 ≤ 2 * x * y / (b ^ 4 * (b + s) ^ 3) := by
    have : 0 ≤ s := r.coe_nonneg.trans hs.le
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp ht, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp ht
  simpa [F, neg_div, neg_neg, div_div] using h

/-- Weighted (9.30), with time clamping and r=0 included. -/
private theorem gX_difference (hH : MemXPrimeBall u₀ x H) (hK : MemXPrimeBall u₀ x K)
    (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y)
    (u r : ℝ≥0) :
    |gX hH.1 u r - gX hK.1 u r| ≤ 4 * π * x * y / (base u₀ u ^ 4 * (base u₀ u + (r : ℝ)) ^ 2) := by
  have hx : 0 ≤ x := XWC.x_nonneg hH
  let f := H.curry (min u u₀)
  let k := K.curry (min u u₀)
  let A := ∫ s in Ioi (r : ℝ), tailIntegrand f s
  let B := ∫ s in Ioi (r : ℝ), tailIntegrand k s
  have hA : 0 ≤ A := setIntegral_Ioi_nonneg f r
  have hB : 0 ≤ B := setIntegral_Ioi_nonneg k r
  have hi : |A - B| ≤ x * y / (base u₀ u ^ 4 * (base u₀ u + (r : ℝ)) ^ 2) := by
    dsimp [A, B]
    rw [← integral_sub
      (integrable_tailIntegrand f (hH.1.isSlice _ (min_le_right u u₀))).integrableOn
      (integrable_tailIntegrand k (hK.1.isSlice _ (min_le_right u u₀))).integrableOn]
    have hm := tail_majorant (base u₀ u) (base_pos _ _) hx hy r
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
    _ ≤ (4 * π) * (x * y / (base u₀ u ^ 4 * (base u₀ u + (r : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
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

/-- Weighted (9.31), also including the centre. -/
private theorem gBarX_difference (hH : MemXPrimeBall u₀ x H) (hK : MemXPrimeBall u₀ x K)
    (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y)
    (u r : ℝ≥0) :
    |gBarX hH.1 u r - gBarX hK.1 u r| ≤
      4 * π * x * y / (base u₀ u ^ 5 * (base u₀ u + (r : ℝ))) := by
  let f := gMap (H.curry (min u u₀)) (hH.1.isSlice _ (min_le_right u u₀))
  let k := gMap (K.curry (min u u₀)) (hK.1.isSlice _ (min_le_right u u₀))
  change |mean f r - mean k r| ≤ _
  rw [← mean_sub]
  have hm := mean_decay (f - k) (base_pos u₀ u) (fun s => by
    have hd := gX_difference hH hK hy hY u s
    change |(f - k) s| ≤ _ at hd
    rw [← div_div] at hd
    exact hd) r
  convert hm using 1
  field_simp


/-- The cancellation behind weighted (9.33); no lower radial cutoff. -/
private theorem weighted_integral (b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r, s / (b + s) ^ 3) = r ^ 2 / (2 * b * (b + r) ^ 2) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 r) :
      HasDerivAt (fun t : ℝ => t ^ 2 / (2 * b * (b + t) ^ 2)) (s / (b + s) ^ 3) s := by
    have hn : b + s ≠ 0 := by linarith only [hb, hs.1]
    convert ((hasDerivAt_id s).pow 2).div
      ((((hasDerivAt_id s).const_add b).pow 2).const_mul (2 * b))
      (by positivity : 2 * b * (b + s) ^ 2 ≠ 0) using 1
    · ext t
      simp only [Pi.pow_apply, Pi.div_apply, id_eq]
    · dsimp
      field_simp
      ring
  have hc : ContinuousOn (fun s : ℝ => s / (b + s) ^ 3) (Icc 0 r) := by
    exact continuousOn_id.div (continuousOn_const.add continuousOn_id |>.pow 3)
      (fun s hs => pow_ne_zero 3 (by linarith only [hb, hs.1]))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := r) (fun s hs => hd s (by simpa only [uIcc_of_le hr] using hs))
    (hc.intervalIntegrable_of_Icc hr)
  simpa using he

/-- Centre is specified, never inferred by cancellation of r=0. -/
private theorem mean_deriv_difference_bound (b : ℝ) (hb : 0 < b) (C : ℝ) (hC : 0 ≤ C) (D V : ℝ → ℝ)
    (hzero : V 0 = 0)
    (hformula : ∀ r > 0, V r = (∫ s in (0 : ℝ)..r, s * D s) / r ^ 2)
    (hD : ∀ s ≥ 0, |D s| ≤ C / (b + s) ^ 3)
    (r : ℝ) (hr : 0 ≤ r) : |V r| ≤ C / (2 * b * (b + r) ^ 2) := by
  rcases eq_or_lt_of_le hr with he | hp
  · subst r
    simp only [hzero, abs_zero, add_zero]
    positivity
  rw [hformula r hp, abs_div, abs_of_nonneg (sq_nonneg r)]
  have hc : ContinuousOn (fun s : ℝ => C * (s / (b + s) ^ 3)) (Icc 0 r) := by
    exact continuousOn_const.mul (continuousOn_id.div
      (continuousOn_const.add continuousOn_id |>.pow 3)
      (fun s hs => pow_ne_zero 3 (by linarith only [hb, hs.1])))
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr
    (Filter.Eventually.of_forall (fun s (hs : s ∈ Ioc 0 r) =>
      show ‖s * D s‖ ≤ C * (s / (b + s) ^ 3) by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs.1]
      calc
        s * |D s| ≤ s * (C / (b + s) ^ 3) := mul_le_mul_of_nonneg_left (hD s hs.1.le) hs.1.le
        _ = _ := by ring))
    (hc.intervalIntegrable_of_Icc hr)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, weighted_integral b r hb hr] at hi
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  calc
    |∫ s in (0 : ℝ)..r, s * D s| ≤ C * (r ^ 2 / (2 * b * (b + r) ^ 2)) := hi
    _ = C / (2 * b * (b + r) ^ 2) * r ^ 2 := by ring

private noncomputable def metricDerivative (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0)
    (s : ℝ) : ℝ :=
  4 * π * s * gX hH.1 u s.toNNReal * derivHBarX hH.1 u s.toNNReal ^ 2

private theorem continuous_metricDerivative (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0) :
    Continuous (metricDerivative hH u) := by
  exact ((continuous_const.mul continuous_id).mul
    ((continuous_gX hH.1).comp (continuous_const.prodMk continuous_real_toNNReal))).mul
    (((continuous_derivHBarX hH.1).comp
      (continuous_const.prodMk continuous_real_toNNReal)).pow 2)

private theorem metricDerivative_eq (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    metricDerivative hH u s = 4 * π * gX hH.1 u s.toNNReal *
      tailIntegrand (H.curry (min u u₀)) s := by
  simp only [metricDerivative, derivHBarX,
    ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hs)),
    Real.coe_toNNReal s hs.le, tailIntegrand, hBarX, ContinuousMap.curry_apply]
  field_simp

private theorem hasDerivAt_gX (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gX hH.1 u t.toNNReal) (metricDerivative hH u s) s := by
  rw [metricDerivative_eq hH u hs]
  have hd := hasDerivAt_g (H.curry (min u u₀))
    (hH.1.isSlice _ (min_le_right u u₀)) s.toNNReal (Real.toNNReal_pos.mpr hs)
  rw [Real.coe_toNNReal s hs.le] at hd
  convert hd using 1
  · rfl
  · dsimp only [tailIntegrand, gX]
    ring

private theorem derivGBarX_integral (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0)
    {r : ℝ} (hr : 0 < r) :
    derivGBarX hH.1 u r.toNNReal =
      (∫ s in (0 : ℝ)..r, s * metricDerivative hH u s) / r ^ 2 := by
  let f := gMap (H.curry (min u u₀)) (hH.1.isSlice _ (min_le_right u u₀))
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
  change (gX hH.1 u r.toNNReal - gBarX hH.1 u r.toNNReal) / r =
    r * (gX hH.1 u r.toNNReal - gBarX hH.1 u r.toNNReal) / r ^ 2
  field_simp

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |a - c| * |d| := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

private theorem tail_bound (hH : MemXPrimeBall u₀ x H) (u : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    |tailIntegrand (H.curry (min u u₀)) s| ≤ x ^ 2 / (4 * (base u₀ u + s)) := by
  have hx := XWC.x_nonneg hH
  have bp := base_pos u₀ u
  have b1 := base_one u₀ u
  have hb := residual_bound hH u s.toNNReal
  rw [Real.coe_toNNReal s hs.le] at hb
  have hw : 0 < base u₀ u + s := by positivity
  have hw1 : 1 ≤ base u₀ u + s := by linarith only [b1, hs]
  have hpow : s ≤ (base u₀ u + s) ^ 3 := by
    calc
      _ ≤ base u₀ u + s := by linarith only [bp]
      _ ≤ _ := by simpa only [pow_one] using
        pow_le_pow_right₀ hw1 (by norm_num : 1 ≤ 3)
  change |(H (min u u₀, s.toNNReal) - hBarX u₀ H u s.toNNReal) ^ 2 / s| ≤ _
  rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hs]
  calc
    _ ≤ (x * s / (2 * base u₀ u ^ 2 * (base u₀ u + s) ^ 2)) ^ 2 / s := by
      apply div_le_div_of_nonneg_right _ hs.le
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = x ^ 2 * s / (4 * base u₀ u ^ 4 * (base u₀ u + s) ^ 4) := by field_simp; ring
    _ ≤ x ^ 2 * (base u₀ u + s) ^ 3 / (4 * base u₀ u ^ 4 * (base u₀ u + s) ^ 4) := by
      gcongr
    _ = x ^ 2 / (4 * base u₀ u ^ 4 * (base u₀ u + s)) := by field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) (by positivity)
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (one_le_pow₀ b1 : 1 ≤ base u₀ u ^ 4) (show (0 : ℝ) ≤ 4 by norm_num)

private theorem metricDerivative_difference (hH : MemXPrimeBall u₀ x H)
    (hK : MemXPrimeBall u₀ x K) (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y)
    (u : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    |metricDerivative hH u s - metricDerivative hK u s| ≤
      4 * π * x * (2 + π * x ^ 2) * y /
        (base u₀ u ^ 4 * (base u₀ u + s) ^ 3) := by
  have hx : 0 ≤ x := XWC.x_nonneg hH
  have bp := base_pos u₀ u
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp only [metricDerivative, mul_zero, zero_mul, sub_self, abs_zero]
    positivity
  rw [metricDerivative_eq hH u hs, metricDerivative_eq hK u hs,
    mul_assoc (4 * π), mul_assoc (4 * π), ← mul_sub, abs_mul,
    abs_of_pos (by positivity : 0 < 4 * π)]
  have hg : |gX hH.1 u s.toNNReal| ≤ 1 := by
    rw [gX, abs_of_pos (g_pos _ _ _)]
    exact g_le_one _ _ _
  have hdiff := gX_difference hH hK hy hY u s.toNNReal
  rw [Real.coe_toNNReal s hs.le] at hdiff
  calc
    _ ≤ (4 * π) * (|gX hH.1 u s.toNNReal| *
        |tailIntegrand (H.curry (min u u₀)) s -
          tailIntegrand (K.curry (min u u₀)) s| +
        |gX hH.1 u s.toNNReal - gX hK.1 u s.toNNReal| *
          |tailIntegrand (K.curry (min u u₀)) s|) := by
      exact mul_le_mul_of_nonneg_left (abs_mul_sub_mul_le _ _ _ _) (by positivity)
    _ ≤ (4 * π) * (1 * (2 * x * y / (base u₀ u ^ 4 * (base u₀ u + s) ^ 3)) +
        (4 * π * x * y / (base u₀ u ^ 4 * (base u₀ u + s) ^ 2)) *
          (x ^ 2 / (4 * (base u₀ u + s)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul hg (tail_difference_pointwise hH hK hy hY u hs)
          (abs_nonneg _) (by norm_num))
        (mul_le_mul hdiff (tail_bound hK u hs) (abs_nonneg _) (by positivity))
    _ = _ := by field_simp

private theorem derivGBarX_difference (hH : MemXPrimeBall u₀ x H)
    (hK : MemXPrimeBall u₀ x K) (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y)
    (u r : ℝ≥0) :
    |derivGBarX hH.1 u r - derivGBarX hK.1 u r| ≤
      2 * π * x * (2 + π * x ^ 2) * y /
        (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2) := by
  have hx : 0 ≤ x := XWC.x_nonneg hH
  have bp := base_pos u₀ u
  have hi := mean_deriv_difference_bound (base u₀ u) (base_pos _ _)
    (4 * π * x * (2 + π * x ^ 2) * y / base u₀ u ^ 4)
    (by positivity)
    (fun s => metricDerivative hH u s - metricDerivative hK u s)
    (fun s => derivGBarX hH.1 u s.toNNReal - derivGBarX hK.1 u s.toNNReal)
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
    (fun t ht => by
      have hd := metricDerivative_difference hH hK hy hY u t ht
      rw [← div_div] at hd
      exact hd) (r : ℝ) r.coe_nonneg
  rw [Real.toNNReal_coe] at hi
  convert hi using 1
  field_simp
  ring

private theorem linearSource_difference (hH : MemXPrimeBall u₀ x H)
    (hK : MemXPrimeBall u₀ x K) (hy : 0 ≤ y)
    (hY : YPrimeDistLe u₀ H K y)
    (u r : ℝ≥0) :
    |linearSource hH.1 u r - linearSource hK.1 u r| ≤
      π * x ^ 2 * (13 / 6 + π * x ^ 2) * y /
        (base u₀ u ^ 7 * (base u₀ u + (r : ℝ)) ^ 3) := by
  have hx : 0 ≤ x := XWC.x_nonneg hH
  have bp := base_pos u₀ u
  have hr := r.coe_nonneg
  have hw : 0 < base u₀ u + (r : ℝ) := by positivity
  have hcoeff : |linearCoeff hH.1 u r| ≤
      π * x ^ 2 / (6 * base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2) := by
    rw [abs_of_nonneg (XWC.linearCoeff_nonneg hH u r)]
    calc
      _ ≤ π / 6 * x ^ 2 * (r : ℝ) / (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 3) :=
        XWC.linearCoeff_le hH u r
      _ ≤ π / 6 * x ^ 2 * (base u₀ u + (r : ℝ)) /
          (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 3) := by gcongr; linarith only [bp]
      _ = _ := by field_simp
  have hcd : |linearCoeff hH.1 u r - linearCoeff hK.1 u r| ≤
      π * x * (2 + π * x ^ 2) * y /
        (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2) := by
    simp only [linearCoeff, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ (1 / 2) *
          (2 * π * x * (2 + π * x ^ 2) * y /
        (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (derivGBarX_difference hH hK hy hY u r) (by norm_num)
      _ = _ := by ring
  change |-(linearCoeff hH.1 u r) * hBarX u₀ H u r -
    -(linearCoeff hK.1 u r) * hBarX u₀ K u r| ≤ _
  have hc := abs_mul_sub_mul_le (-(linearCoeff hH.1 u r)) (hBarX u₀ H u r)
    (-(linearCoeff hK.1 u r)) (hBarX u₀ K u r)
  simp only [abs_neg, neg_sub_neg] at hc
  rw [abs_sub_comm (linearCoeff hK.1 u r) (linearCoeff hH.1 u r)] at hc
  calc
    _ ≤ |linearCoeff hH.1 u r| * |hBarX u₀ H u r - hBarX u₀ K u r| +
        |linearCoeff hH.1 u r - linearCoeff hK.1 u r| * |hBarX u₀ K u r| := hc
    _ ≤ (π * x ^ 2 / (6 * base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2)) *
          (y / (base u₀ u ^ 2 * (base u₀ u + (r : ℝ)))) +
        (π * x * (2 + π * x ^ 2) * y /
        (base u₀ u ^ 5 * (base u₀ u + (r : ℝ)) ^ 2)) *
          (x / (base u₀ u ^ 2 * (base u₀ u + (r : ℝ)))) := by
      exact add_le_add
        (mul_le_mul hcoeff (hBar_difference hy hY u r) (abs_nonneg _) (by positivity))
        (mul_le_mul hcd (XWC.abs_hBarX_le hK u r) (abs_nonneg _) (by positivity))
    _ = _ := by field_simp; ring


private lemma relax_weight {b w C : ℝ} (hb : 0 < b) (hw : b ≤ w) (hC : 0 ≤ C) :
    C / (b ^ 5 * w ^ 5) ≤ C / (b ^ 7 * w ^ 3) := by
  have wp : 0 < w := hb.trans_le hw
  apply div_le_div_of_nonneg_left hC (by positivity)
  calc
    _ = b ^ 5 * w ^ 3 * b ^ 2 := by ring
    _ ≤ b ^ 5 * w ^ 3 * w ^ 2 := by gcongr
    _ = _ := by ring

private theorem remainder_bound (hH : MemXPrimeBall u₀ x H)
    (hK : MemXPrimeBall u₀ x K) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hSK : MemXPrimeBall u₀ x (linearStepMap hK.1 data)) (hy0 : 0 ≤ y)
    (hy : YPrimeDistLe u₀ H K y) (u r : ℝ≥0) (hu : u ≤ u₀) :
    |(gBarX hH.1 u r - gBarX hK.1 u r) / 2 * derivLinearStep hK.1 data hdata u r +
      (linearCoeff hH.1 u r - linearCoeff hK.1 u r) * linearStep hK.1 data u r +
      linearSource hH.1 u r - linearSource hK.1 u r| ≤
      π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2) * y /
        (base u₀ u ^ 7 * (base u₀ u + (r : ℝ)) ^ 3) := by
  let b := base u₀ u
  let w := b + (r : ℝ)
  let S := linearStep hK.1 data u r
  let q := derivLinearStep hK.1 data hdata u r
  have bp : 0 < b := base_pos _ _
  have bw : b ≤ w := by dsimp [w]; linarith only [r.coe_nonneg]
  have wp : 0 < w := bp.trans_le bw
  have hx := XWC.x_nonneg hH
  have hbudget := hSK.2 u hu r
  have he : primeWeight u r = w := by
    dsimp [primeWeight, w, b, base]
    rw [min_eq_left hu]
    ring
  rw [he] at hbudget
  simp only [radialDerivative, linearStepMap_apply] at hbudget
  have hqeq := (hasDerivWithinAt_linearStep hK.1 data hdata u r).derivWithin
    (uniqueDiffOn_Ici 0 r r.coe_nonneg)
  rw [hqeq] at hbudget
  change w ^ 3 * |S| + w ^ 4 * |q| ≤ x at hbudget
  have hSv : |S| ≤ x / w ^ 3 := (le_div_iff₀ (pow_pos wp 3)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos wp 4).le (abs_nonneg q)])
  have hqv : |q| ≤ x / w ^ 4 := (le_div_iff₀ (pow_pos wp 4)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos wp 3).le (abs_nonneg S)])
  have hg := gBarX_difference hH hK hy0 hy u r
  have ha := derivGBarX_difference hH hK hy0 hy u r
  have hf := linearSource_difference hH hK hy0 hy u r
  have hgterm : |(gBarX hH.1 u r - gBarX hK.1 u r) / 2 * q| ≤
      2 * π * x ^ 2 * y / (b ^ 7 * w ^ 3) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (4 * π * x * y / (b ^ 5 * w) / 2) * (x / w ^ 4) :=
        mul_le_mul (div_le_div_of_nonneg_right hg (by norm_num)) hqv
          (abs_nonneg q) (by positivity)
      _ = 2 * π * x ^ 2 * y / (b ^ 5 * w ^ 5) := by field_simp; ring
      _ ≤ _ := relax_weight bp bw (by positivity)
  have hac : |linearCoeff hH.1 u r - linearCoeff hK.1 u r| ≤
      π * x * (2 + π * x ^ 2) * y / (b ^ 5 * w ^ 2) := by
    rw [linearCoeff, linearCoeff, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ 1 / 2 * (2 * π * x * (2 + π * x ^ 2) * y / (b ^ 5 * w ^ 2)) :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = _ := by ring
  have haterm : |(linearCoeff hH.1 u r - linearCoeff hK.1 u r) * S| ≤
      π * x ^ 2 * (2 + π * x ^ 2) * y / (b ^ 7 * w ^ 3) := by
    rw [abs_mul]
    calc
      _ ≤ (π * x * (2 + π * x ^ 2) * y / (b ^ 5 * w ^ 2)) * (x / w ^ 3) :=
        mul_le_mul hac hSv (abs_nonneg S) (by positivity)
      _ = π * x ^ 2 * (2 + π * x ^ 2) * y / (b ^ 5 * w ^ 5) := by field_simp
      _ ≤ _ := relax_weight bp bw (by positivity)
  calc
    _ = |(gBarX hH.1 u r - gBarX hK.1 u r) / 2 * q +
        (linearCoeff hH.1 u r - linearCoeff hK.1 u r) * S +
        (linearSource hH.1 u r - linearSource hK.1 u r)| := by
      congr 1
      dsimp [q, S]
      ring
    _ ≤ (|(gBarX hH.1 u r - gBarX hK.1 u r) / 2 * q| +
        |(linearCoeff hH.1 u r - linearCoeff hK.1 u r) * S|) +
        |linearSource hH.1 u r - linearSource hK.1 u r| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * π * x ^ 2 * y / (b ^ 7 * w ^ 3) +
        π * x ^ 2 * (2 + π * x ^ 2) * y / (b ^ 7 * w ^ 3) +
        π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / (b ^ 7 * w ^ 3) :=
      add_le_add (add_le_add hgterm haterm) hf
    _ = _ := by change _ = _ / (b ^ 7 * w ^ 3); ring

private lemma weight_integrable {a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) :
    IntervalIntegrable (fun s : ℝ => 1 / (1 + s / 2) ^ 7) volume a v := by
  apply ContinuousOn.intervalIntegrable_of_Icc hav
  exact continuousOn_const.div
    ((continuousOn_const.add (continuousOn_id.div_const 2)).pow 7)
    (fun s hs => by have hsn : 0 ≤ s := ha.trans hs.1; positivity)

private lemma weight_integral_le {a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) :
    (∫ s in a..v, 1 / (1 + s / 2) ^ 7) ≤ 1 / 3 := by
  have hd (s : ℝ) (hs : s ∈ Icc a v) :
      HasDerivAt (fun t : ℝ => -1 / (3 * (1 + t / 2) ^ 6))
        (1 / (1 + s / 2) ^ 7) s := by
    have hsn : 0 ≤ s := ha.trans hs.1
    convert (hasDerivAt_const s (-1 : ℝ)).div
      (((((hasDerivAt_id s).div_const 2).const_add 1).pow 6).const_mul 3)
      (by dsimp; positivity) using 1
    · rfl
    · dsimp
      field_simp
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := v) (fun s hs => hd s (by simpa only [uIcc_of_le hav] using hs))
    (weight_integrable ha hav)
  rw [hi]
  have hv : 0 ≤ v := ha.trans hav
  have hn : 0 ≤ 1 / (3 * (1 + v / 2) ^ 6) := by positivity
  have hp : 1 ≤ (1 + a / 2) ^ 6 := one_le_pow₀ (by linarith only [ha])
  have hb : 1 / (3 * (1 + a / 2) ^ 6) ≤ (1 / 3 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hp]
  simp only [neg_div] at *
  linarith only [hn, hb]

private theorem characteristic_weight (hH : MemXPrimeBall u₀ x H)
    {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH.1 v r χ) {s : ℝ} (hs : s ∈ Icc 0 (v : ℝ)) :
    exp (-(π / 6) * x ^ 2) * primeWeight (v : ℝ).toNNReal r ≤
      primeWeight s.toNNReal (χ s).toNNReal := by
  let k := exp (-(π / 6) * x ^ 2)
  have hk : 0 < k := exp_pos _
  have hneg : -(π / 6) * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg pi_pos.le (by norm_num))) (sq_nonneg x)
  have hk1 : k ≤ 1 := exp_le_one_iff.mpr hneg
  have hc : ContinuousOn χ (Icc 0 (v : ℝ)) := HasDerivWithinAt.continuousOn hχ.2
  have hp : ContinuousOn (fun t : ℝ => (t.toNNReal, (χ t).toNNReal))
      (Icc 0 (v : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn hc)
  have hg : ContinuousOn (fun t : ℝ => gBarX hH.1 t.toNNReal (χ t).toNNReal)
      (Icc 0 (v : ℝ)) :=
    (continuous_gBarX hH.1).comp_continuousOn
      (f := fun t : ℝ => (t.toNNReal, (χ t).toNNReal)) hp
  have hi : k * ((v : ℝ) - s) ≤
      ∫ t in s..(v : ℝ), gBarX hH.1 t.toNNReal (χ t).toNNReal := by
    calc
      _ = ∫ _t in s..(v : ℝ), k := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hs.2 intervalIntegrable_const
        ((hg.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2)
        (fun t _ => (XWC.exp_lower (T := u₀) (x := x) t.toNNReal).trans
          (XWC.gBarX_lower hH t.toNNReal (χ t).toNNReal))
  have he := hχ.eq_add_integral hs
  have hr : 0 ≤ χ s := r.coe_nonneg.trans (hχ.mem_Icc hs).1
  have hchi : (r : ℝ) + k / 2 * ((v : ℝ) - s) ≤ χ s := by
    linarith only [hi, he]
  have hkr : k * (r : ℝ) ≤ (r : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 r.coe_nonneg
  have hks : k * (1 + s / 2) ≤ 1 + s / 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1
      (show 0 ≤ 1 + s / 2 by linarith only [hs.1])
  dsimp only [primeWeight]
  rw [Real.coe_toNNReal _ v.2.1, Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hr]
  change k * (1 + (r : ℝ) + (v : ℝ) / 2) ≤ 1 + χ s + s / 2
  calc
    _ = k * (1 + s / 2) + k * (r : ℝ) + k / 2 * ((v : ℝ) - s) := by ring
    _ ≤ (1 + s / 2) + (r : ℝ) + k / 2 * ((v : ℝ) - s) :=
      add_le_add (add_le_add hks hkr) le_rfl
    _ ≤ _ := by linarith only [hchi]

private theorem integrating_factor_le (hH : MemXPrimeBall u₀ x H)
    {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH.1 v r χ) {s : ℝ} (hs : s ∈ Icc 0 (v : ℝ)) :
    exp (∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal) ≤
      exp (π * x ^ 2 / 18) := by
  have hc : ContinuousOn χ (Icc 0 (v : ℝ)) := HasDerivWithinAt.continuousOn hχ.2
  have hp : ContinuousOn (fun t : ℝ => (t.toNNReal, (χ t).toNNReal))
      (Icc 0 (v : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn hc)
  have ha : ContinuousOn (fun t : ℝ => linearCoeff hH.1 t.toNNReal (χ t).toNNReal)
      (Icc 0 (v : ℝ)) :=
    (continuous_const.mul (continuous_derivGBarX hH.1)).comp_continuousOn hp
  have hi : (∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal) ≤
      ∫ t in s..(v : ℝ), (π / 6 * x ^ 2) * (1 / (1 + t / 2) ^ 7) := by
    apply intervalIntegral.integral_mono_on hs.2
      ((ha.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2)
      ((weight_integrable hs.1 hs.2).const_mul _)
    intro t ht
    have htT : t.toNNReal ≤ u₀ :=
      Real.toNNReal_le_iff_le_coe.mpr (ht.2.trans v.2.2)
    have htn : 0 ≤ t := hs.1.trans ht.1
    have hb := XWC.linearCoeff_le_uniform hH t.toNNReal (χ t).toNNReal
    dsimp only at hb
    rw [min_eq_left htT, Real.coe_toNNReal _ htn] at hb
    simpa only [div_eq_mul_inv, one_div, one_mul] using hb
  rw [intervalIntegral.integral_const_mul] at hi
  apply exp_le_exp.mpr
  calc
    _ ≤ (π / 6 * x ^ 2) * ∫ t in s..(v : ℝ), 1 / (1 + t / 2) ^ 7 := hi
    _ ≤ (π / 6 * x ^ 2) * (1 / 3) :=
      mul_le_mul_of_nonneg_left (weight_integral_le hs.1 hs.2) (by positivity)
    _ = _ := by ring

/-- The weighted (9.27)--(9.38): the linear step contracts the Y′ distance by s(x). -/
theorem linearStep_yPrime_lipschitz {T : ℝ≥0} {x y : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXPrimeBall T x H)
    (hK : MemXPrimeBall T x K) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun z : ℝ => data z.toNNReal) (Ici 0))
    (hSK : MemXPrimeBall T x (linearStepMap hK.1 data))
    (hy : YPrimeDistLe T H K y) :
    YPrimeDistLe T (linearStepMap hH.1 data) (linearStepMap hK.1 data)
      (contractionFactor x * y) := by
  have hy0 : 0 ≤ y :=
    (mul_nonneg (by norm_num [primeWeight]) (abs_nonneg _)).trans (hy 0 bot_le 0)
  intro u hu r
  let v : Icc (0 : ℝ) T := ⟨u, u.coe_nonneg, hu⟩
  let χ := characteristic hH.1 v r
  have hχ : IsCharacteristic hH.1 v r χ := isCharacteristic_characteristic hH.1 v r
  let k := exp (-(π / 6) * x ^ 2)
  let E := exp (π * x ^ 2 / 18)
  let C := π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2) * y
  let w := primeWeight u r
  have kp : 0 < k := exp_pos _
  have Ep : 0 < E := exp_pos _
  have Cn : 0 ≤ C := by dsimp [C]; positivity
  have wp : 0 < w := by dsimp [w, primeWeight]; positivity
  let R := fun s : ℝ =>
    (gBarX hH.1 s.toNNReal (χ s).toNNReal -
        gBarX hK.1 s.toNNReal (χ s).toNNReal) / 2 *
          derivLinearStep hK.1 data hdata s.toNNReal (χ s).toNNReal +
      (linearCoeff hH.1 s.toNNReal (χ s).toNNReal -
        linearCoeff hK.1 s.toNNReal (χ s).toNNReal) *
          linearStep hK.1 data s.toNNReal (χ s).toNNReal +
      linearSource hH.1 s.toNNReal (χ s).toNNReal -
        linearSource hK.1 s.toNNReal (χ s).toNNReal
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      ‖exp (∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal) * R s‖ ≤
        (E * C / (k * w) ^ 3) * (1 / (1 + s / 2) ^ 7) := by
    have sn : 0 ≤ s := hs.1
    have bs : 0 < 1 + s / 2 := by linarith only [sn]
    have hsT : s.toNNReal ≤ T :=
      Real.toNNReal_le_iff_le_coe.mpr (hs.2.trans v.2.2)
    have hb : base T s.toNNReal = 1 + s / 2 := by
      dsimp only [base]
      rw [min_eq_left hsT, Real.coe_toNNReal _ hs.1]
    have hweight : k * w ≤ primeWeight s.toNNReal (χ s).toNNReal := by
      simpa only [v, Real.toNNReal_coe] using characteristic_weight hH hχ hs
    have hwp : 0 < primeWeight s.toNNReal (χ s).toNNReal :=
      (mul_pos kp wp).trans_le hweight
    have heq : base T s.toNNReal + ((χ s).toNNReal : ℝ) =
        primeWeight s.toNNReal (χ s).toNNReal := by
      dsimp only [base, primeWeight]
      rw [min_eq_left hsT]
      ring
    have hR := remainder_bound hH hK data hdata hSK hy0 hy
      s.toNNReal (χ s).toNNReal hsT
    change |R s| ≤ C / (base T s.toNNReal ^ 7 *
      (base T s.toNNReal + ((χ s).toNNReal : ℝ)) ^ 3) at hR
    rw [heq, hb] at hR
    have hRn : |R s| ≤ (C / (k * w) ^ 3) * (1 / (1 + s / 2) ^ 7) := by
      calc
        _ ≤ C / ((1 + s / 2) ^ 7 * primeWeight s.toNNReal (χ s).toNNReal ^ 3) := hR
        _ ≤ C / ((1 + s / 2) ^ 7 * (k * w) ^ 3) := by
          apply div_le_div_of_nonneg_left Cn (by positivity)
          gcongr
        _ = _ := by field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    calc
      _ ≤ E * ((C / (k * w) ^ 3) * (1 / (1 + s / 2) ^ 7)) :=
        mul_le_mul (integrating_factor_le hH hχ hs) hRn (abs_nonneg _) Ep.le
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) v.2.1
    (Filter.Eventually.of_forall (fun s (hs : s ∈ Ioc 0 (v : ℝ)) =>
      hpoint s ⟨hs.1.le, hs.2⟩))
    ((weight_integrable (a := 0) (by norm_num) v.2.1).const_mul (E * C / (k * w) ^ 3))
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hi
  have heq := linearStep_difference_integral hH.1 hK.1 data hdata v r
  change linearStep hH.1 data (v : ℝ).toNNReal r -
    linearStep hK.1 data (v : ℝ).toNNReal r =
      ∫ s in (0 : ℝ)..(v : ℝ),
        exp (∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal) * R s at heq
  rw [← heq] at hi
  have hbound : |linearStep hH.1 data u r - linearStep hK.1 data u r| ≤
      E * C / (3 * (k * w) ^ 3) := by
    calc
      _ ≤ (E * C / (k * w) ^ 3) * ∫ s in (0 : ℝ)..(v : ℝ), 1 / (1 + s / 2) ^ 7 := by
        simpa only [v, Real.toNNReal_coe] using hi
      _ ≤ (E * C / (k * w) ^ 3) * (1 / 3) :=
        mul_le_mul_of_nonneg_left (weight_integral_le (by norm_num) v.2.1) (by positivity)
      _ = _ := by ring
  have hexp : E / k ^ 3 = exp (5 * π / 9 * x ^ 2) := by
    dsimp only [E, k]
    rw [← exp_nat_mul, ← exp_sub]
    congr 1
    ring
  simp only [linearStepMap_apply]
  change w ^ 3 * |linearStep hH.1 data u r - linearStep hK.1 data u r| ≤ _
  calc
    _ ≤ w ^ 3 * (E * C / (3 * (k * w) ^ 3)) :=
      mul_le_mul_of_nonneg_left hbound (pow_pos wp 3).le
    _ = (E / k ^ 3) * (C / 3) := by field_simp
    _ = contractionFactor x * y := by rw [hexp]; dsimp [C, contractionFactor]; ring

end XWL
end Christodoulou.Bondi
