module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearSource
public import Christodoulou.Frozen.Bondi.DerivGBarXNonneg
import Christodoulou.Frozen.Bondi.GLeOne
import Christodoulou.Frozen.Bondi.HasDerivAtG
import Christodoulou.Frozen.Bondi.IntegrableOnTail
import Christodoulou.Bondi.GBarBasic
import Christodoulou.Bondi.GBasic
import Christodoulou.Radial.MeanBasic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Weighted coefficient estimates

The single-slice comparison proofs of (9.4)--(9.9), lifted through the frozen
`MemXPrimeBall` gate. All radial estimates include the centre. The time parameter
in the estimates is clamped to the strip, as in the sealed coefficient definitions.
-/

public section

open Set MeasureTheory Real Filter Topology Asymptotics
open scoped NNReal

namespace Christodoulou.Bondi.XWC
open Christodoulou.Radial

private lemma compare_of_deriv {f B f' B' : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hf' : ∀ s > 0, HasDerivAt f (f' s) s)
    (hB' : ∀ s > 0, HasDerivAt B (B' s) s)
    (h0 : f 0 ≤ B 0) (hb : ∀ s > 0, f' s ≤ B' s) {r : ℝ} (hr : 0 ≤ r) :
    f r ≤ B r := by
  have hm : MonotoneOn (fun s => B s - f s) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (hB.sub hf)
      (f' := fun s => B' s - f' s)
    · intro s hs
      rw [interior_Ici] at hs
      exact ((hB' s hs).sub (hf' s hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      exact sub_nonneg.mpr (hb s hs)
  have := hm (by simp) hr hr
  linarith

private lemma hasDerivAt_mul_sub_mean (f : C(ℝ≥0, ℝ)) {s d : ℝ} (hs : 0 < s)
    (hd : HasDerivAt (fun t : ℝ => f (Real.toNNReal t)) d s) :
    HasDerivAt (fun t : ℝ => t * (f (Real.toNNReal t) - mean f (Real.toNNReal t)))
      (s * d) s := by
  have hm := hasDerivAt_mean f (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
  rw [Real.coe_toNNReal s hs.le] at hm
  convert (hasDerivAt_id s).mul (hd.sub hm) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma continuous_mul_sub_mean (f : C(ℝ≥0, ℝ)) :
    Continuous (fun t : ℝ => t * (f (Real.toNNReal t) - mean f (Real.toNNReal t))) :=
  continuous_id.mul ((f.continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean f).comp continuous_real_toNNReal))

private lemma abs_compare_of_deriv {f B f' B' : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hf' : ∀ s > 0, HasDerivAt f (f' s) s)
    (hB' : ∀ s > 0, HasDerivAt B (B' s) s)
    (h0 : |f 0| ≤ B 0) (hb : ∀ s > 0, |f' s| ≤ B' s) {r : ℝ} (hr : 0 ≤ r) :
    |f r| ≤ B r := by
  apply abs_le.mpr
  constructor
  · have hn := compare_of_deriv hf.neg hB (fun s hs => (hf' s hs).neg) hB'
      ((neg_le_abs (f 0)).trans h0)
      (fun s hs => (neg_le_abs (f' s)).trans (hb s hs)) hr
    change -f r ≤ B r at hn
    linarith
  · exact compare_of_deriv hf hB hf' hB' ((le_abs_self (f 0)).trans h0)
      (fun s hs => (le_abs_self (f' s)).trans (hb s hs)) hr


/-- Source premise: a C¹ slice with the X′ combined bound. -/
private def WeightedSlice (f : C(ℝ≥0, ℝ)) (b x : ℝ) : Prop :=
  ContDiffOn ℝ 1 (lift f) (Ici 0) ∧
  ∀ r : ℝ≥0, (b + (r : ℝ)) ^ 3 * |f r| +
    (b + (r : ℝ)) ^ 4 * |derivWithin (lift f) (Ici 0) r| ≤ x

variable {f : C(ℝ≥0, ℝ)} {b x : ℝ}

private lemma slice_x_nonneg (hb : 1 ≤ b) (hf : WeightedSlice f b x) : 0 ≤ x := by
  have bp : 0 < b := by linarith
  exact le_trans (by positivity) (hf.2 0)

private lemma value_le (hb : 1 ≤ b) (hf : WeightedSlice f b x) (r : ℝ≥0) :
    |f r| ≤ x / (b * (b + (r : ℝ)) ^ 2) := by
  have bp : 0 < b := by linarith
  have hs := r.coe_nonneg
  have hw : (b + (r : ℝ)) ^ 3 * |f r| ≤ x :=
    (le_add_of_nonneg_right (by positivity)).trans (hf.2 r)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    |f r| * (b * (b + (r : ℝ)) ^ 2) ≤ |f r| * (b + (r : ℝ)) ^ 3 := by
      gcongr
      nlinarith [sq_nonneg (b + (r : ℝ))]
    _ ≤ x := by simpa only [mul_comm] using hw

private lemma hasDerivAt_bound_one (b x s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => x * t / (b ^ 2 * (b + t)))
      (x / (b * (b + s) ^ 2)) s := by
  convert ((hasDerivAt_id s).const_mul x).div
    (((hasDerivAt_id s).const_add b).const_mul (b ^ 2))
    (by dsimp; positivity) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma slice_mean_le (hb : 1 ≤ b) (hf : WeightedSlice f b x) (r : ℝ≥0) :
    |mean f r| ≤ x / (b ^ 2 * (b + (r : ℝ))) := by
  have bp : 0 < b := by linarith
  rcases eq_or_ne r 0 with rfl | hr
  · have hv := value_le hb hf 0
    simpa only [mean_zero, NNReal.coe_zero, add_zero, mul_comm b (b ^ 2)] using hv
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let F := fun s : ℝ => ∫ t in (0 : ℝ)..s, lift f t
  have hc : Continuous F :=
    intervalIntegral.continuous_primitive (continuous_lift f).intervalIntegrable 0
  have hB : ContinuousOn (fun s : ℝ => x * s / (b ^ 2 * (b + s))) (Ici 0) := by
    exact (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hval (s : ℝ) (hs : 0 < s) : |lift f s| ≤ x / (b * (b + s) ^ 2) := by
    simpa only [lift, Real.coe_toNNReal s hs.le] using value_le hb hf (Real.toNNReal s)
  have hle := abs_compare_of_deriv hc.continuousOn hB
    (fun s _ => hasDerivAt_integral_lift f s)
    (fun s hs => hasDerivAt_bound_one b x s bp hs.le) (by simp [F]) hval r.coe_nonneg
  change |∫ t in (0 : ℝ)..(r : ℝ), lift f t| ≤ x * (r : ℝ) / (b ^ 2 * (b + (r : ℝ))) at hle
  rw [← coe_mul_mean, abs_mul, abs_of_pos rp] at hle
  apply (mul_le_mul_iff_right₀ rp).mp
  convert hle using 1
  ring

private lemma hasDerivAt_bound_two (b x s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => x * t ^ 2 / (2 * b ^ 2 * (b + t) ^ 2))
      (x * s / (b * (b + s) ^ 3)) s := by
  convert (((hasDerivAt_id s).pow 2).const_mul x).div
    ((((hasDerivAt_id s).const_add b).pow 2).const_mul (2 * b ^ 2))
    (by dsimp; positivity) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma slice_sub_mean_le (hb : 1 ≤ b) (hf : WeightedSlice f b x) (r : ℝ≥0) :
    |f r - mean f r| ≤ x * (r : ℝ) / (2 * b ^ 2 * (b + (r : ℝ)) ^ 2) := by
  have bp : 0 < b := by linarith
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [mean_zero, sub_self, abs_zero, NNReal.coe_zero, mul_zero, zero_div, le_refl]
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let D := fun s : ℝ => derivWithin (lift f) (Ici 0) s
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt (lift f) (D s) s := by
    exact (hf.1.differentiableOn one_ne_zero s hs.le).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hs)
  have hder (s : ℝ) (hs : 0 < s) : |s * D s| ≤ x * s / (b * (b + s) ^ 3) := by
    have hw := hf.2 (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.le] at hw
    have hw' : (b + s) ^ 4 * |D s| ≤ x :=
      (le_add_of_nonneg_left (by positivity)).trans hw
    have hw'' : (b * (b + s) ^ 3) * |D s| ≤ x := by
      calc
        _ ≤ (b + s) ^ 4 * |D s| := by
          gcongr
          nlinarith [pow_nonneg (by positivity : 0 ≤ b + s) 3]
        _ ≤ x := hw'
    rw [abs_mul, abs_of_pos hs, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hw'' hs.le]
  have hB : ContinuousOn (fun s : ℝ => x * s ^ 2 / (2 * b ^ 2 * (b + s) ^ 2)) (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow _))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hc := abs_compare_of_deriv (continuous_mul_sub_mean f).continuousOn hB
    (fun s hs => hasDerivAt_mul_sub_mean f hs (hd s hs))
    (fun s hs => hasDerivAt_bound_two b x s bp hs.le) (by simp) hder r.coe_nonneg
  simp only [Real.toNNReal_coe, abs_mul, abs_of_nonneg r.coe_nonneg] at hc
  have heq : x * (r : ℝ) ^ 2 / (2 * b ^ 2 * (b + (r : ℝ)) ^ 2) =
      (r : ℝ) * (x * (r : ℝ) / (2 * b ^ 2 * (b + (r : ℝ)) ^ 2)) := by ring
  rw [heq] at hc
  exact (mul_le_mul_iff_right₀ rp).mp hc



private lemma isSlice (hb : 1 ≤ b) (hf : WeightedSlice f b x) : IsSlice f := by
  have bp : 0 < b := by linarith
  have hx := slice_x_nonneg hb hf
  refine ⟨hf.1, IsBigO.of_bound x ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hw := hf.2 (Real.toNNReal s)
  rw [Real.coe_toNNReal s hs.le] at hw
  have hw' : (b + s) ^ 3 * |f (Real.toNNReal s)| ≤ x :=
    (le_add_of_nonneg_right (by positivity)).trans hw
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zpow_pos hs _)]
  calc
    |f (Real.toNNReal s)| ≤ x / (b + s) ^ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using hw'
    _ ≤ x * s ^ (-3 : ℤ) := by
      rw [div_eq_mul_inv, zpow_neg, zpow_ofNat]
      gcongr
      linarith

private lemma square_sub_mean_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (s : ℝ) (hs : 0 ≤ s) :
    (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 ≤
      (x * s / (2 * b ^ 2 * (b + s) ^ 2)) ^ 2 := by
  have ha := slice_sub_mean_le hb hf (Real.toNNReal s)
  rw [Real.coe_toNNReal s hs] at ha
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

private lemma metric_derivative_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (s : ℝ) (hs : 0 ≤ s) :
    4 * π * g f hh (Real.toNNReal s) *
      (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 ≤
      π * x ^ 2 * s ^ 2 / (b ^ 4 * (b + s) ^ 4) := by
  have bp : 0 < b := by linarith
  have ha2 := square_sub_mean_le hb hf s hs
  calc
    _ ≤ 4 * π * (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (g_le_one f hh (Real.toNNReal s))
        (show 0 ≤ 4 * π * (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 by positivity)
      nlinarith only [this]
    _ ≤ 4 * π * (x * s / (2 * b ^ 2 * (b + s) ^ 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left ha2 (by positivity)
    _ = _ := by field_simp; ring

private lemma hasDerivAt_g_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (r : ℝ≥0) (hr : 0 < r) :
    deriv (fun s : ℝ => g f hh (Real.toNNReal s)) r ≤
      π * x ^ 2 * (r : ℝ) / (b ^ 4 * (b + (r : ℝ)) ^ 4) := by
  have bp : 0 < b := by linarith
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
  rw [(hasDerivAt_g f hh r hr).deriv]
  have h := metric_derivative_le hb hf hh r r.coe_nonneg
  simp only [Real.toNNReal_coe] at h
  apply (div_le_iff₀ rp).mpr
  convert h using 1
  ring

private lemma hasDerivAt_bound_three (b x s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => π * x ^ 2 * t ^ 3 / (3 * b ^ 5 * (b + t) ^ 3))
      (π * x ^ 2 * s ^ 2 / (b ^ 4 * (b + s) ^ 4)) s := by
  convert (((hasDerivAt_id s).pow 3).const_mul (π * x ^ 2)).div
    ((((hasDerivAt_id s).const_add b).pow 3).const_mul (3 * b ^ 5))
    (by dsimp; positivity) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma mul_metric_gap_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (r : ℝ≥0) :
    (r : ℝ) * (g f hh r - gBar f hh r) ≤
      π * x ^ 2 * (r : ℝ) ^ 3 / (3 * b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  have bp : 0 < b := by linarith
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => t * (g f hh (Real.toNNReal t) - gBar f hh (Real.toNNReal t)))
        (4 * π * g f hh (Real.toNNReal s) *
          (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2) s := by
    have hg := hasDerivAt_g f hh (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
    rw [Real.coe_toNNReal s hs.le] at hg
    convert hasDerivAt_mul_sub_mean (gMap f hh) hs hg using 1
    · rfl
    · field_simp
  have hB : ContinuousOn
      (fun s : ℝ => π * x ^ 2 * s ^ 3 / (3 * b ^ 5 * (b + s) ^ 3)) (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow _))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hc := compare_of_deriv (continuous_mul_sub_mean (gMap f hh)).continuousOn hB hd
    (fun s hs => hasDerivAt_bound_three b x s bp hs.le) (by simp)
    (fun s hs => metric_derivative_le hb hf hh s hs.le) r.coe_nonneg
  simpa only [Real.toNNReal_coe, gMap_apply, gBar] using hc

private lemma slice_metric_gap_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (r : ℝ≥0) :
    g f hh r - gBar f hh r ≤
      π / 3 * x ^ 2 * (r : ℝ) ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  have bp : 0 < b := by linarith
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [gBar_zero, sub_self, NNReal.coe_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_div, le_refl]
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have h := mul_metric_gap_le hb hf hh r
  apply (mul_le_mul_iff_right₀ rp).mp
  convert h using 1
  field_simp

private lemma slice_metric_gap_div_le (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (r : ℝ≥0) :
    (g f hh r - gBar f hh r) / (r : ℝ) ≤
      π / 3 * x ^ 2 * (r : ℝ) / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  have bp : 0 < b := by linarith
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [NNReal.coe_zero, div_zero, mul_zero, zero_div, le_refl]
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  apply (div_le_iff₀ rp).mpr
  convert slice_metric_gap_le hb hf hh r using 1
  ring

private lemma uniform_majorant_le (hb : 1 ≤ b) (r : ℝ≥0) :
    π / 3 * x ^ 2 * (r : ℝ) / (b ^ 5 * (b + (r : ℝ)) ^ 3) ≤
      π / 3 * x ^ 2 / b ^ 7 := by
  have bp : 0 < b := by linarith
  have hs := r.coe_nonneg
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp : (r : ℝ) * b ^ 2 ≤ (b + (r : ℝ)) ^ 3 := by
    nlinarith [sq_nonneg (r : ℝ), pow_nonneg hs 3]
  calc
    _ = (π / 3 * x ^ 2 * b ^ 5) * ((r : ℝ) * b ^ 2) := by ring
    _ ≤ (π / 3 * x ^ 2 * b ^ 5) * (b + (r : ℝ)) ^ 3 := by gcongr
    _ = _ := by ring

/-- Primitive of the tail majorant, tending to zero at infinity. -/
private noncomputable def tailPrimitive (b x s : ℝ) : ℝ :=
  x ^ 2 / (4 * b ^ 4) * (-(b + s)⁻¹ ^ 2 / 2 + b * (b + s)⁻¹ ^ 3 / 3)

private lemma hasDerivAt_tailPrimitive (b x s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) :
    HasDerivAt (tailPrimitive b x)
      (x ^ 2 * s / (4 * b ^ 4 * (b + s) ^ 4)) s := by
  have hn : b + s ≠ 0 := by positivity
  have hd := ((hasDerivAt_id s).const_add b).inv hn
  convert ((((hd.pow 2).neg.div_const 2).add
    (((hd.pow 3).const_mul b).div_const 3)).const_mul (x ^ 2 / (4 * b ^ 4))) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma tendsto_tailPrimitive (b x : ℝ) : Tendsto (tailPrimitive b x) atTop (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ => (b + s)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop b tendsto_id)
  have h := (((ht.pow 2).neg.div_const 2).add
    (((ht.pow 3).const_mul b).div_const 3)).const_mul (x ^ 2 / (4 * b ^ 4))
  change Tendsto (fun s : ℝ => x ^ 2 / (4 * b ^ 4) *
    (-(b + s)⁻¹ ^ 2 / 2 + b * (b + s)⁻¹ ^ 3 / 3)) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0),
    neg_zero, zero_div, mul_zero, add_zero] using h

private lemma tail_majorant_integrable (hb : 1 ≤ b) :
    IntegrableOn (fun s : ℝ => x ^ 2 * s / (4 * b ^ 4 * (b + s) ^ 4)) (Ioi 0) := by
  have bp : 0 < b := by linarith
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun s hs => hasDerivAt_tailPrimitive b x s bp hs)
    (fun s hs => by have sp : 0 ≤ s := hs.le; positivity) (tendsto_tailPrimitive b x)

private lemma tail_majorant_integral (hb : 1 ≤ b) :
    (∫ s in Ioi (0 : ℝ), x ^ 2 * s / (4 * b ^ 4 * (b + s) ^ 4)) = x ^ 2 / (24 * b ^ 6) := by
  have bp : 0 < b := by linarith
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun s hs => hasDerivAt_tailPrimitive b x s bp hs)
    (fun s hs => by have sp : 0 ≤ s := hs.le; positivity) (tendsto_tailPrimitive b x)]
  dsimp [tailPrimitive]
  field_simp
  ring

private lemma slice_tail_integral_le (hb : 1 ≤ b) (hf : WeightedSlice f b x) :
    (∫ s in Ioi (0 : ℝ), tailIntegrand f s) ≤ x ^ 2 / (24 * b ^ 6) := by
  have bp : 0 < b := by linarith
  have hh := isSlice hb hf
  rw [← tail_majorant_integral hb]
  apply setIntegral_mono_on (integrable_tailIntegrand f hh).integrableOn
    (tail_majorant_integrable hb) measurableSet_Ioi
  intro s hs
  have ha2 := square_sub_mean_le hb hf s hs.le
  change (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 / s ≤ _
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ (x * s / (2 * b ^ 2 * (b + s) ^ 2)) ^ 2 := ha2
    _ = _ := by field_simp; ring

private lemma slice_g_zero_lower (hb : 1 ≤ b) (hf : WeightedSlice f b x) (hh : IsSlice f) :
    Real.exp (-(π / 6) * x ^ 2 / b ^ 6) ≤ g f hh 0 := by
  have bp : 0 < b := by linarith
  change Real.exp _ ≤ Real.exp (-(4 * π) * ∫ s in Ioi (0 : ℝ), tailIntegrand f s)
  apply Real.exp_le_exp.mpr
  calc
    _ = -(4 * π) * (x ^ 2 / (24 * b ^ 6)) := by ring
    _ ≤ _ := mul_le_mul_of_nonpos_left (slice_tail_integral_le hb hf)
      (neg_nonpos.mpr (by positivity))


variable {T : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}

private lemma clamped_slice (hH : MemXPrimeBall T x H) (u : ℝ≥0) :
    WeightedSlice (H.curry (min u T)) (1 + ((min u T : ℝ≥0) : ℝ) / 2) x := by
  refine ⟨hH.1.1 _ (min_le_right _ _), ?_⟩
  intro r
  change (1 + ((min u T : ℝ≥0) : ℝ) / 2 + (r : ℝ)) ^ 3 * |H (min u T, r)| +
    (1 + ((min u T : ℝ≥0) : ℝ) / 2 + (r : ℝ)) ^ 4 *
      |radialDerivative H (min u T) r| ≤ x
  convert hH.2 (min u T) (min_le_right _ _) r using 1
  dsimp only [primeWeight]
  ring

private lemma base_pos (u : ℝ≥0) : 0 < 1 + ((min u T : ℝ≥0) : ℝ) / 2 := by positivity

private lemma base_one (u : ℝ≥0) : 1 ≤ 1 + ((min u T : ℝ≥0) : ℝ) / 2 := by
  have := (min u T).coe_nonneg
  linarith

/-- The frozen X′ gate implies a nonnegative radius. -/
theorem x_nonneg (hH : MemXPrimeBall T x H) : 0 ≤ x :=
  slice_x_nonneg (base_one 0) (clamped_slice hH 0)

/-- (9.4), including the centre, with clamped time. -/
theorem abs_hBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |hBarX T H u r| ≤ x / (b ^ 2 * (b + (r : ℝ))) :=
  slice_mean_le (base_one u) (clamped_slice hH u) r

/-- (9.6), including the centre, with clamped time. -/
theorem abs_sub_hBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |H (min u T, r) - hBarX T H u r| ≤
      x * (r : ℝ) / (2 * b ^ 2 * (b + (r : ℝ)) ^ 2) :=
  slice_sub_mean_le (base_one u) (clamped_slice hH u) r

/-- The centre tail bound used in the metric lower estimate. -/
theorem tail_integral_le (hH : MemXPrimeBall T x H) (u : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    (∫ s in Ioi (0 : ℝ),
      (H (min u T, s.toNNReal) - hBarX T H u s.toNNReal) ^ 2 / s) ≤
      x ^ 2 / (24 * b ^ 6) :=
  slice_tail_integral_le (base_one u) (clamped_slice hH u)


theorem gX_zero_lower (hH : MemXPrimeBall T x H) (u : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    exp (-(π / 6) * x ^ 2 / b ^ 6) ≤ gX hH.1 u 0 :=
  slice_g_zero_lower (base_one u) (clamped_slice hH u) _

/-- The weighted lower bound dominates the time-independent lower bound. -/
theorem exp_lower (u : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    exp (-(π / 6) * x ^ 2) ≤ exp (-(π / 6) * x ^ 2 / b ^ 6) := by
  dsimp
  apply exp_le_exp.mpr
  have hb := base_one (T := T) u
  have hp : 1 ≤ (1 + ((min u T : ℝ≥0) : ℝ) / 2) ^ 6 := one_le_pow₀ hb
  have hn : 0 ≤ π / 6 * x ^ 2 := by positivity
  simpa only [neg_mul, neg_div] using neg_le_neg (div_le_self hn hp)


theorem gX_sub_gBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    gX hH.1 u r - gBarX hH.1 u r ≤
      π / 3 * x ^ 2 * (r : ℝ) ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) :=
  slice_metric_gap_le (base_one u) (clamped_slice hH u) _ r

/-- The first radial derivative of the metric mean, including its zero centre value. -/
theorem derivGBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    derivGBarX hH.1 u r ≤
      π / 3 * x ^ 2 * (r : ℝ) / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [derivGBarX, ite_true, NNReal.coe_zero, mul_zero, zero_div, le_refl]
  · rw [derivGBarX, ite_eq_right hr]
    exact slice_metric_gap_div_le (base_one u) (clamped_slice hH u) _ r

/-- The coefficient is nonnegative, including at the centre. -/
theorem linearCoeff_nonneg (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    0 ≤ linearCoeff hH.1 u r :=
  mul_nonneg (by norm_num) (Christodoulou.Bondi.derivGBarX_nonneg hH.1 u r)

/-- The weighted coefficient bound, including the centre. -/
theorem linearCoeff_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    linearCoeff hH.1 u r ≤
      π / 6 * x ^ 2 * (r : ℝ) / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  have hd := mul_le_mul_of_nonneg_left (derivGBarX_le hH u r)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  dsimp [linearCoeff]
  convert hd using 1
  ring

/-- The uniform coefficient majorant has the seventh power of the time weight. -/
theorem linearCoeff_le_uniform (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    linearCoeff hH.1 u r ≤ π / 6 * x ^ 2 / b ^ 7 := by
  have hd := mul_le_mul_of_nonneg_left
    ((derivGBarX_le hH u r).trans (uniform_majorant_le (base_one u) r))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  dsimp [linearCoeff]
  convert hd using 1
  ring

/-- The weighted derivative of the scalar mean, including the one-sided centre. -/
theorem abs_derivHBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |derivHBarX hH.1 u r| ≤ x / (2 * b ^ 2 * (b + (r : ℝ)) ^ 2) := by
  have bp := base_pos (T := T) u
  have hx := x_nonneg hH
  rcases eq_or_ne r 0 with rfl | hr
  · have hd := (clamped_slice hH u).2 0
    simp only [NNReal.coe_zero, add_zero] at hd
    have hd' : (1 + ((min u T : ℝ≥0) : ℝ) / 2) ^ 4 *
        |derivWithin (fun s : ℝ => H (min u T, s.toNNReal)) (Ici 0) 0| ≤ x := by
      have hn : 0 ≤ (1 + ((min u T : ℝ≥0) : ℝ) / 2) ^ 3 *
          |(H.curry (min u T)) 0| := by positivity
      exact (le_add_of_nonneg_left hn).trans hd
    dsimp only
    simp only [derivHBarX, ite_true]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [NNReal.coe_zero, add_zero]
    apply (le_div_iff₀ (by positivity)).mpr
    convert hd' using 1
    ring
  · have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    dsimp only
    rw [derivHBarX, ite_eq_right hr, abs_div, abs_of_pos rp]
    apply (div_le_iff₀ rp).mpr
    convert abs_sub_hBarX_le hH u r using 1
    ring

/-- (9.10): the source has the seventh power of the time weight. -/
theorem abs_linearSource_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |linearSource hH.1 u r| ≤ π / 6 * x ^ 3 / (b ^ 7 * (b + (r : ℝ)) ^ 3) := by
  let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
  let R : ℝ := b + (r : ℝ)
  have bp : 0 < b := base_pos u
  have Rp : 0 < R := by dsimp [R]; positivity
  have hx := x_nonneg hH
  change |linearSource hH.1 u r| ≤ π / 6 * x ^ 3 / (b ^ 7 * R ^ 3)
  rw [linearSource, abs_mul, abs_neg, abs_of_nonneg (linearCoeff_nonneg hH u r)]
  calc
    _ ≤ (π / 6 * x ^ 2 * (r : ℝ) / (b ^ 5 * R ^ 3)) *
        (x / (b ^ 2 * R)) := by
      gcongr
      · exact linearCoeff_le hH u r
      · exact abs_hBarX_le hH u r
    _ = (π / 6 * x ^ 3 / (b ^ 7 * R ^ 3)) * ((r : ℝ) / R) := by field_simp
    _ ≤ (π / 6 * x ^ 3 / (b ^ 7 * R ^ 3)) * 1 := by
      gcongr
      apply (div_le_one Rp).mpr
      dsimp [R]
      linarith
    _ = _ := mul_one _

/-- The second derivative estimate on p. 356, with its sealed centre value. -/
theorem abs_deriv2GBarX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |deriv2GBarX hH.1 u r| ≤ π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
  let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
  have bp : 0 < b := base_pos u
  have hx := x_nonneg hH
  have hg0 (s : ℝ≥0) : 0 ≤ gX hH.1 u s := (g_pos _ _ s).le
  have hg1 (s : ℝ≥0) : gX hH.1 u s ≤ 1 := g_le_one _ _ s
  have hBs (s : ℝ≥0) : 4 * π * gX hH.1 u s * derivHBarX hH.1 u s ^ 2 ≤
      π * x ^ 2 / (b ^ 4 * (b + (s : ℝ)) ^ 4) := by
    have hb := abs_derivHBarX_le hH u s
    have hb2 : derivHBarX hH.1 u s ^ 2 ≤
        (x / (2 * b ^ 2 * (b + (s : ℝ)) ^ 2)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc
      _ ≤ 4 * π * derivHBarX hH.1 u s ^ 2 := by
        have hh := mul_le_mul_of_nonneg_right (hg1 s)
          (show 0 ≤ 4 * π * derivHBarX hH.1 u s ^ 2 by positivity)
        nlinarith only [hh]
      _ ≤ 4 * π * (x / (2 * b ^ 2 * (b + (s : ℝ)) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = _ := by field_simp; ring
  change |deriv2GBarX hH.1 u r| ≤ π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3)
  rcases eq_or_ne r 0 with rfl | hr
  · have hb := hBs 0
    have hval : deriv2GBarX hH.1 u 0 =
        (4 * π * gX hH.1 u 0 * derivHBarX hH.1 u 0 ^ 2) / 3 := by
      simp only [deriv2GBarX, derivHBarX, ite_true]
      ring
    have := hg0 0
    rw [hval, abs_of_nonneg (by positivity)]
    simp only [NNReal.coe_zero, add_zero] at hb ⊢
    have he : π * x ^ 2 / (b ^ 4 * b ^ 4) = π * x ^ 2 / (b ^ 5 * b ^ 3) := by ring
    rw [he] at hb
    have hp : 0 ≤ π * x ^ 2 / (b ^ 5 * b ^ 3) := by positivity
    linarith only [hb, hp]
  · have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hA0 : 0 ≤ 2 * derivGBarX hH.1 u r / (r : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num)
        (Christodoulou.Bondi.derivGBarX_nonneg hH.1 u r)) r.coe_nonneg
    have hB0 : 0 ≤ 4 * π * gX hH.1 u r * derivHBarX hH.1 u r ^ 2 := by
      have := hg0 r
      positivity
    have hAle : 2 * derivGBarX hH.1 u r / (r : ℝ) ≤
        π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
      calc
        _ ≤ 2 * (π / 3 * x ^ 2 * (r : ℝ) /
            (b ^ 5 * (b + (r : ℝ)) ^ 3)) / (r : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (derivGBarX_le hH u r) (by norm_num)) r.coe_nonneg
        _ = (2 / 3) * (π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3)) := by field_simp
        _ ≤ _ := by
          have hp : 0 ≤ π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by positivity
          linarith only [hp]
    have hBle : 4 * π * gX hH.1 u r * derivHBarX hH.1 u r ^ 2 ≤
        π * x ^ 2 / (b ^ 5 * (b + (r : ℝ)) ^ 3) := by
      apply (hBs r).trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have hn : 0 ≤ (r : ℝ) := r.coe_nonneg
      nlinarith [mul_nonneg hn (show 0 ≤ b ^ 4 * (b + (r : ℝ)) ^ 3 by positivity)]
    rw [deriv2GBarX, ite_eq_right hr]
    simp only [neg_mul, neg_div]
    exact abs_le.mpr ⟨by linarith only [hB0, hAle], by linarith only [hA0, hBle]⟩

/-- (9.17), stated on the explicit formula of the sealed source derivative. -/
theorem abs_deriv_linearSource_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    |-(1 / 2 * deriv2GBarX hH.1 u r) * hBarX T H u r -
      linearCoeff hH.1 u r * derivHBarX hH.1 u r| ≤
      7 * π * x ^ 3 / (12 * b ^ 7 * (b + (r : ℝ)) ^ 4) := by
  let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
  let R : ℝ := b + (r : ℝ)
  have bp : 0 < b := base_pos u
  have Rp : 0 < R := by dsimp [R]; positivity
  have hx := x_nonneg hH
  have hc := abs_deriv2GBarX_le hH u r
  have hh := abs_hBarX_le hH u r
  have hb := abs_derivHBarX_le hH u r
  have ha := linearCoeff_le hH u r
  change _ ≤ 7 * π * x ^ 3 / (12 * b ^ 7 * R ^ 4)
  calc
    _ ≤ 1 / 2 * |deriv2GBarX hH.1 u r| * |hBarX T H u r| +
        linearCoeff hH.1 u r * |derivHBarX hH.1 u r| := by
      calc
        _ ≤ |-(1 / 2 * deriv2GBarX hH.1 u r) * hBarX T H u r| +
            |linearCoeff hH.1 u r * derivHBarX hH.1 u r| := abs_sub _ _
        _ = _ := by
          rw [abs_mul, abs_neg, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
            abs_of_nonneg (linearCoeff_nonneg hH u r)]
    _ ≤ 1 / 2 * (π * x ^ 2 / (b ^ 5 * R ^ 3)) * (x / (b ^ 2 * R)) +
        (π / 6 * x ^ 2 * (r : ℝ) / (b ^ 5 * R ^ 3)) *
          (x / (2 * b ^ 2 * R ^ 2)) := by gcongr
    _ = π * x ^ 3 / (2 * b ^ 7 * R ^ 4) +
        π * x ^ 3 * ((r : ℝ) / R) / (12 * b ^ 7 * R ^ 4) := by field_simp; ring
    _ ≤ π * x ^ 3 / (2 * b ^ 7 * R ^ 4) +
        π * x ^ 3 * 1 / (12 * b ^ 7 * R ^ 4) := by
      gcongr
      apply (div_le_one Rp).mpr
      dsimp [R]
      linarith
    _ = _ := by field_simp; ring

/-- The metric lower bound at every radius. -/
theorem gX_lower (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    exp (-(π / 6) * x ^ 2 / b ^ 6) ≤ gX hH.1 u r :=
  (gX_zero_lower hH u).trans (monotone_g _ _ (show 0 ≤ r from zero_le))

/-- The same metric lower bound holds for the radial mean, including the centre. -/
theorem gBarX_lower (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    exp (-(π / 6) * x ^ 2 / b ^ 6) ≤ gBarX hH.1 u r := by
  let k := exp (-(π / 6) * x ^ 2 / (1 + ((min u T : ℝ≥0) : ℝ) / 2) ^ 6)
  change k ≤ gBarX hH.1 u r
  rcases eq_or_ne r 0 with rfl | hr
  · change k ≤ gBar _ _ 0
    rw [gBar_zero]
    exact gX_zero_lower hH u
  · have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    rw [gBarX, gBar_eq_integral _ _ r (pos_iff_ne_zero.mpr hr)]
    have hc : Continuous (fun s : ℝ => gX hH.1 u (Real.toNNReal s)) :=
      (continuous_g _ _).comp continuous_real_toNNReal
    have hi : k * (r : ℝ) ≤ ∫ s in (0 : ℝ)..(r : ℝ),
        gX hH.1 u (Real.toNNReal s) := by
      calc
        _ = ∫ _s in (0 : ℝ)..(r : ℝ), k := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
        _ ≤ _ := intervalIntegral.integral_mono_on rp.le
          intervalIntegrable_const (hc.intervalIntegrable _ _) (fun s _ => gX_lower hH u _)
    change k ≤ (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), gX hH.1 u (Real.toNNReal s)
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ rp).mpr hi

private lemma slice_hasDerivWithinAt_g (hb : 1 ≤ b) (hf : WeightedSlice f b x)
    (hh : IsSlice f) (r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => g f hh (Real.toNNReal s))
      (4 * π * g f hh r * (f r - mean f r) ^ 2 / (r : ℝ)) (Ici 0) (r : ℝ) := by
  have bp : 0 < b := by linarith
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [NNReal.coe_zero, div_zero]
    let F := fun s : ℝ => g f hh (Real.toNNReal s)
    have hd (s : ℝ) (hs : 0 < s) :
        HasDerivAt F
          (4 * π * g f hh (Real.toNNReal s) *
            (f (Real.toNNReal s) - mean f (Real.toNNReal s)) ^ 2 / s) s := by
      have h := hasDerivAt_g f hh (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
      rwa [Real.coe_toNNReal s hs.le] at h
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    · exact ((continuous_g f hh).comp continuous_real_toNNReal).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · have hc : ContinuousAt (fun s : ℝ => π * x ^ 2 * s / (b ^ 4 * (b + s) ^ 4)) 0 := by
        fun_prop (disch := positivity)
      have ht : Tendsto (fun s : ℝ => π * x ^ 2 * s / (b ^ 4 * (b + s) ^ 4))
          (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero, zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [(hd s hs).deriv]
        have := (g_pos f hh (Real.toNNReal s)).le
        have sp : 0 ≤ s := le_of_lt hs
        positivity
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact hasDerivAt_g_le hb hf hh (Real.toNNReal s) (Real.toNNReal_pos.mpr hs) |>
          fun h => by simpa only [Real.coe_toNNReal s hs.le] using h
  · exact (hasDerivAt_g f hh r (pos_iff_ne_zero.mpr hr)).hasDerivWithinAt

/-- The one-sided metric derivative estimate, including its zero centre value. -/
theorem derivWithin_gX_le (hH : MemXPrimeBall T x H) (u r : ℝ≥0) :
    let b : ℝ := 1 + ((min u T : ℝ≥0) : ℝ) / 2
    derivWithin (fun s : ℝ => gX hH.1 u s.toNNReal) (Ici 0) r ≤
      π * x ^ 2 * (r : ℝ) / (b ^ 4 * (b + (r : ℝ)) ^ 4) := by
  dsimp only [gX]
  rw [(slice_hasDerivWithinAt_g (base_one u) (clamped_slice hH u) _ r).derivWithin
    (uniqueDiffOn_Ici (0 : ℝ) r r.coe_nonneg)]
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [NNReal.coe_zero, div_zero, mul_zero, zero_div, le_refl]
  · have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    apply (div_le_iff₀ rp).mpr
    have h := metric_derivative_le (base_one u) (clamped_slice hH u)
      (hH.1.isSlice _ (min_le_right u T)) r r.coe_nonneg
    simp only [Real.toNNReal_coe] at h
    convert h using 1
    ring

end Christodoulou.Bondi.XWC
