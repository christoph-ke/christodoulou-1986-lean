module
public import Christodoulou.Frozen.Bondi.DerivHBarX
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
public import Christodoulou.Frozen.Bondi.LinearSource
import Christodoulou.Frozen.Radial.HasDerivAtMean
import Christodoulou.Frozen.Radial.ContinuousMean
import Christodoulou.Frozen.Bondi.HasDerivAtG
import Christodoulou.Frozen.Bondi.GPos
import Christodoulou.Frozen.Bondi.GLeOne
import Christodoulou.Frozen.Bondi.HasDerivAtDerivGBar
import Christodoulou.Frozen.Bondi.HasDerivWithinAtGBarX
import Christodoulou.Frozen.Bondi.DerivGBarXNonneg
import Christodoulou.Frozen.Bondi.DerivGBarXLe
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Bondi.XBallContinuity
import Christodoulou.Radial.MeanBasic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Radial regularity of the X-ball coefficients

The clamped mean and the averaged metric have continuous radial derivatives, including
one-sided derivatives at the centre. Nonsingular integral representations identify these
extensions. The coefficient and source inherit radial derivatives, weighted bounds, and
chain rules for real curves taking values in the nonnegative half-line.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial Filter Topology

namespace XCoef

private theorem continuous_hBarX (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => hBarX u₀ H p.1 p.2) := by
  simp only [hBarX]
  simp_rw [mean_eq_integral_unitInterval]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact H.continuous.comp
    (((continuous_fst.comp continuous_fst).min continuous_const).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)))

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

private lemma deriv_bound_two (c s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => c * t ^ 2 / (2 * (1 + t) ^ 2))
      (c * s / (1 + s) ^ 3) s := by
  have hn : 1 + s ≠ 0 := by positivity
  convert (((hasDerivAt_id s).pow 2).const_mul c).div
    ((((hasDerivAt_id s).const_add 1).pow 2).const_mul 2) (by dsimp; positivity) using 1
  · rfl
  · dsimp
    field_simp
    ring

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

private lemma slice_abs_sub_mean_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀)
    (r : ℝ≥0) :
    |H.curry u r - mean (H.curry u) r| ≤ x * (r : ℝ) / (2 * (1 + (r : ℝ)) ^ 2) := by
  have hx : 0 ≤ x := by
    have hb := hH.2.2 u hu 0
    exact le_trans (by positivity) hb
  rcases eq_or_ne r 0 with rfl | hr
  · simp [mean_zero]
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let f := H.curry u
  let D := fun s : ℝ => derivWithin (fun t : ℝ => H (u, Real.toNNReal t)) (Ici 0) s
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => f (Real.toNNReal t)) (D s) s := by
    exact ((hH.1 u hu).differentiableOn (by norm_num) s hs.le).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hs)
  have hb (s : ℝ) (hs : 0 < s) : |s * D s| ≤ x * s / (1 + s) ^ 3 := by
    have hw := hH.2.2 u hu (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.le] at hw
    have hw' : (1 + s) ^ 4 * |D s| ≤ x :=
      le_trans (le_add_of_nonneg_left (by positivity)) hw
    have hp : (1 + s) ^ 3 ≤ (1 + s) ^ 4 := by
      exact pow_le_pow_right₀ (by linarith) (by norm_num)
    have hw'' : (1 + s) ^ 3 * |D s| ≤ x :=
      (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans hw'
    rw [abs_mul, abs_of_pos hs, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hw'' hs.le]
  have hB : ContinuousOn (fun s : ℝ => x * s ^ 2 / (2 * (1 + s) ^ 2)) (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow _))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hc := abs_compare_of_deriv (continuous_mul_sub_mean f).continuousOn hB
    (fun s hs => hasDerivAt_mul_sub_mean f hs (hd s hs))
    (fun s hs => deriv_bound_two x s hs.le) (by simp) hb r.coe_nonneg
  simp only [Real.toNNReal_coe, abs_mul, abs_of_nonneg r.coe_nonneg] at hc
  apply (le_div_iff₀ (by positivity)).mpr
  have := (le_div_iff₀ (by positivity)).mp hc
  nlinarith

private lemma x_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) : 0 ≤ x :=
  le_trans (by positivity) (hH.2.2 0 (by positivity) 0)

private lemma slice_value_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    |H (u, r)| ≤ x / (1 + (r : ℝ)) ^ 2 := by
  have hb := (le_add_of_nonneg_right (by positivity)).trans (hH.2.2 u hu r)
  have hp : (1 + (r : ℝ)) ^ 2 ≤ (1 + (r : ℝ)) ^ 3 :=
    pow_le_pow_right₀ (by linarith [r.coe_nonneg]) (by norm_num)
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans hb

private lemma deriv_bound_one (c s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => c * t / (1 + t)) (c / (1 + s) ^ 2) s := by
  convert ((hasDerivAt_id s).const_mul c).div ((hasDerivAt_id s).const_add 1)
    (by dsimp; positivity) using 1
  · rfl
  · dsimp
    ring

/-- `|h̄| ≤ x/(1 + r)` (the `u`-unweighted form of (9.4), p. 352). -/
theorem abs_hBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |hBarX u₀ H u r| ≤ x / (1 + (r : ℝ)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa only [hBarX, mean_zero, ContinuousMap.curry_apply, NNReal.coe_zero,
      add_zero, one_pow, div_one] using slice_value_le hH (min u u₀) (min_le_right u u₀) 0
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let f := H.curry (min u u₀)
  let F := fun s : ℝ => ∫ t in (0 : ℝ)..s, lift f t
  have hc : Continuous F :=
    intervalIntegral.continuous_primitive (continuous_lift f).intervalIntegrable 0
  have hB : ContinuousOn (fun s : ℝ => x * s / (1 + s)) (Ici 0) :=
    (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.add continuousOn_id) (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hb (s : ℝ) (hs : 0 < s) : |lift f s| ≤ x / (1 + s) ^ 2 := by
    simpa only [lift, f, ContinuousMap.curry_apply, Real.coe_toNNReal _ hs.le] using
      slice_value_le hH (min u u₀) (min_le_right u u₀) (Real.toNNReal s)
  have hle := abs_compare_of_deriv hc.continuousOn hB
    (fun s _ => hasDerivAt_integral_lift f s) (fun s hs => deriv_bound_one x s hs.le)
    (by simp [F]) hb r.coe_nonneg
  change |∫ t in (0 : ℝ)..(r : ℝ), lift f t| ≤ x * (r : ℝ) / (1 + (r : ℝ)) at hle
  rw [← coe_mul_mean, abs_mul, abs_of_pos hrp] at hle
  change |mean f r| ≤ x / (1 + (r : ℝ))
  apply (mul_le_mul_iff_right₀ hrp).mp
  convert hle using 1
  ring

private lemma continuous_sliceDerivative {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivWithin
      (fun s : ℝ => H (min p.1 u₀, Real.toNNReal s)) (Ici 0) (p.2 : ℝ)) := by
  have hc : Continuous (fun p : ℝ≥0 × ℝ≥0 => (((min p.1 u₀ : ℝ≥0) : ℝ), (p.2 : ℝ))) :=
    (NNReal.continuous_coe.comp (continuous_fst.min continuous_const)).prodMk
      (NNReal.continuous_coe.comp continuous_snd)
  have hm (p : ℝ≥0 × ℝ≥0) :
      (((min p.1 u₀ : ℝ≥0) : ℝ), (p.2 : ℝ)) ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0 :=
    ⟨⟨(min p.1 u₀).coe_nonneg, by exact_mod_cast min_le_right p.1 u₀⟩, p.2.coe_nonneg⟩
  simpa only [Function.comp_def, Real.toNNReal_coe] using hH.2.1.comp_continuous hc hm

private noncomputable def betaAverage (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ))
    (u r : ℝ≥0) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * derivWithin
    (fun s : ℝ => H (min u u₀, Real.toNNReal s)) (Ici 0)
      (Real.toNNReal ((r : ℝ) * t) : ℝ)

private lemma continuous_betaAverage {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => betaAverage u₀ H p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply continuous_snd.mul
  exact (continuous_sliceDerivative hH).comp
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)))

private lemma betaAverage_zero (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u : ℝ≥0) :
    betaAverage u₀ H u 0 =
      derivWithin (fun s : ℝ => H (min u u₀, Real.toNNReal s)) (Ici 0) 0 / 2 := by
  simp only [betaAverage, NNReal.coe_zero, zero_mul, Real.toNNReal_zero]
  rw [intervalIntegral.integral_mul_const, integral_id]
  norm_num
  ring

private lemma betaAverage_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) (hr : 0 < r) :
    betaAverage u₀ H u r = (H (min u u₀, r) - hBarX u₀ H u r) / (r : ℝ) := by
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
  let f := H.curry (min u u₀)
  let D := fun s : ℝ => derivWithin (fun t : ℝ => H (min u u₀, Real.toNNReal t)) (Ici 0) s
  have hD : ContinuousOn D (Ici 0) := by
    have hc := (continuous_sliceDerivative hH).comp
      ((continuous_const (y := u)).prodMk continuous_real_toNNReal)
    apply hc.continuousOn.congr
    intro s hs
    simp only [D, Function.comp_def, Real.coe_toNNReal s hs]
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => f (Real.toNNReal t)) (D s) s :=
    ((hH.1 _ (min_le_right u u₀)).differentiableOn one_ne_zero s hs.le).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hs)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le r.coe_nonneg
    (continuous_mul_sub_mean f).continuousOn
    (fun s hs => hasDerivAt_mul_sub_mean f hs.1 (hd s hs.1))
    ((continuousOn_id.mul hD).mono Icc_subset_Ici_self |>.intervalIntegrable_of_Icc r.coe_nonneg)
  simp only [Real.toNNReal_coe, zero_mul, sub_zero] at hi
  have hscale : (∫ t in (0 : ℝ)..1, (r : ℝ) * t * D ((r : ℝ) * t)) =
      (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), s * D s := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun s => s * D s) hrp.ne'
  rw [hi] at hscale
  have heq : (∫ t in (0 : ℝ)..1, (r : ℝ) * t * D ((r : ℝ) * t)) =
      (r : ℝ) * betaAverage u₀ H u r := by
    rw [betaAverage, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [Real.coe_toNNReal _ (mul_nonneg r.coe_nonneg ht.1)]
    exact mul_assoc _ _ _
  rw [heq] at hscale
  change betaAverage u₀ H u r = (f r - mean f r) / (r : ℝ)
  field_simp at hscale ⊢
  nlinarith only [hscale]

private lemma derivHBarX_eq_betaAverage {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivHBarX hH u r = betaAverage u₀ H u r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa only [derivHBarX, ite_true] using (betaAverage_zero u₀ H u).symm
  · rw [derivHBarX, ite_eq_right hr, betaAverage_pos hH u r (pos_iff_ne_zero.mpr hr)]

/-- `h̄` is differentiable in `r` within `[0, ∞)` with derivative `derivHBarX`, including the
centre (one-sided). -/
theorem hasDerivWithinAt_hBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => hBarX u₀ H u (Real.toNNReal s)) (derivHBarX hH u r)
      (Ici 0) (r : ℝ) := by
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => hBarX u₀ H u (Real.toNNReal t))
        (derivHBarX hH u (Real.toNNReal s)) s := by
    have hm := hasDerivAt_mean (H.curry (min u u₀))
      (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
    rw [Real.coe_toNNReal s hs.le] at hm
    simpa only [derivHBarX, ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hs)),
      Real.coe_toNNReal s hs.le, Real.toNNReal_coe, hBarX, ContinuousMap.curry_apply] using hm
  rcases eq_or_ne r 0 with rfl | hr
  · have hc : Continuous (fun s : ℝ => betaAverage u₀ H u (Real.toNNReal s)) :=
      (continuous_betaAverage hH).comp ((continuous_const (y := u)).prodMk continuous_real_toNNReal)
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    · exact ((continuous_hBarX u₀ H).comp
        ((continuous_const (y := u)).prodMk
          continuous_real_toNNReal)).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · have ht : Tendsto (fun s : ℝ => betaAverage u₀ H u (Real.toNNReal s))
          (𝓝[>] 0) (𝓝 (betaAverage u₀ H u (Real.toNNReal 0))) :=
        hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [Real.toNNReal_zero, ← derivHBarX_eq_betaAverage hH u 0] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hd s hs).deriv.trans (derivHBarX_eq_betaAverage hH u _)).symm
  · have hm := hd (r : ℝ) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))
    simpa only [Real.toNNReal_coe] using hm.hasDerivWithinAt

/-- Joint continuity of `∂_r h̄` on the quadrant, including the centre. -/
theorem continuous_derivHBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivHBarX hH p.1 p.2) := by
  have heq : (fun p : ℝ≥0 × ℝ≥0 => derivHBarX hH p.1 p.2) =
      (fun p : ℝ≥0 × ℝ≥0 => betaAverage u₀ H p.1 p.2) :=
    funext fun p => derivHBarX_eq_betaAverage hH p.1 p.2
  rw [heq]
  exact continuous_betaAverage hH

/-- `|∂_r h̄| ≤ x/(2 (1 + r)²)` (from the `u`-unweighted form of (9.6), p. 353). -/
theorem abs_derivHBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |derivHBarX hH u r| ≤ x / (2 * (1 + (r : ℝ)) ^ 2) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hb := hH.2.2 (min u u₀) (min_le_right u u₀) 0
    simp only [NNReal.coe_zero, add_zero, one_pow, one_mul] at hb
    have hD := (le_add_of_nonneg_left (abs_nonneg _)).trans hb
    simp only [derivHBarX, ite_true, NNReal.coe_zero, add_zero, one_pow, mul_one,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hD (by norm_num)
  · have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hb := slice_abs_sub_mean_le hH (min u u₀) (min_le_right u u₀) r
    rw [derivHBarX, ite_eq_right hr, abs_div, abs_of_pos hrp]
    change |H.curry (min u u₀) r - mean (H.curry (min u u₀)) r| / (r : ℝ) ≤ _
    calc
      _ ≤ (x * (r : ℝ) / (2 * (1 + (r : ℝ)) ^ 2)) / (r : ℝ) :=
        div_le_div_of_nonneg_right hb r.coe_nonneg
      _ = _ := by field_simp

private noncomputable def metricAverage {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ 2 * gX hH u (Real.toNNReal ((r : ℝ) * t)) *
    derivHBarX hH u (Real.toNNReal ((r : ℝ) * t)) ^ 2

private lemma continuous_metricAverage {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => metricAverage hH p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hc : Continuous (fun p : (ℝ≥0 × ℝ≥0) × ℝ =>
      (p.1.1, Real.toNNReal ((p.1.2 : ℝ) * p.2))) :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd))
  exact ((continuous_snd.pow 2).mul ((continuous_gX hH).comp hc)).mul
    (((continuous_derivHBarX hH).comp hc).pow 2)

private lemma metricAverage_zero {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) :
    metricAverage hH u 0 = gX hH u 0 * derivHBarX hH u 0 ^ 2 / 3 := by
  simp only [metricAverage, NNReal.coe_zero, zero_mul, Real.toNNReal_zero]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_pow]
  norm_num
  ring

private lemma hasDerivAt_gX_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gX hH u (Real.toNNReal t))
      (4 * π * s * gX hH u (Real.toNNReal s) * derivHBarX hH u (Real.toNNReal s) ^ 2) s := by
  have hd := hasDerivAt_g (H.curry (min u u₀)) (hH.isSlice _ (min_le_right u u₀))
    (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
  rw [Real.coe_toNNReal s hs.le] at hd
  convert hd using 1
  · rfl
  · simp only [derivHBarX, ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hs)),
      Real.coe_toNNReal s hs.le, gX, hBarX, ContinuousMap.curry_apply]
    field_simp

private lemma derivGBarX_eq_metricAverage {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivGBarX hH u r = 4 * π * (r : ℝ) * metricAverage hH u r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [derivGBarX, ite_true, NNReal.coe_zero, mul_zero, zero_mul]
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let f := gMap (H.curry (min u u₀)) (hH.isSlice _ (min_le_right u u₀))
  let K := fun s : ℝ => gX hH u (Real.toNNReal s) * derivHBarX hH u (Real.toNNReal s) ^ 2
  have hK : Continuous K :=
    ((continuous_gX hH).comp ((continuous_const (y := u)).prodMk continuous_real_toNNReal)).mul
      (((continuous_derivHBarX hH).comp
        ((continuous_const (y := u)).prodMk continuous_real_toNNReal)).pow 2)
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => t * (f (Real.toNNReal t) - mean f (Real.toNNReal t)))
        (4 * π * s ^ 2 * K s) s := by
    convert hasDerivAt_mul_sub_mean f hs (hasDerivAt_gX_pos hH u s hs) using 1
    dsimp only [K]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le r.coe_nonneg
    (continuous_mul_sub_mean f).continuousOn (fun s hs => hd s hs.1)
    ((continuous_const.mul (continuous_id.pow 2)).mul hK |>.intervalIntegrable 0 (r : ℝ))
  simp only [Real.toNNReal_coe, zero_mul, sub_zero] at hi
  have hscale : (r : ℝ) * (∫ t in (0 : ℝ)..1, 4 * π * ((r : ℝ) * t) ^ 2 * K ((r : ℝ) * t)) =
      ∫ s in (0 : ℝ)..(r : ℝ), 4 * π * s ^ 2 * K s := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := 1)
        (f := fun s => 4 * π * s ^ 2 * K s) (r : ℝ)
  have heq : (∫ t in (0 : ℝ)..1, 4 * π * ((r : ℝ) * t) ^ 2 * K ((r : ℝ) * t)) =
      (4 * π * (r : ℝ) ^ 2) * metricAverage hH u r := by
    rw [metricAverage, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [K]
    ring
  rw [heq, hi] at hscale
  change (r : ℝ) * (4 * π * (r : ℝ) ^ 2 * metricAverage hH u r) =
      (r : ℝ) * (gX hH u r - gBarX hH u r) at hscale
  rw [derivGBarX, ite_eq_right hr]
  apply (div_eq_iff hrp.ne').mpr
  have hcancel := (mul_left_cancel₀ hrp.ne' hscale).symm
  convert hcancel using 1
  ring

private lemma deriv2GBarX_eq_average {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    deriv2GBarX hH u r = -8 * π * metricAverage hH u r +
      4 * π * gX hH u r * derivHBarX hH u r ^ 2 := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [metricAverage_zero]
    simp only [deriv2GBarX, derivHBarX, ite_true]
    ring
  · have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    rw [deriv2GBarX, ite_eq_right hr, derivGBarX_eq_metricAverage]
    field_simp
    ring

private lemma continuous_secondAverage {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => -8 * π * metricAverage hH p.1 p.2 +
      4 * π * gX hH p.1 p.2 * derivHBarX hH p.1 p.2 ^ 2) :=
  (continuous_const.mul (continuous_metricAverage hH)).add
    ((continuous_const.mul (continuous_gX hH)).mul ((continuous_derivHBarX hH).pow 2))

private lemma hasDerivAt_derivGBarX_pos {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => derivGBarX hH u (Real.toNNReal s)) (deriv2GBarX hH u r)
      (r : ℝ) := by
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hd := hasDerivAt_deriv_gBar (H.curry (min u u₀))
    (hH.isSlice _ (min_le_right u u₀)) r hr
  have heq : (fun s : ℝ => derivGBarX hH u (Real.toNNReal s)) =ᶠ[𝓝 (r : ℝ)]
      (deriv (fun s : ℝ => gBarX hH u (Real.toNNReal s))) := by
    filter_upwards [Ioi_mem_nhds hrp] with s hs
    have hg := (hasDerivWithinAt_gBarX hH u (Real.toNNReal s)).hasDerivAt
      (by rw [Real.coe_toNNReal s hs.le]; exact Ici_mem_nhds hs)
    rw [Real.coe_toNNReal s hs.le] at hg
    exact hg.deriv.symm
  have hnew := hd.congr_of_eventuallyEq heq
  convert hnew using 1
  simp only [deriv2GBarX, derivGBarX, derivHBarX, ite_eq_right (ne_of_gt hr),
    gX, gBarX, hBarX, ContinuousMap.curry_apply]
  field_simp

/-- Joint continuity of `∂²_r ḡ` on the quadrant, including the centre. -/
theorem continuous_deriv2GBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => deriv2GBarX hH p.1 p.2) := by
  have heq : (fun p : ℝ≥0 × ℝ≥0 => deriv2GBarX hH p.1 p.2) =
      (fun p : ℝ≥0 × ℝ≥0 => -8 * π * metricAverage hH p.1 p.2 +
        4 * π * gX hH p.1 p.2 * derivHBarX hH p.1 p.2 ^ 2) :=
    funext fun p => deriv2GBarX_eq_average hH p.1 p.2
  rw [heq]
  exact continuous_secondAverage hH

/-- `∂_r ḡ` is differentiable in `r` within `[0, ∞)` with derivative `deriv2GBarX`, including
the centre (one-sided); no second derivative of `H` is used. -/
theorem hasDerivWithinAt_derivGBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => derivGBarX hH u (Real.toNNReal s)) (deriv2GBarX hH u r)
      (Ici 0) (r : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hd (s : ℝ) (hs : 0 < s) :
        HasDerivAt (fun t : ℝ => derivGBarX hH u (Real.toNNReal t))
          (deriv2GBarX hH u (Real.toNNReal s)) s := by
      have hh := hasDerivAt_derivGBarX_pos hH u (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
      rwa [Real.coe_toNNReal s hs.le] at hh
    have hc : Continuous (fun s : ℝ => deriv2GBarX hH u (Real.toNNReal s)) :=
      (continuous_deriv2GBarX hH).comp
        ((continuous_const (y := u)).prodMk continuous_real_toNNReal)
    have ht : Tendsto (fun s : ℝ => deriv2GBarX hH u (Real.toNNReal s))
        (𝓝[>] 0) (𝓝 (deriv2GBarX hH u 0)) := by
      simpa only [Real.toNNReal_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    · exact ((continuous_derivGBarX hH).comp
        ((continuous_const (y := u)).prodMk
          continuous_real_toNNReal)).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hd s hs).deriv.symm
  · exact (hasDerivAt_derivGBarX_pos hH u r (pos_iff_ne_zero.mpr hr)).hasDerivWithinAt

/-- `|∂²_r ḡ| ≤ π x²/(1 + r)³` (the `u`-unweighted form of the second display of p. 356). -/
theorem abs_deriv2GBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : |deriv2GBarX hH u r| ≤ π * x ^ 2 / (1 + (r : ℝ)) ^ 3 := by
  have hx := x_nonneg hH
  have hg0 (s : ℝ≥0) : 0 ≤ gX hH u s :=
    (g_pos _ (hH.isSlice _ (min_le_right u u₀)) s).le
  have hg1 (s : ℝ≥0) : gX hH u s ≤ 1 :=
    g_le_one _ (hH.isSlice _ (min_le_right u u₀)) s
  have hBs (s : ℝ≥0) : 4 * π * gX hH u s * derivHBarX hH u s ^ 2 ≤
      π * x ^ 2 / (1 + (s : ℝ)) ^ 4 := by
    have hb := abs_derivHBarX_le hH u s
    have hb2 : derivHBarX hH u s ^ 2 ≤ (x / (2 * (1 + (s : ℝ)) ^ 2)) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
    calc
      _ ≤ 4 * π * derivHBarX hH u s ^ 2 := by
        have hh := mul_le_mul_of_nonneg_right (hg1 s)
          (show 0 ≤ 4 * π * derivHBarX hH u s ^ 2 by positivity)
        nlinarith only [hh]
      _ ≤ 4 * π * (x / (2 * (1 + (s : ℝ)) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = _ := by field_simp; ring
  rcases eq_or_ne r 0 with rfl | hr
  · have hb := hBs 0
    have hval : deriv2GBarX hH u 0 =
        (4 * π * gX hH u 0 * derivHBarX hH u 0 ^ 2) / 3 := by
      simp only [deriv2GBarX, derivHBarX, ite_true]
      ring
    have := hg0 0
    rw [hval, abs_of_nonneg (by positivity)]
    simp only [NNReal.coe_zero, add_zero, one_pow, div_one] at hb ⊢
    have hp : 0 ≤ π * x ^ 2 := by positivity
    linarith only [hb, hp]
  · have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hA0 : 0 ≤ 2 * derivGBarX hH u r / (r : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) (derivGBarX_nonneg hH u r)) r.coe_nonneg
    have hB0 : 0 ≤ 4 * π * gX hH u r * derivHBarX hH u r ^ 2 := by
      have := hg0 r
      positivity
    have hAle : 2 * derivGBarX hH u r / (r : ℝ) ≤ π * x ^ 2 / (1 + (r : ℝ)) ^ 3 := by
      calc
        _ ≤ 2 * (π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3) / (r : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (derivGBarX_le hH u r) (by norm_num)) r.coe_nonneg
        _ = (2 / 3) * (π * x ^ 2 / (1 + (r : ℝ)) ^ 3) := by field_simp
        _ ≤ _ := by
          have hp : 0 ≤ π * x ^ 2 / (1 + (r : ℝ)) ^ 3 := by positivity
          linarith only [hp]
    have hBle : 4 * π * gX hH u r * derivHBarX hH u r ^ 2 ≤
        π * x ^ 2 / (1 + (r : ℝ)) ^ 3 := by
      apply (hBs r).trans
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by linarith [r.coe_nonneg]) (by norm_num))
    rw [deriv2GBarX, ite_eq_right hr]
    simp only [neg_mul, neg_div]
    apply abs_le.mpr
    constructor
    · linarith only [hB0, hAle]
    · linarith only [hA0, hBle]

/-- The radial derivative of the coefficient `a = ½ ∂_r ḡ` of (7.2): `∂_r a = ½ ∂²_r ḡ`. -/
theorem hasDerivWithinAt_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => linearCoeff hH u (Real.toNNReal s))
      (1 / 2 * deriv2GBarX hH u r) (Ici 0) (r : ℝ) := by
  exact (hasDerivWithinAt_derivGBarX hH u r).const_mul (1 / 2)

/-- The radial derivative of the source `f = −a h̄` of (7.2) ([P] p. 355, after (9.16)):
`∂_r f = −(∂_r a) h̄ − a ∂_r h̄`. -/
theorem hasDerivWithinAt_linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => linearSource hH u (Real.toNNReal s))
      (-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r -
        linearCoeff hH u r * derivHBarX hH u r) (Ici 0) (r : ℝ) := by
  have hc := (hasDerivWithinAt_linearCoeff hH u r).neg.mul (hasDerivWithinAt_hBarX hH u r)
  convert hc using 1
  · ext s
    rfl
  · simp only [Pi.neg_apply, Real.toNNReal_coe, neg_mul, sub_eq_add_neg]


/-- `|∂_r f| ≤ 7π x³/(12 (1 + r)⁴)` for the radial derivative of the source `f = −a h̄`, written
as the explicit formula of `hasDerivWithinAt_linearSource` (the `u`-unweighted form of (9.17),
p. 356). -/
theorem abs_deriv_linearSource_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |-(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r - linearCoeff hH u r * derivHBarX hH u r| ≤
      7 * π * x ^ 3 / (12 * (1 + (r : ℝ)) ^ 4) := by
  have hx := x_nonneg hH
  have hc := abs_deriv2GBarX_le hH u r
  have hh := abs_hBarX_le hH u r
  have hb := abs_derivHBarX_le hH u r
  have hg0 := derivGBarX_nonneg hH u r
  have hg1 := derivGBarX_le hH u r
  have hr := r.coe_nonneg
  set R : ℝ := 1 + (r : ℝ) with hR
  have hR1 : 1 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  set c := deriv2GBarX hH u r
  set hb' := hBarX u₀ H u r
  set β := derivHBarX hH u r
  set d := derivGBarX hH u r
  have ha : linearCoeff hH u r = 1 / 2 * d := rfl
  rw [ha]
  have e1 : |-(1 / 2 * c) * hb' - 1 / 2 * d * β| ≤ 1 / 2 * |c| * |hb'| + 1 / 2 * d * |β| := by
    calc _ ≤ |-(1 / 2 * c) * hb'| + |1 / 2 * d * β| := abs_sub _ _
      _ = _ := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
          abs_of_nonneg hg0]
  have e2 : 1 / 2 * |c| * |hb'| ≤ 1 / 2 * (π * x ^ 2 / R ^ 3) * (x / R) := by
    gcongr
  have e3 : 1 / 2 * d * |β| ≤ 1 / 2 * (π / 3 * x ^ 2 * (r : ℝ) / R ^ 3) * (x / (2 * R ^ 2)) := by
    gcongr
  have e4 : 1 / 2 * (π * x ^ 2 / R ^ 3) * (x / R) +
      1 / 2 * (π / 3 * x ^ 2 * (r : ℝ) / R ^ 3) * (x / (2 * R ^ 2)) ≤
      7 * π * x ^ 3 / (12 * R ^ 4) := by
    have hrR : (r : ℝ) ≤ R := by linarith
    have hpx : 0 ≤ π * x ^ 3 := by positivity
    have heq : 1 / 2 * (π * x ^ 2 / R ^ 3) * (x / R) +
        1 / 2 * (π / 3 * x ^ 2 * (r : ℝ) / R ^ 3) * (x / (2 * R ^ 2)) =
        π * x ^ 3 / (2 * R ^ 4) + π * x ^ 3 * ((r : ℝ) / R) / (12 * R ^ 4) := by
      field_simp
      ring
    have hq : (r : ℝ) / R ≤ 1 := (div_le_one hRp).mpr hrR
    have h2 : π * x ^ 3 * ((r : ℝ) / R) / (12 * R ^ 4) ≤ π * x ^ 3 * 1 / (12 * R ^ 4) := by
      gcongr
    have h3 : π * x ^ 3 / (2 * R ^ 4) + π * x ^ 3 * 1 / (12 * R ^ 4) =
        7 * π * x ^ 3 / (12 * R ^ 4) := by
      field_simp
      ring
    linarith
  linarith

/-- At a positive radius the ordinary derivative of the metric mean equals `derivGBarX`. -/
theorem deriv_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) (hr : 0 < r) :
    deriv (fun s : ℝ => gBarX hH u s.toNNReal) (r : ℝ) = derivGBarX hH u r :=
  ((hasDerivWithinAt_gBarX hH u r).hasDerivAt (Ici_mem_nhds (NNReal.coe_pos.mpr hr))).deriv

/-- The canonical derivative within the half-line of the linear coefficient. -/
theorem derivWithin_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivWithin (fun s : ℝ => linearCoeff hH u s.toNNReal) (Ici 0) (r : ℝ) =
      1 / 2 * deriv2GBarX hH u r := by
  exact (hasDerivWithinAt_linearCoeff hH u r).derivWithin
    (uniqueDiffOn_Ici 0 _ r.coe_nonneg)

/-- The canonical derivative within the half-line of the linear source. -/
theorem derivWithin_linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivWithin (fun s : ℝ => linearSource hH u s.toNNReal) (Ici 0) (r : ℝ) =
      -(1 / 2 * deriv2GBarX hH u r) * hBarX u₀ H u r -
        linearCoeff hH u r * derivHBarX hH u r := by
  exact (hasDerivWithinAt_linearSource hH u r).derivWithin
    (uniqueDiffOn_Ici 0 _ r.coe_nonneg)

/-- Joint continuity of the explicit radial derivative of the coefficient. -/
theorem continuous_deriv_linearCoeff {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => 1 / 2 * deriv2GBarX hH p.1 p.2) :=
  continuous_const.mul (continuous_deriv2GBarX hH)

/-- Joint continuity of the explicit radial derivative of the source. -/
theorem continuous_deriv_linearSource {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      -(1 / 2 * deriv2GBarX hH p.1 p.2) * hBarX u₀ H p.1 p.2 -
        linearCoeff hH p.1 p.2 * derivHBarX hH p.1 p.2) :=
  ((continuous_deriv_linearCoeff hH).neg.mul (continuous_hBarX u₀ H)).sub
    ((continuous_const.mul (continuous_derivGBarX hH)).mul (continuous_derivHBarX hH))


theorem linearCoeff_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : 0 ≤ linearCoeff hH u r :=
  mul_nonneg (by norm_num) (derivGBarX_nonneg hH u r)


theorem linearCoeff_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    linearCoeff hH u r ≤ π / 6 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 := by
  calc
    _ ≤ 1 / 2 * (π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3) :=
      mul_le_mul_of_nonneg_left (derivGBarX_le hH u r) (by norm_num)
    _ = _ := by ring


theorem linearCoeff_le_uniform {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : linearCoeff hH u r ≤ π / 12 * x ^ 2 := by
  have hr := r.coe_nonneg
  have hp : (1 + (r : ℝ)) ^ 2 ≤ (1 + (r : ℝ)) ^ 3 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hq : (r : ℝ) / (1 + (r : ℝ)) ^ 3 ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp, sq_nonneg (r : ℝ)]
  calc
    _ ≤ π / 6 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 := linearCoeff_le hH u r
    _ = (π / 6 * x ^ 2) * ((r : ℝ) / (1 + (r : ℝ)) ^ 3) := by ring
    _ ≤ (π / 6 * x ^ 2) * (1 / 2) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring


theorem abs_linearSource_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |linearSource hH u r| ≤ π * x ^ 3 / (6 * (1 + (r : ℝ)) ^ 3) := by
  have hx := x_nonneg hH
  have hr := r.coe_nonneg
  have hR : 0 < 1 + (r : ℝ) := by positivity
  change |-(linearCoeff hH u r) * hBarX u₀ H u r| ≤ _
  rw [abs_mul, abs_neg, abs_of_nonneg (linearCoeff_nonneg hH u r)]
  calc
    _ ≤ (π / 6 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3) *
        (x / (1 + (r : ℝ))) := by
      gcongr
      · exact linearCoeff_le hH u r
      · exact abs_hBarX_le hH u r
    _ = (π * x ^ 3 / (6 * (1 + (r : ℝ)) ^ 3)) *
        ((r : ℝ) / (1 + (r : ℝ))) := by field_simp
    _ ≤ (π * x ^ 3 / (6 * (1 + (r : ℝ)) ^ 3)) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one hR).mpr (by linarith)
    _ = _ := mul_one _


theorem abs_sub_hBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |H (min u u₀, r) - hBarX u₀ H u r| ≤
      x * (r : ℝ) / (2 * (1 + (r : ℝ)) ^ 2) :=
  slice_abs_sub_mean_le hH (min u u₀) (min_le_right u u₀) r


theorem derivHBarX_eq_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivHBarX hH u r = ∫ t in (0 : ℝ)..1, t * derivWithin
      (fun s : ℝ => H (min u u₀, s.toNNReal)) (Ici 0) ((r : ℝ) * t) := by
  rw [derivHBarX_eq_betaAverage, betaAverage]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only
  rw [Real.coe_toNNReal _ (mul_nonneg r.coe_nonneg ht.1)]


theorem deriv2GBarX_eq_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    deriv2GBarX hH u r =
      -8 * π * (∫ t in (0 : ℝ)..1, t ^ 2 * gX hH u ((r : ℝ) * t).toNNReal *
        derivHBarX hH u ((r : ℝ) * t).toNNReal ^ 2) +
      4 * π * gX hH u r * derivHBarX hH u r ^ 2 :=
  deriv2GBarX_eq_average hH u r

/-- The coefficient derivative at a nonnegative real point, without a subtype coercion. -/
theorem hasDerivWithinAt_linearCoeff_real {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0)
    (y : ℝ) (hy : 0 ≤ y) :
    HasDerivWithinAt (fun s : ℝ => linearCoeff hH u s.toNNReal)
      (1 / 2 * deriv2GBarX hH u y.toNNReal) (Ici 0) y := by
  simpa only [Real.coe_toNNReal _ hy] using
    hasDerivWithinAt_linearCoeff hH u y.toNNReal

/-- The source derivative at a nonnegative real point, without a subtype coercion. -/
theorem hasDerivWithinAt_linearSource_real {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0)
    (y : ℝ) (hy : 0 ≤ y) :
    HasDerivWithinAt (fun s : ℝ => linearSource hH u s.toNNReal)
      (-(1 / 2 * deriv2GBarX hH u y.toNNReal) * hBarX u₀ H u y.toNNReal -
        linearCoeff hH u y.toNNReal * derivHBarX hH u y.toNNReal) (Ici 0) y := by
  simpa only [Real.coe_toNNReal _ hy] using
    hasDerivWithinAt_linearSource hH u y.toNNReal

/-- Chain rule for the coefficient along a real curve in the nonnegative half-line. -/
theorem hasDerivWithinAt_linearCoeff_comp {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {φ : ℝ → ℝ} {φ' t : ℝ} {s : Set ℝ} (hφ : HasDerivWithinAt φ φ' s t)
    (hφs : MapsTo φ s (Ici 0)) (hφt : 0 ≤ φ t) :
    HasDerivWithinAt (fun τ => linearCoeff hH u (φ τ).toNNReal)
      (1 / 2 * deriv2GBarX hH u (φ t).toNNReal * φ') s t :=
  (hasDerivWithinAt_linearCoeff_real hH u (φ t) hφt).comp t hφ hφs

/-- Chain rule for the source along a real curve in the nonnegative half-line. -/
theorem hasDerivWithinAt_linearSource_comp {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0)
    {φ : ℝ → ℝ} {φ' t : ℝ} {s : Set ℝ} (hφ : HasDerivWithinAt φ φ' s t)
    (hφs : MapsTo φ s (Ici 0)) (hφt : 0 ≤ φ t) :
    HasDerivWithinAt (fun τ => linearSource hH u (φ τ).toNNReal)
      ((-(1 / 2 * deriv2GBarX hH u (φ t).toNNReal) * hBarX u₀ H u (φ t).toNNReal -
        linearCoeff hH u (φ t).toNNReal * derivHBarX hH u (φ t).toNNReal) * φ') s t :=
  (hasDerivWithinAt_linearSource_real hH u (φ t) hφt).comp t hφ hφs

end XCoef

end Christodoulou.Bondi
