module
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Christodoulou.Frozen.Bondi.GBarLeG
public import Christodoulou.Frozen.Bondi.GLeOne
public import Christodoulou.Bondi.GBarBasic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Radial derivative of the averaged metric in the X-ball

Derivative comparison for weighted mean differences gives the radial bound, including the
one-sided derivative at the centre.
-/

public section

open Set Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
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

private lemma deriv_bound_three (c s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => c * t ^ 3 / (3 * (1 + t) ^ 3))
      (c * s ^ 2 / (1 + s) ^ 4) s := by
  have hn : 1 + s ≠ 0 := by positivity
  convert (((hasDerivAt_id s).pow 3).const_mul c).div
    ((((hasDerivAt_id s).const_add 1).pow 3).const_mul 3) (by dsimp; positivity) using 1
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

private lemma slice_mul_gap_le {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀)
    (r : ℝ≥0) :
    (r : ℝ) * (g (H.curry u) (hH.isSlice u hu) r - gBar (H.curry u) (hH.isSlice u hu) r)
      ≤ π * x ^ 2 * (r : ℝ) ^ 3 / (3 * (1 + (r : ℝ)) ^ 3) := by
  let h := H.curry u
  let hh := hH.isSlice u hu
  let A := fun s : ℝ => h (Real.toNNReal s) - mean h (Real.toNNReal s)
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t : ℝ => t * (g h hh (Real.toNNReal t)
        - gBar h hh (Real.toNNReal t)))
        (4 * π * g h hh (Real.toNNReal s) * A s ^ 2) s := by
    have hg := hasDerivAt_g h hh (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
    rw [Real.coe_toNNReal s hs.le] at hg
    convert hasDerivAt_mul_sub_mean (gMap h hh) hs hg using 1
    · rfl
    · dsimp [A]
      field_simp
  have hb (s : ℝ) (hs : 0 < s) :
      4 * π * g h hh (Real.toNNReal s) * A s ^ 2 ≤ π * x ^ 2 * s ^ 2 / (1 + s) ^ 4 := by
    have ha := slice_abs_sub_mean_le hH u hu (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.le] at ha
    change |A s| ≤ x * s / (2 * (1 + s) ^ 2) at ha
    have ha2 : A s ^ 2 ≤ (x * s / (2 * (1 + s) ^ 2)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A s)) ha 2
    calc
      4 * π * g h hh (Real.toNNReal s) * A s ^ 2
          ≤ 4 * π * A s ^ 2 := by
            have := mul_le_mul_of_nonneg_right (g_le_one h hh (Real.toNNReal s))
              (show 0 ≤ 4 * π * A s ^ 2 by positivity)
            nlinarith only [this]
      _ ≤ 4 * π * (x * s / (2 * (1 + s) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ = π * x ^ 2 * s ^ 2 / (1 + s) ^ 4 := by
        field_simp
        ring
  have hB : ContinuousOn (fun s : ℝ => π * x ^ 2 * s ^ 3 / (3 * (1 + s) ^ 3))
      (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow _))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hc := compare_of_deriv (continuous_mul_sub_mean (gMap h hh)).continuousOn hB hd
    (fun s hs => deriv_bound_three (π * x ^ 2) s hs.le) (by simp) hb r.coe_nonneg
  simpa only [Real.toNNReal_coe, gMap_apply, gBar] using hc

/-- The radial derivative of the averaged metric is nonnegative, including at the centre. -/
theorem XBall.derivGBarX_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : 0 ≤ derivGBarX hH u r := by
  unfold derivGBarX
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sub_nonneg.mpr (gBar_le_g _ _ r)) r.coe_nonneg

/-- The X norm controls the radial derivative with the sharp rational majorant used here. -/
theorem XBall.derivGBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    derivGBarX hH u r ≤ π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [derivGBarX]
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hb := slice_mul_gap_le hH (min u u₀) (min_le_right u u₀) r
  change (r : ℝ) * (gX hH u r - gBarX hH u r)
    ≤ π * x ^ 2 * (r : ℝ) ^ 3 / (3 * (1 + (r : ℝ)) ^ 3) at hb
  rw [derivGBarX, ite_eq_right hr]
  apply (div_le_iff₀ hrp).mpr
  have hb' := (le_div_iff₀ (by positivity)).mp hb
  apply (mul_le_mul_iff_right₀ hrp).mp
  apply (mul_le_mul_iff_left₀ (show 0 < 3 * (1 + (r : ℝ)) ^ 3 by positivity)).mp
  calc
    _ ≤ π * x ^ 2 * (r : ℝ) ^ 3 := hb'
    _ = _ := by field_simp

private lemma hasDerivAt_gBarX_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => gBarX hH u (Real.toNNReal s)) (derivGBarX hH u r)
      (r : ℝ) := by
  rw [derivGBarX, ite_eq_right (ne_of_gt hr)]
  exact hasDerivAt_gBar _ _ r hr

/-- The averaged metric has the stated one-sided radial derivative at every radius. -/
theorem XBall.hasDerivWithinAt_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => gBarX hH u (Real.toNNReal s)) (derivGBarX hH u r)
      (Ici 0) (r : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [derivGBarX, ite_true, NNReal.coe_zero]
    let f := fun s : ℝ => gBarX hH u (Real.toNNReal s)
    have hd (s : ℝ) (hs : 0 < s) :
        HasDerivAt f (derivGBarX hH u (Real.toNNReal s)) s := by
      have := hasDerivAt_gBarX_pos hH u (Real.toNNReal s) (Real.toNNReal_pos.mpr hs)
      rwa [Real.coe_toNNReal s hs.le] at this
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    · exact ((continuous_gBar _ _).comp continuous_real_toNNReal).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · have hc : ContinuousAt (fun s : ℝ => π / 3 * x ^ 2 * s / (1 + s) ^ 3) 0 := by
        fun_prop (disch := norm_num)
      have ht : Tendsto (fun s : ℝ => π / 3 * x ^ 2 * s / (1 + s) ^ 3)
          (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero, zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [(hd s hs).deriv]
        exact XBall.derivGBarX_nonneg hH u _
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [(hd s hs).deriv]
        have := XBall.derivGBarX_le hH u (Real.toNNReal s)
        rwa [Real.coe_toNNReal s hs.le] at this
  · exact (hasDerivAt_gBarX_pos hH u r (pos_iff_ne_zero.mpr hr)).hasDerivWithinAt

end Christodoulou.Bondi
