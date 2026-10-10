module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.HasDerivAtMass
public import Christodoulou.Frozen.Bondi.MassZero
public import Christodoulou.Frozen.Bondi.GBarLeG
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.IsSlice
public import Christodoulou.Bondi.GBarBasic
public import Christodoulou.Frozen.Radial.Mean
public import Christodoulou.Frozen.Radial.HasDerivAtMean
public import Christodoulou.Frozen.Radial.ContinuousMean
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Radial.MeanBasic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Direct decay estimate for the Bondi mass

A weighted bound on the radial derivative controls the difference from the radial mean.
Comparing the mass derivative with an explicit primitive then bounds the Bondi mass.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.XBD

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

private theorem coefficient_nonneg {h : C(ℝ≥0, ℝ)} {C c : ℝ} (hc : 0 < c)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ)) :
    0 ≤ C := by
  have hz := (abs_nonneg _).trans (hd 0)
  simp only [NNReal.coe_zero, add_zero] at hz
  exact nonneg_of_mul_nonneg_left hz (zpow_pos hc _)

/-- Smooth envelope obtained by comparing the derivatives of `r * (h - mean h)`. -/
private theorem difference_bound (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) {C c : ℝ} (hc : 0 < c)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ))
    (r : ℝ≥0) :
    |h r - mean h r| ≤ C * (r : ℝ) / (2 * c ^ 2 * (c + (r : ℝ)) ^ 2) := by
  have hC := coefficient_nonneg hc hd
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [mean_zero, sub_self, abs_zero, NNReal.coe_zero, mul_zero, zero_div, le_refl]
  have rp : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  let D := fun s : ℝ => derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) s
  have hd' (s : ℝ) (hs : 0 < s) : HasDerivAt (fun z : ℝ => h z.toNNReal) (D s) s := by
    exact (hh.1.differentiableOn one_ne_zero s hs.le).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hs)
  have hder (s : ℝ) (hs : 0 < s) : |s * D s| ≤ C * s / (c * (c + s) ^ 3) := by
    have hw := hd (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.le] at hw
    change |D s| ≤ C * (c + s) ^ (-4 : ℤ) at hw
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv] at hw
    have hw' : |D s| ≤ C / (c * (c + s) ^ 3) := by
      apply hw.trans
      apply div_le_div_of_nonneg_left hC (by positivity)
      nlinarith [pow_nonneg (by positivity : 0 ≤ c + s) 3]
    rw [abs_mul, abs_of_pos hs]
    convert mul_le_mul_of_nonneg_left hw' hs.le using 1
    ring
  have hB : ContinuousOn (fun s : ℝ => C * s ^ 2 / (2 * c ^ 2 * (c + s) ^ 2)) (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow _))
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hb := abs_compare_of_deriv (continuous_mul_sub_mean h).continuousOn hB
    (fun s hs => hasDerivAt_mul_sub_mean h hs (hd' s hs))
    (fun s hs => hasDerivAt_bound_two c C s hc hs.le) (by simp) hder r.coe_nonneg
  simp only [Real.toNNReal_coe, abs_mul, abs_of_nonneg r.coe_nonneg] at hb
  have heq : C * (r : ℝ) ^ 2 / (2 * c ^ 2 * (c + (r : ℝ)) ^ 2) =
      (r : ℝ) * (C * (r : ℝ) / (2 * c ^ 2 * (c + (r : ℝ)) ^ 2)) := by ring
  rw [heq] at hb
  exact (mul_le_mul_iff_right₀ rp).mp hb

private theorem mass_bound_derivative (C c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    HasDerivAt (fun t : ℝ => (π / 6 * C ^ 2 / c ^ 5) * t ^ 3 / (c + t) ^ 3)
      (2 * π * (C * s / (2 * c ^ 2 * (c + s) ^ 2)) ^ 2) s := by
  have hn : c + s ≠ 0 := by positivity
  convert (((hasDerivAt_id s).pow 3).const_mul (π / 6 * C ^ 2 / c ^ 5)).div
    (((hasDerivAt_id s).const_add c).pow 3) (by dsimp; positivity) using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- Comparison with an explicit primitive gives a stronger finite-radius mass bound. -/
private theorem mass_bound (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) {C c : ℝ} (hc : 0 < c)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ))
    (r : ℝ≥0) : mass h hh r ≤ π / 6 * C ^ 2 / c ^ 5 := by
  have hB : ContinuousOn
      (fun t : ℝ => (π / 6 * C ^ 2 / c ^ 5) * t ^ 3 / (c + t) ^ 3) (Ici 0) := by
    exact (continuousOn_const.mul (continuousOn_id.pow _)).div
      ((continuousOn_const.add continuousOn_id).pow _)
      (fun s hs => by have : 0 ≤ s := hs; positivity)
  have hd' (s : ℝ) (hs : 0 < s) := hasDerivAt_mass h hh s.toNNReal (Real.toNNReal_pos.mpr hs)
  have hmder (s : ℝ) (hs : 0 < s) :
      2 * π * (gBar h hh s.toNNReal / g h hh s.toNNReal) *
        (h s.toNNReal - mean h s.toNNReal) ^ 2 ≤
      2 * π * (C * s / (2 * c ^ 2 * (c + s) ^ 2)) ^ 2 := by
    have hg : gBar h hh s.toNNReal / g h hh s.toNNReal ≤ 1 :=
      (div_le_one (g_pos h hh _)).mpr (gBar_le_g h hh _)
    have hdiff := difference_bound h hh hc hd s.toNNReal
    rw [Real.coe_toNNReal s hs.le] at hdiff
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    rw [sq_abs] at hsq
    calc
      _ ≤ 2 * π * (1 : ℝ) * (h s.toNNReal - mean h s.toNNReal) ^ 2 := by
        gcongr
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * π)
  have hb := compare_of_deriv
    (f := fun s : ℝ => mass h hh s.toNNReal)
    (f' := fun s : ℝ => 2 * π * (gBar h hh s.toNNReal / g h hh s.toNNReal) *
      (h s.toNNReal - mean h s.toNNReal) ^ 2)
    ((continuous_mass h hh).comp continuous_real_toNNReal).continuousOn hB
    (fun s hs => by simpa only [Real.coe_toNNReal s hs.le] using hd' s hs)
    (fun s hs => mass_bound_derivative C c s hc hs.le)
    (by simp [mass_zero]) hmder r.coe_nonneg
  simp only [Real.toNNReal_coe] at hb
  apply hb.trans
  apply (div_le_iff₀ (by positivity : 0 < (c + (r : ℝ)) ^ 3)).mpr
  gcongr
  exact le_add_of_nonneg_left hc.le

/-- The direct decay estimate for the Bondi mass under a weighted radial derivative bound. -/
theorem bondiMass_le_of_deriv_bound (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) {C c : ℝ} (hc : 0 < c)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ)) :
    bondiMass h hh ≤ 2 * π / 3 * C ^ 2 * c ^ (-5 : ℤ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨r, rfl⟩
  apply (mass_bound h hh hc hd r).trans
  rw [zpow_neg, zpow_ofNat]
  have hn : 0 ≤ C ^ 2 / c ^ 5 := by positivity
  calc
    _ = (π / 6) * (C ^ 2 / c ^ 5) := by ring
    _ ≤ (2 * π / 3) * (C ^ 2 / c ^ 5) :=
      mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hn
    _ = _ := by ring

end Christodoulou.Bondi.XBD
