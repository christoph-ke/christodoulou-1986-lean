module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Radial.Mean
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.GMap
public import Christodoulou.Frozen.Bondi.GBar
public import Christodoulou.Bondi.ScalingBasic
import Christodoulou.Radial.MeanBasic
import Mathlib.MeasureTheory.Function.JacobianOneDim



public section

open Set Real Filter Topology MeasureTheory
open scoped NNReal Pointwise

namespace Christodoulou.Bondi
open Christodoulou.Radial

namespace XSC

/-- The radial mean commutes with radial scaling, including at the centre. -/
theorem mean_radialScale (b : ℝ≥0) (h : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    mean (radialScale b h) r = mean h (b * r) := by
  rw [mean_eq_integral_unitInterval, mean_eq_integral_unitInterval]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [XSB.lift_radialScale, NNReal.coe_mul, mul_assoc]

/-- Positive scaling maps an open radial tail onto the scaled open tail. -/
theorem image_scale_Ioi (b : ℝ≥0) (hb : 0 < b) (r : ℝ) :
    (fun s : ℝ => (b : ℝ) * s) '' Ioi r = Ioi ((b : ℝ) * r) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mul_lt_mul_of_pos_left (mem_Ioi.mp hs) hb
  · intro ht
    refine ⟨t / b, ?_, by field_simp [show (b : ℝ) ≠ 0 from ne_of_gt hb]⟩
    exact (lt_div_iff₀ (show (0 : ℝ) < b from hb)).mpr (by simpa [mul_comm] using ht)

/-- The metric function `g` commutes with positive radial scaling (p. 345, the laws before
(4.14)). -/
theorem g_radialScale (b : ℝ≥0) (hb : 0 < b) (h : C(ℝ≥0, ℝ))
    (hh : IsSlice h) (hs : IsSlice (radialScale b h)) (r : ℝ≥0) :
    g (radialScale b h) hs r = g h hh (b * r) := by
  unfold g
  congr 2
  let F : ℝ → ℝ := fun s => (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 / s
  have hi := integral_image_eq_integral_abs_deriv_smul (s := Ioi (r : ℝ))
    (f := fun s : ℝ => (b : ℝ) * s) (f' := fun _ => (b : ℝ)) measurableSet_Ioi
    (fun s _ => by
      convert ((hasDerivAt_id s).const_mul (b : ℝ)).hasDerivWithinAt using 1 <;> simp)
    (mul_right_injective₀ (show (b : ℝ) ≠ 0 from ne_of_gt hb)).injOn F
  rw [image_scale_Ioi b hb] at hi
  change _ = ∫ s in Ioi ((b : ℝ) * (r : ℝ)), F s
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [XSB.lift_radialScale, mean_radialScale,
    Real.toNNReal_mul b.coe_nonneg, Real.toNNReal_coe,
    abs_of_pos (show (0 : ℝ) < b from hb), smul_eq_mul, F]
  field_simp [show (b : ℝ) ≠ 0 from ne_of_gt hb]

/-- The continuous metric map commutes with positive radial scaling. -/
theorem gMap_radialScale (b : ℝ≥0) (hb : 0 < b) (h : C(ℝ≥0, ℝ))
    (hh : IsSlice h) (hs : IsSlice (radialScale b h)) :
    gMap (radialScale b h) hs = radialScale b (gMap h hh) := by
  ext r
  exact g_radialScale b hb h hh hs r

/-- The metric mean `ḡ` commutes with positive radial scaling (p. 345, the laws before (4.14)). -/
theorem gBar_radialScale (b : ℝ≥0) (hb : 0 < b) (h : C(ℝ≥0, ℝ))
    (hh : IsSlice h) (hs : IsSlice (radialScale b h)) (r : ℝ≥0) :
    gBar (radialScale b h) hs r = gBar h hh (b * r) := by
  unfold gBar
  rw [gMap_radialScale b hb h hh hs, mean_radialScale]

/-- The time derivative of a scaled field acquires the scale factor. -/
theorem deriv_fieldScale_time (b : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) :
    deriv (fun v : ℝ => fieldScale b H (Real.toNNReal v, r)) u =
      (b : ℝ) * deriv (fun v : ℝ => H (Real.toNNReal v, b * r)) (b * u) := by
  have heq : (fun v : ℝ => fieldScale b H (Real.toNNReal v, r)) =
      (fun v : ℝ => H (Real.toNNReal ((b : ℝ) * v), b * r)) := by
    funext v
    simp [Real.toNNReal_mul b.coe_nonneg]
  rw [heq]
  exact deriv_comp_mul_left (b : ℝ) (fun v => H (Real.toNNReal v, b * r)) u

/-- The radial derivative of a scaled field acquires the scale factor. -/
theorem deriv_fieldScale_radial (b : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) :
    deriv (fun s : ℝ => fieldScale b H (u, Real.toNNReal s)) r =
      (b : ℝ) * deriv (fun s : ℝ => H (b * u, Real.toNNReal s)) (b * r) :=
  XSB.deriv_radialScale b (H.curry (b * u)) r

/-- Positive radial scaling preserves cubic decay with an explicit constant. -/
theorem weighted_scale_bound (b : ℝ≥0) (hb : 0 < b) (r : ℝ≥0) :
    (1 + (b * r : ℝ≥0) : ℝ) ^ (-3 : ℤ) ≤
      (1 + (b : ℝ)⁻¹) ^ 3 * (1 + (r : ℝ)) ^ (-3 : ℤ) := by
  have hb' : (0 : ℝ) < b := hb
  have hr : 0 ≤ (r : ℝ) := r.coe_nonneg
  have hbr : 0 < 1 + (b : ℝ) * r := by positivity
  have hr1 : 0 < 1 + (r : ℝ) := by positivity
  have hi : (1 + (b : ℝ) * r)⁻¹ ≤ (1 + (b : ℝ)⁻¹) / (1 + (r : ℝ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hbr hr1]
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (b : ℝ)) hr]
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hbr.le) hi 3
  simpa only [NNReal.coe_mul, zpow_neg, zpow_ofNat, inv_pow, div_pow,
    div_eq_mul_inv, mul_pow] using hp

/-- Positive field scaling transports a classical solution to the divided strip. -/
theorem isClassicalSolution_fieldScale_strip (b : ℝ≥0) (hb : 0 < b) (u₀ : ℝ≥0)
    (H : C(ℝ≥0 × ℝ≥0, ℝ)) (hH : IsClassicalSolution u₀ H) :
    IsClassicalSolution (u₀ / b) (fieldScale b H) := by
  have hb' : (0 : ℝ) < b := hb
  refine ⟨?_, ?_, ?_⟩
  · have hc : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((b : ℝ) * p.1, (b : ℝ) * p.2)) :=
      (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)
    have hm : MapsTo (fun p : ℝ × ℝ => ((b : ℝ) * p.1, (b : ℝ) * p.2))
        (Icc 0 (↑(u₀ / b) : ℝ) ×ˢ Ici 0) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
      intro p hp
      refine ⟨⟨mul_nonneg hb'.le hp.1.1, ?_⟩, mul_nonneg hb'.le hp.2⟩
      have hh := mul_le_mul_of_nonneg_left hp.1.2 hb'.le
      simpa only [NNReal.coe_div, mul_div_cancel₀ _ (ne_of_gt hb'), mul_comm (b : ℝ)] using hh
    have heq : (fun p : ℝ × ℝ => fieldScale b H (Real.toNNReal p.1, Real.toNNReal p.2)) =
        (fun p : ℝ × ℝ => H (Real.toNNReal p.1, Real.toNNReal p.2)) ∘
          (fun p : ℝ × ℝ => ((b : ℝ) * p.1, (b : ℝ) * p.2)) := by
      funext p
      simp [Real.toNNReal_mul b.coe_nonneg]
    rw [heq]
    exact hH.1.comp hc.contDiffOn hm
  · obtain ⟨C, hC⟩ := hH.2.1
    have hC0 : 0 ≤ C := by
      have ht := hC 0 (show 0 ≤ u₀ from bot_le) 0
      simpa using (abs_nonneg (H (0,0))).trans ht
    refine ⟨C * (1 + (b : ℝ)⁻¹) ^ 3, fun u hu r => ?_⟩
    have hu' : b * u ≤ u₀ := by
      simpa [mul_comm] using (le_div_iff₀ hb).mp hu
    calc
      |fieldScale b H (u,r)| ≤ C * (1 + ((b * r : ℝ≥0) : ℝ)) ^ (-3 : ℤ) := hC (b*u) hu' (b*r)
      _ ≤ C * ((1 + (b : ℝ)⁻¹) ^ 3 * (1 + (r : ℝ)) ^ (-3 : ℤ)) :=
        mul_le_mul_of_nonneg_left (weighted_scale_bound b hb r) hC0
      _ = _ := (mul_assoc _ _ _).symm
  · intro u hu hu₀ hs r hr
    have hu' : b * u < u₀ := by
      simpa [mul_comm] using (lt_div_iff₀ hb).mp hu₀
    have hs0 := hH.isSlice (b * u) hu'.le
    have hsr := XSB.isSlice_radialScale b hb (H.curry (b * u)) hs0
    have he := hH.2.2 (b * u) (mul_pos hb hu) hu' hs0 (b * r) (mul_pos hb hr)
    have hg := g_radialScale b hb (H.curry (b * u)) hs0 hsr r
    have hgb := gBar_radialScale b hb (H.curry (b * u)) hs0 hsr r
    rw [deriv_fieldScale_time, deriv_fieldScale_radial]
    simp only [XSB.fieldScale_curry] at hs ⊢
    rw [hg, hgb, mean_radialScale, XSB.fieldScale_apply]
    simp only [NNReal.coe_mul] at he ⊢
    calc
      _ = (b : ℝ) * (deriv (fun v : ℝ => H (Real.toNNReal v, b * r)) (↑b * ↑u) -
          1 / 2 * gBar (H.curry (b*u)) hs0 (b*r) *
            deriv (fun s : ℝ => H (b*u, Real.toNNReal s)) (↑b * ↑r)) := by ring
      _ = _ := by rw [he]; field_simp [ne_of_gt hb']

/-- Covariance (4.13): a solution on `[0, b * T]` scales to a solution on `[0, T]`. -/
theorem isClassicalSolution_fieldScale {b : ℝ≥0} (hb : 0 < b) {T : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution (b * T) H) :
    IsClassicalSolution T (fieldScale b H) := by
  simpa only [mul_div_cancel_left₀ T (ne_of_gt hb)] using
    isClassicalSolution_fieldScale_strip b hb (b * T) H hH

end XSC

end Christodoulou.Bondi
