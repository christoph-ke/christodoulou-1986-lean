module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.ContDiff.Operations



public section

open Set Real Filter Topology Asymptotics
open scoped NNReal Pointwise

namespace Christodoulou.Bondi.XSB

@[simp] theorem radialScale_apply (b : ℝ≥0) (h : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    radialScale b h r = h (b * r) := rfl

@[simp] theorem fieldScale_apply (b : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) :
    fieldScale b H (u,r) = H (b * u, b * r) := rfl

theorem fieldScale_curry (b : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u : ℝ≥0) :
    (fieldScale b H).curry u = radialScale b (H.curry (b * u)) := by
  ext r
  rfl

theorem lift_radialScale (b : ℝ≥0) (h : C(ℝ≥0, ℝ)) (s : ℝ) :
    radialScale b h (Real.toNNReal s) = h (Real.toNNReal ((b : ℝ) * s)) := by
  simp [Real.toNNReal_mul b.coe_nonneg]

theorem deriv_radialScale (b : ℝ≥0) (h : C(ℝ≥0, ℝ)) (s : ℝ) :
    deriv (fun t : ℝ => radialScale b h (Real.toNNReal t)) s =
      (b : ℝ) * deriv (fun t : ℝ => h (Real.toNNReal t)) ((b : ℝ) * s) := by
  simp_rw [lift_radialScale]
  exact deriv_comp_mul_left (b : ℝ) (fun t => h (Real.toNNReal t)) s

theorem derivWithin_radialScale (b : ℝ≥0) (hb : 0 < b) (h : C(ℝ≥0, ℝ)) (s : ℝ) :
    derivWithin (fun t : ℝ => radialScale b h (Real.toNNReal t)) (Ici 0) s =
      (b : ℝ) * derivWithin (fun t : ℝ => h (Real.toNNReal t)) (Ici 0) ((b : ℝ) * s) := by
  simp_rw [lift_radialScale]
  have hset : (b : ℝ) • Ici (0 : ℝ) = Ici (0 : ℝ) := by
    change (fun x : ℝ => (b : ℝ) * x) '' Ici 0 = Ici 0
    simpa only [mul_zero] using image_mul_left_Ici (show (0 : ℝ) < b from hb) 0
  simpa only [hset, smul_eq_mul] using
    derivWithin_comp_mul_left (b : ℝ) (fun t => h (Real.toNNReal t)) (Ici 0) s

theorem bigO_scale (b : ℝ≥0) (hb : 0 < b) (f : ℝ → ℝ) (n : ℤ)
    (hf : f =O[atTop] (fun s => s ^ n)) :
    (fun s => f ((b : ℝ) * s)) =O[atTop] (fun s => s ^ n) := by
  have ht : Tendsto (fun s : ℝ => (b : ℝ) * s) atTop atTop := by
    simpa [mul_comm] using tendsto_id.atTop_mul_const (show (0 : ℝ) < b from hb)
  have hh := (hf.comp_tendsto ht)
  simp only [Function.comp_def, mul_zpow] at hh
  exact hh.trans ((isBigO_refl (fun s : ℝ => s ^ n) atTop).const_mul_left ((b : ℝ) ^ n))

theorem isSlice_radialScale (b : ℝ≥0) (hb : 0 < b) (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IsSlice (radialScale b h) := by
  constructor
  · simp_rw [lift_radialScale]
    exact hh.1.comp ((contDiff_const.mul contDiff_id).contDiffOn)
      (fun s hs => mul_nonneg b.coe_nonneg hs)
  · simp_rw [lift_radialScale]
    exact bigO_scale b hb _ _ hh.2

theorem weighted_summand_scale_within (a : ℝ≥0) (ha : 0 < a) (data : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |radialScale a data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => radialScale a data (Real.toNNReal s)) (Ici 0) r| =
    (1 + ((a*r : ℝ≥0) : ℝ) / (a : ℝ)) ^ 3 * |data (a*r)| +
      (1 + ((a*r : ℝ≥0) : ℝ) / (a : ℝ)) ^ 4 *
        |(a : ℝ) * derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) (a*r)| := by
  rw [derivWithin_radialScale a ha]
  simp only [radialScale_apply, NNReal.coe_mul,
    mul_div_cancel_left₀ (r : ℝ) (show (a : ℝ) ≠ 0 from ne_of_gt ha)]

theorem weighted_summand_rescale_radius_within (a : ℝ≥0) (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    (1 + (r : ℝ) / (a : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ) / (a : ℝ)) ^ 4 *
        |(a : ℝ) * derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| =
    (1 + (r/a : ℝ≥0) : ℝ) ^ 3 * |radialScale a data (r/a)| +
      (1 + (r/a : ℝ≥0) : ℝ) ^ 4 *
        |derivWithin (fun s : ℝ => radialScale a data (Real.toNNReal s)) (Ici 0) (r/a)| := by
  simpa only [mul_div_cancel₀ r (ne_of_gt ha), NNReal.coe_div,
    mul_div_cancel₀ (r : ℝ) (show (a : ℝ) ≠ 0 from ne_of_gt ha)] using
    (weighted_summand_scale_within a ha data (r/a)).symm

end Christodoulou.Bondi.XSB
