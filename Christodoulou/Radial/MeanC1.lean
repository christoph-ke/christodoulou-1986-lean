module
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Mathlib.Topology.EMetricSpace.Lipschitz



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Radial

/-- Centre estimate: a Lipschitz bound for the real lift of `f` on `[0, r]` gives
`|f(s) − f̄(s)| ≤ K s` for `s ∈ [0, r]`. -/
theorem abs_sub_mean_le (f : C(ℝ≥0, ℝ)) {K : ℝ≥0} {r : ℝ}
    (hK : LipschitzOnWith K (fun s : ℝ => f (Real.toNNReal s)) (Icc 0 r)) {s : ℝ}
    (hs : s ∈ Icc 0 r) :
    |f (Real.toNNReal s) - mean f (Real.toNNReal s)| ≤ K * s := by
  rcases hs.1.eq_or_lt with h0 | hpos
  · subst h0
    simp [mean_zero]
  set H : ℝ → ℝ := fun t => f (Real.toNNReal t) with hH
  have hHc : Continuous H := f.continuous.comp continuous_real_toNNReal
  have hmean : mean f (Real.toNNReal s) = s⁻¹ * ∫ t in (0 : ℝ)..s, H t := by
    have := mean_eq_integral (f := f) (r := Real.toNNReal s) (Real.toNNReal_pos.2 hpos)
    rwa [Real.coe_toNNReal s hpos.le] at this
  have hsub : f (Real.toNNReal s) - mean f (Real.toNNReal s)
      = s⁻¹ * ∫ t in (0 : ℝ)..s, (H s - H t) := by
    rw [hmean, intervalIntegral.integral_sub intervalIntegrable_const
      (hHc.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hH]
    field_simp
  rw [hsub, abs_mul, abs_inv, abs_of_pos hpos]
  have hb : ‖∫ t in (0 : ℝ)..s, (H s - H t)‖ ≤ (K * s) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hpos.le] at ht
    have hd := hK.dist_le_mul s hs t ⟨ht.1.le, ht.2.trans hs.2⟩
    have hst : |s - t| = s - t := abs_of_nonneg (by linarith [ht.2])
    rw [Real.dist_eq, Real.dist_eq, hst] at hd
    rw [Real.norm_eq_abs]
    calc |H s - H t| ≤ K * (s - t) := hd
      _ ≤ K * s := by gcongr; linarith [ht.1]
  rw [sub_zero, abs_of_pos hpos, Real.norm_eq_abs] at hb
  calc s⁻¹ * |∫ t in (0 : ℝ)..s, (H s - H t)| ≤ s⁻¹ * (K * s * s) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hpos.le)
    _ = K * s := by field_simp

end Christodoulou.Radial
