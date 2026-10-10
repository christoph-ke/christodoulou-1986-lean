module
public import Christodoulou.Frozen.Bondi.MemXBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem MemXBall.isSlice {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : Christodoulou.Bondi.MemXBall u₀ x H := by assumption) {u : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) : IsSlice (H.curry u) := by
  obtain ⟨h1, -, h3⟩ := hH
  refine ⟨h1 u hu, ?_⟩
  refine IsBigO.of_bound x ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hb := h3 u hu (Real.toNNReal s)
  rw [Real.coe_toNNReal s hs.le] at hb
  have hpos : (0 : ℝ) < (1 + s) ^ 3 := by positivity
  have hH : |H (u, Real.toNNReal s)| ≤ x * ((1 + s) ^ 3)⁻¹ := by
    rw [le_mul_inv_iff₀ hpos]
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + s) 4)
      (abs_nonneg (derivWithin (fun t : ℝ => H (u, Real.toNNReal t)) (Ici 0) s)),
      abs_nonneg (H (u, Real.toNNReal s))]
  have hx : 0 ≤ x := le_trans (by positivity) hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zpow_pos hs _)]
  calc |(H.curry u) (Real.toNNReal s)| = |H (u, Real.toNNReal s)| := rfl
    _ ≤ x * ((1 + s) ^ 3)⁻¹ := hH
    _ ≤ x * s ^ (-3 : ℤ) := by
        gcongr
        rw [zpow_neg, zpow_ofNat]
        exact inv_anti₀ (pow_pos hs 3) (pow_le_pow_left₀ hs.le (by linarith) 3)

end Christodoulou.Bondi.Provider
