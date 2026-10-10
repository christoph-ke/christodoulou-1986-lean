module
public import Christodoulou.Frozen.Bondi.CharField
public import Mathlib.Analysis.ODE.PicardLindelof
import Christodoulou.Frozen.Bondi.LipschitzWithGBarX
import Christodoulou.Frozen.Bondi.ContinuousGBarX
import Christodoulou.Frozen.Bondi.GBarXPos
import Christodoulou.Frozen.Bondi.GBarXLeOne

/-!
# Provider for `Christodoulou.Bondi.isPicardLindelof_charField`

Implementation module for the frozen anchor
`Christodoulou/Frozen/Bondi/IsPicardLindelofCharField.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: the four fields of Mathlib's `IsPicardLindelof`: spatial Lipschitz constant
`½ · (π/6) x² = (π/12) x²` (sealed `lipschitzWith_gBarX`), continuity in time (sealed
`continuous_gBarX`), speed bound `1/2` (sealed `gBarX_pos`, `gBarX_le_one`), and
`(1/2) · max (u₀ − t₀) t₀ ≤ u₀/2 = (ρ + u₀/2) − ρ`.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem isPicardLindelof_charField {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {t₀ : Icc (0 : ℝ) u₀} {z₀ : ℝ} {ρ : ℝ≥0} :
    IsPicardLindelof (charField hH) t₀ z₀ (ρ + u₀ / 2) ρ (1 / 2)
      (Real.toNNReal (π / 12 * x ^ 2)) := by
  refine ⟨fun t _ => ?_, fun z _ => ?_, fun t _ z _ => ?_, ?_⟩
  · -- spatial Lipschitz constant ½ · π/6 x² = π/12 x²
    have hL := lipschitzWith_gBarX hH (Real.toNNReal t)
    have h2 : LipschitzWith (Real.toNNReal (π / 12 * x ^ 2)) (charField hH t) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have := hL.dist_le_mul a b
      simp only [charField, Real.dist_eq] at this ⊢
      rw [← mul_sub, abs_mul, show |(-(1 / 2 : ℝ))| = 1 / 2 by norm_num]
      have hc : ((Real.toNNReal (π / 12 * x ^ 2) : ℝ≥0) : ℝ)
          = 1 / 2 * ((Real.toNNReal (π / 6 * x ^ 2) : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]; ring
      rw [hc, mul_assoc]
      gcongr
    exact h2.lipschitzOnWith
  · -- continuity in time
    have hc := continuous_gBarX hH
    exact (continuous_const.mul (hc.comp ((continuous_real_toNNReal).prodMk
      continuous_const))).continuousOn
  · -- speed bound ½
    have h0 := gBarX_pos hH (Real.toNNReal t) (Real.toNNReal z)
    have h1 := gBarX_le_one hH (Real.toNNReal t) (Real.toNNReal z)
    simp only [charField, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [abs_mul, abs_of_pos h0]
    norm_num
    linarith
  · -- L · max (u₀ − t₀) (t₀ − 0) ≤ a − ρ
    obtain ⟨t, ht0, ht1⟩ := t₀
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_add]
    have : max ((u₀ : ℝ) - t) (t - 0) ≤ u₀ := max_le (by linarith) (by linarith)
    nlinarith

end Christodoulou.Bondi.Provider
