module
public import Christodoulou.Frozen.Radial.Mean
public import Christodoulou.Radial.MeanBasic
import Mathlib.Topology.Instances.NNReal.Lemmas



public section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- Graph step `P.344.center.continuity#continuous-at-pos`: `f̄` is continuous at `r > 0`. -/
theorem continuousAt_mean_of_pos (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) (hr : 0 < r) :
    ContinuousAt (mean f) r := by
  have hr' : (0 : ℝ) < r := hr
  have hreal : ContinuousAt (fun x : ℝ => x⁻¹ * ∫ s in (0 : ℝ)..x, lift f s) (r : ℝ) :=
    (continuousAt_inv₀ hr'.ne').mul (hasDerivAt_integral_lift f r).continuousAt
  refine (hreal.comp NNReal.continuous_coe.continuousAt).congr ?_
  filter_upwards [lt_mem_nhds hr] with s hs
  exact (mean_eq_integral f s hs).symm

/-- Graph step `P.344.center.continuity#centre-estimate`: if `|f − f(0)| ≤ M` on `[0, r]` then
`|f̄(r) − f(0)| ≤ M`. -/
theorem abs_mean_sub_le (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) (hr : 0 < r) (M : ℝ)
    (hM : ∀ s : ℝ, s ∈ Icc 0 (r : ℝ) → |lift f s - f 0| ≤ M) :
    |mean f r - f 0| ≤ M := by
  have hrpos : (0 : ℝ) < r := hr
  have hest : ‖∫ s in (0 : ℝ)..(r : ℝ), (lift f s - f 0)‖ ≤ M * |(r : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [uIoc_of_le hrpos.le] at hs
      exact hM s ⟨hs.1.le, hs.2⟩
  have hint : ∫ s in (0 : ℝ)..(r : ℝ), (lift f s - f 0) =
      (∫ s in (0 : ℝ)..(r : ℝ), lift f s) - r * f 0 := by
    rw [intervalIntegral.integral_sub ((continuous_lift f).intervalIntegrable _ _)
      intervalIntegrable_const]
    simp
  have hmean : mean f r - f 0 = (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), (lift f s - f 0) := by
    rw [hint, mean_eq_integral f r hr, mul_sub, inv_mul_cancel_left₀ hrpos.ne']
    rfl
  rw [hmean, abs_mul, abs_inv, abs_of_pos hrpos]
  calc (r : ℝ)⁻¹ * |∫ s in (0 : ℝ)..(r : ℝ), (lift f s - f 0)|
      ≤ (r : ℝ)⁻¹ * (M * |(r : ℝ) - 0|) := by gcongr; exact hest
    _ = M := by rw [sub_zero, abs_of_pos hrpos]; field_simp

/-- Graph step `P.344.center.continuity#continuous-at-zero`: `f̄` is continuous at the centre. -/
theorem continuousAt_mean_zero (f : C(ℝ≥0, ℝ)) : ContinuousAt (mean f) 0 := by
  rw [ContinuousAt, mean_zero, Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := Metric.continuousAt_iff.1 (continuous_lift f).continuousAt (ε / 2)
    (half_pos hε)
  refine ⟨δ, hδ, fun {r} hr => ?_⟩
  rcases eq_or_ne r 0 with rfl | hr0
  · simpa [mean_zero] using hε
  have hrδ : (r : ℝ) < δ := by simpa [NNReal.dist_eq] using hr
  have hbound := abs_mean_sub_le f r (pos_iff_ne_zero.2 hr0) (ε / 2) fun s hs => by
    have hs' : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; exact hs.2.trans_lt hrδ
    have := hf hs'
    rw [Real.dist_eq, show lift f 0 = f 0 by simp [lift]] at this
    exact this.le
  rw [Real.dist_eq]
  exact hbound.trans_lt (half_lt_self hε)

/-- Continuity of `f̄` on `[0, ∞)`, including the centre (reconstructed from [P] p. 344). -/
theorem continuous_mean {f : C(ℝ≥0, ℝ)} : Continuous (mean f) := by
  refine continuous_iff_continuousAt.2 fun r => ?_
  rcases eq_or_ne r 0 with rfl | hr
  · exact continuousAt_mean_zero f
  · exact continuousAt_mean_of_pos f r (pos_iff_ne_zero.2 hr)

end Christodoulou.Radial.Provider
