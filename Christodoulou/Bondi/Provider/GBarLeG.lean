module
public import Christodoulou.Frozen.Bondi.GBar
import Christodoulou.Bondi.GBarBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `ḡ ≤ g` ([P] p. 344): the mean of the nondecreasing `g` over `[0, r]` is at most `g(r)`. -/
theorem gBar_le_g {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} : gBar h hh r ≤ g h hh r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [gBar_zero]
  · have hr' : (0 : ℝ) < r := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr)
    rw [gBar_eq_integral h hh r (pos_iff_ne_zero.2 hr), inv_mul_le_iff₀ hr']
    have hc : Continuous fun s : ℝ => g h hh (Real.toNNReal s) :=
      (continuous_g h hh).comp continuous_real_toNNReal
    calc ∫ s in (0 : ℝ)..(r : ℝ), g h hh (Real.toNNReal s)
        ≤ ∫ _ in (0 : ℝ)..(r : ℝ), g h hh r := by
          refine intervalIntegral.integral_mono_on hr'.le (hc.intervalIntegrable _ _)
            intervalIntegrable_const fun s hs => monotone_g h hh ?_
          rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
      _ = (r : ℝ) * g h hh r := by simp

end Christodoulou.Bondi.Provider
