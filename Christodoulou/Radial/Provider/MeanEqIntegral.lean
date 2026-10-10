module
public import Christodoulou.Frozen.Radial.Mean



public section
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- The defining formula (3.7) of the mean for `r > 0`: the `r ≠ 0` branch of `mean`. -/
theorem mean_eq_integral {f : C(ℝ≥0, ℝ)} {r : ℝ≥0} (hr : 0 < r := by assumption) :
    mean f r = (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), f (Real.toNNReal s) := by
  simp [mean, hr.ne']

end Christodoulou.Radial.Provider
