module
public import Christodoulou.Frozen.Radial.Mean



public section
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- The centre value `f̄(0) = f(0)` ([P] p. 344): the centre branch of `mean`. -/
theorem mean_zero {f : C(ℝ≥0, ℝ)} : mean f 0 = f 0 := by
  simp [mean]

end Christodoulou.Radial.Provider
