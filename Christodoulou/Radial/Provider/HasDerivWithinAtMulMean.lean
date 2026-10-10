module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.MeanBasic



public section
open Set
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- First identity of (3.8): `∂_r (r f̄) = f` on `[0, ∞)`, one-sided at the centre. The FTC for
`∫₀ʳ f` is transferred to `r f̄` along their agreement on `[0, ∞)`. -/
theorem hasDerivWithinAt_mul_mean {f : C(ℝ≥0, ℝ)} {r : ℝ≥0} :
    HasDerivWithinAt (fun s : ℝ => s * mean f (Real.toNNReal s)) (f r)
      (Ici 0) (r : ℝ) := by
  have h := (hasDerivAt_integral_lift f r).hasDerivWithinAt (s := Ici 0)
  rw [lift_coe] at h
  exact h.congr_of_mem (fun s hs => mul_mean_eqOn f hs) r.2

end Christodoulou.Radial.Provider
