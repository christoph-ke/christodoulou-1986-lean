module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Frozen.Radial.HasDerivWithinAtMulMean
import Mathlib.Analysis.Calculus.Deriv.Inv



public section
open Set Filter Topology
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- Second identity of (3.8): `∂_r f̄ = (f − f̄)/r` for `r > 0`. Consumes the sealed first
identity `Christodoulou.Radial.hasDerivWithinAt_mul_mean`: graph steps
`P.3.8.second#interior-derivative` (the within-derivative at an interior point) and
`P.3.8.second#quotient-rule`. -/
theorem hasDerivAt_mean {f : C(ℝ≥0, ℝ)} {r : ℝ≥0} (hr : 0 < r := by assumption) :
    HasDerivAt (fun s : ℝ => mean f (Real.toNNReal s))
      ((f r - mean f r) / (r : ℝ)) (r : ℝ) := by
  have hr' : (0 : ℝ) < r := hr
  -- interior derivative
  have h1 : HasDerivAt (fun s : ℝ => s * mean f (Real.toNNReal s)) (f r) (r : ℝ) :=
    (Christodoulou.Radial.hasDerivWithinAt_mul_mean f r).hasDerivAt (Ici_mem_nhds hr')
  -- quotient rule for `s ↦ (s f̄(s)) / s`
  have hq := h1.div (hasDerivAt_id (r : ℝ)) hr'.ne'
  have heq : (fun s : ℝ => mean f (Real.toNNReal s)) =ᶠ[𝓝 (r : ℝ)]
      ((fun s : ℝ => s * mean f (Real.toNNReal s)) / id) := by
    filter_upwards [lt_mem_nhds hr'] with s hs
    rw [Pi.div_apply, id, mul_div_cancel_left₀ _ hs.ne']
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id, Real.toNNReal_coe, mul_one]
  field_simp

end Christodoulou.Radial.Provider
