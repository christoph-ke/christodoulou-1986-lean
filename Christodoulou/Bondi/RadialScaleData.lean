module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Bondi.ScalingBasic

/-!
# Decaying data under radial scaling

Positive radial scaling preserves the data class `IsDecaySlice`: the slice regularity and
decay follow from `XSB.isSlice_radialScale`, and the derivative decay follows from the chain
rule and preservation of big-O bounds under positive scaling.
-/

public section

open Set Real Filter Topology Asymptotics
open scoped NNReal

namespace Christodoulou.Bondi

/-- Positive radial scaling preserves the decaying data class of Theorem 1. -/
theorem XRS.isDecaySlice_radialScale {b : ℝ≥0} (hb : 0 < b) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) : IsDecaySlice (radialScale b data) := by
  refine ⟨XSB.isSlice_radialScale b hb data hdata.1, ?_⟩
  change deriv (fun t : ℝ => radialScale b data (Real.toNNReal t)) =O[atTop] _
  have heq : deriv (fun t : ℝ => radialScale b data (Real.toNNReal t)) =
      (fun s => (b : ℝ) * deriv (fun t : ℝ => data (Real.toNNReal t)) ((b : ℝ) * s)) :=
    funext (XSB.deriv_radialScale b data)
  rw [heq]
  exact (XSB.bigO_scale b hb _ _ hdata.2).const_mul_left (b : ℝ)

end Christodoulou.Bondi
