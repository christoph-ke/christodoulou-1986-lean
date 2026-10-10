module
public import Christodoulou.Frozen.Bondi.BondiMassLeOfDerivBound
public import Christodoulou.Frozen.Bondi.BondiMassSpec
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The Bondi mass tends to zero under radial derivative decay, using the sealed mass estimate
and the nonnegativity supplied by the Bondi mass specification.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Radial derivative decay implies that the Bondi mass tends to zero as time tends to infinity. -/
theorem XBL.tendsto_bondiMass_zero_of_decay (H : C(ℝ≥0 × ℝ≥0, ℝ))
    (hs : ∀ u : ℝ≥0, IsSlice (H.curry u)) {C : ℝ}
    (hd : ∀ u r : ℝ≥0, |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) :
    Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) := by
  have hnonneg (u : ℝ≥0) : 0 ≤ bondiMass (H.curry u) (hs u) :=
    (bondiMass_spec (H.curry u) (hs u)).2.2
  have hupper (u : ℝ≥0) :
      bondiMass (H.curry u) (hs u) ≤ 2 * π / 3 * C ^ 2 * (1 + (u : ℝ)) ^ (-5 : ℤ) := by
    apply bondiMass_le_of_deriv_bound _ (hs u) (by positivity)
    intro r
    rw [show derivWithin (fun z : ℝ => (H.curry u) z.toNNReal) (Ici 0) r =
      radialDerivative H u r from rfl]
    exact hd u r
  have hu : Tendsto (fun u : ℝ≥0 => 1 + (u : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hzero : Tendsto
      (fun u : ℝ≥0 => 2 * π / 3 * C ^ 2 * (1 + (u : ℝ)) ^ (-5 : ℤ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_zpow_atTop_zero (show (-5 : ℤ) < 0 by norm_num)).comp hu).const_mul
        (2 * π / 3 * C ^ 2)
  exact squeeze_zero hnonneg hupper hzero

end Christodoulou.Bondi
