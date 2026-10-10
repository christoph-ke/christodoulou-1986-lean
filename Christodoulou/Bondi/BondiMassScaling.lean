module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Bondi.MassScalingBasic
public import Christodoulou.Bondi.ScalingBasic
public import Mathlib.Basic.Real.Pointwise

/-!
# Bondi mass scaling (4.15)

The slice mass scaling law from XMB and reindexing the range by multiplication by a positive
factor give the scaling law for the supremum defining the Bondi mass.
-/

public section

open Set Real Filter Topology
open scoped NNReal Pointwise

namespace Christodoulou.Bondi


theorem XBMS.bondiMass_fieldScale {b : ℝ≥0} (hb : 0 < b) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u : ℝ≥0)
    (hs : IsSlice ((fieldScale b H).curry u)) (hs' : IsSlice (H.curry (b * u))) :
    bondiMass ((fieldScale b H).curry u) hs = (b : ℝ)⁻¹ * bondiMass (H.curry (b * u)) hs' := by
  have hsr : IsSlice (radialScale b (H.curry (b * u))) := by
    simpa only [XSB.fieldScale_curry] using hs
  have hbij : Function.Surjective (fun r : ℝ≥0 => b * r) :=
    mul_left_surjective₀ (ne_of_gt hb)
  have hrange : Set.range (mass ((fieldScale b H).curry u) hs) =
      (b : ℝ)⁻¹ • Set.range (mass (H.curry (b * u)) hs') := by
    have hmass : mass ((fieldScale b H).curry u) hs =
        fun r => (b : ℝ)⁻¹ • mass (H.curry (b * u)) hs' (b * r) := by
      funext r
      simpa only [XSB.fieldScale_curry, smul_eq_mul] using
        XMB.mass_radialScale hb (H.curry (b * u)) hs' hsr r
    rw [hmass, ← Set.smul_set_range]
    congr 1
    exact hbij.range_comp (mass (H.curry (b * u)) hs')
  unfold bondiMass
  rw [hrange, Real.sSup_smul_of_nonneg (inv_nonneg.mpr b.coe_nonneg), smul_eq_mul]

end Christodoulou.Bondi
