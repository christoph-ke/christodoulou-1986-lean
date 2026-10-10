module
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Bondi.MassScalingBasic
public import Christodoulou.Bondi.ScalingBasic

/-!
# Mass scaling for fields

The mass scaling law (4.14) follows from the radial scaling law on each curried slice.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The mass of the rescaled field is b⁻¹ times the mass at (bu, br), as in (4.14). -/
theorem XMS.mass_fieldScale {b : ℝ≥0} (hb : 0 < b) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0)
    (hs : IsSlice ((fieldScale b H).curry u)) (hs' : IsSlice (H.curry (b * u))) :
    mass ((fieldScale b H).curry u) hs r = (b : ℝ)⁻¹ * mass (H.curry (b * u)) hs' (b * r) := by
  simp only [XSB.fieldScale_curry] at hs ⊢
  exact XMB.mass_radialScale hb _ hs' hs r

end Christodoulou.Bondi
