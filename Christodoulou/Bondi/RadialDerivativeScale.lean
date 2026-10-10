module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Bondi.ScalingBasic

/-!
# Scaling the radial derivative

The radial derivative scales by the positive scaling factor, including the one-sided
derivative at the centre.
-/

public section

open scoped NNReal

namespace Christodoulou.Bondi


theorem XRDS.radialDerivative_fieldScale {b : ℝ≥0} (hb : 0 < b)
    (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) :
    radialDerivative (fieldScale b H) u r = (b : ℝ) * radialDerivative H (b * u) (b * r) := by
  exact XSB.derivWithin_radialScale b hb (H.curry (b * u)) r

end Christodoulou.Bondi
