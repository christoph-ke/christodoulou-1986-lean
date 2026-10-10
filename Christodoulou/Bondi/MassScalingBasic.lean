module
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Bondi.ScalingCovariance



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.XMB

/-- The slice form of (4.14): the mass of `h(b ·)` at r is b⁻¹ times the mass of h at br. -/
theorem mass_radialScale {b : ℝ≥0} (hb : 0 < b) (h : C(ℝ≥0, ℝ))
    (hh : IsSlice h) (hs : IsSlice (radialScale b h)) (r : ℝ≥0) :
    mass (radialScale b h) hs r = (b : ℝ)⁻¹ * mass h hh (b * r) := by
  unfold mass
  rw [XSC.gBar_radialScale b hb h hh hs r, XSC.g_radialScale b hb h hh hs r,
    NNReal.coe_mul, mul_div_assoc, mul_assoc,
    inv_mul_cancel_left₀ (show (b : ℝ) ≠ 0 from ne_of_gt hb)]

end Christodoulou.Bondi.XMB
