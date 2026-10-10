module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic
import Christodoulou.Frozen.Bondi.HasDerivAtMass
import Christodoulou.Frozen.Bondi.MassZero



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- (4.5): `m(r) = 2π ∫₀ʳ (ḡ/g)(h − h̄)²`, by the FTC on `[0, r]` with the sealed derivative (4.4)
on `(0, r)`, continuity of `m`, and the sealed `m(0) = 0`. -/
theorem mass_eq_integral {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} :
    mass h hh r = 2 * π * ∫ s in (0 : ℝ)..(r : ℝ),
      gBar h hh (Real.toNNReal s) / g h hh (Real.toNNReal s) *
        (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 := by
  set F : ℝ → ℝ := fun s => mass h hh (Real.toNNReal s)
  set f : ℝ → ℝ := fun s => gBar h hh (Real.toNNReal s) / g h hh (Real.toNNReal s) *
    (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2
  have hfc : Continuous f :=
    (((continuous_gBar h hh).comp continuous_real_toNNReal).div
      ((continuous_g h hh).comp continuous_real_toNNReal) fun _ => (g_pos h hh _).ne').mul
      (((h.continuous.comp continuous_real_toNNReal).sub
        ((continuous_mean h).comp continuous_real_toNNReal)).pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := F)
    (f' := fun s => 2 * π * f s) r.coe_nonneg
    ((continuous_mass h hh).comp continuous_real_toNNReal).continuousOn
    (fun x hx => by
      have hx' : 0 < Real.toNNReal x := Real.toNNReal_pos.2 hx.1
      have := Christodoulou.Bondi.hasDerivAt_mass h hh _ hx'
      rw [Real.coe_toNNReal x hx.1.le] at this
      exact this.congr_deriv (by simp only [f]; ring))
    ((continuous_const.mul hfc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [F, Real.toNNReal_coe, Real.toNNReal_zero, Christodoulou.Bondi.mass_zero h hh,
    sub_zero] at hFTC
  exact hFTC.symm

end Christodoulou.Bondi.Provider
