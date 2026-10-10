module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic
import Christodoulou.Frozen.Bondi.HasDerivAtMass
import Mathlib.Analysis.Calculus.MeanValue



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `m` is nondecreasing ([P] p. 344, "Thus" after (4.4)): `m` is continuous on `[0, ∞)` and its
derivative (4.4), from the sealed `hasDerivAt_mass`, is nonnegative on `(0, ∞)`. -/
theorem monotone_mass {h : C(ℝ≥0, ℝ)} (hh : IsSlice h := by assumption) :
    Monotone (mass h hh) := by
  set F : ℝ → ℝ := fun s => mass h hh (Real.toNNReal s)
  have hcont : Continuous F := (continuous_mass h hh).comp continuous_real_toNNReal
  have hder : ∀ x : ℝ, 0 < x → HasDerivAt F (2 * π * (gBar h hh (Real.toNNReal x) /
      g h hh (Real.toNNReal x)) * (h (Real.toNNReal x) - mean h (Real.toNNReal x)) ^ 2) x := by
    intro x hx
    have := Christodoulou.Bondi.hasDerivAt_mass h hh (Real.toNNReal x) (Real.toNNReal_pos.2 hx)
    rwa [Real.coe_toNNReal x hx.le] at this
  have hmono : MonotoneOn F (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hder x hx).deriv]
      have : 0 ≤ gBar h hh (Real.toNNReal x) / g h hh (Real.toNNReal x) :=
        div_nonneg (gBar_pos h hh _).le (g_pos h hh _).le
      positivity
  intro a b hab
  have := hmono (mem_Ici.2 a.2) (mem_Ici.2 b.2) (by exact_mod_cast hab)
  simpa [F] using this

end Christodoulou.Bondi.Provider
