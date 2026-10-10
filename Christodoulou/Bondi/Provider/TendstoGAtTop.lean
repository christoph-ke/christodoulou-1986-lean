module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- The normalization `g → 1` as `r → ∞` (`ν + λ → 0`, [P] (3.2)): the tail integral tends to 0. -/
theorem tendsto_g_atTop {h : C(ℝ≥0, ℝ)} (hh : IsSlice h := by assumption) :
    Tendsto (g h hh) atTop (𝓝 1) := by
  have hI : Tendsto (fun x : ℝ => ∫ s in (0 : ℝ)..x, tailIntegrand h s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), tailIntegrand h s)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_tail h hh 0) tendsto_id
  have hc : Tendsto (fun r : ℝ≥0 => (r : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
  have hA := ((hI.comp hc).const_sub (∫ s in Ioi (0 : ℝ), tailIntegrand h s)).const_mul (-(4 * π))
  rw [sub_self, mul_zero] at hA
  have he := (Real.continuous_exp.tendsto 0).comp hA
  rw [Real.exp_zero] at he
  exact he.congr fun r => by simp only [Function.comp, g_eq h hh]

end Christodoulou.Bondi.Provider
