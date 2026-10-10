module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `g` is nondecreasing, [P] p. 344: the tail integral of the nonnegative `F` shrinks with the
domain. -/
theorem monotone_g {h : C(ℝ≥0, ℝ)} (hh : IsSlice h := by assumption) : Monotone (g h hh) := by
  intro a b hab
  rw [g, g, Real.exp_le_exp]
  have hmono : (∫ s in Ioi (b : ℝ), tailIntegrand h s) ≤ ∫ s in Ioi (a : ℝ), tailIntegrand h s :=
    setIntegral_mono_set (integrable_tailIntegrand h hh).integrableOn
      ((ae_restrict_mem measurableSet_Ioi).mono fun s hs =>
        tailIntegrand_nonneg h (a.2.trans (le_of_lt hs)))
      (Eventually.of_forall (Ioi_subset_Ioi (by exact_mod_cast hab)))
  have hπ : 0 < 4 * π := by positivity
  change -(4 * π) * (∫ s in Ioi (a : ℝ), tailIntegrand h s) ≤
    -(4 * π) * (∫ s in Ioi (b : ℝ), tailIntegrand h s)
  nlinarith

end Christodoulou.Bondi.Provider
