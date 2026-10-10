module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Bondi.BondiMassDecay



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem bondiMass_le_of_deriv_bound {h : C(ℝ≥0, ℝ)}
    (hh : IsSlice h := by assumption)
    {C c : ℝ}
    (hc : 0 < c := by assumption)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ) :=
        by assumption) :
    bondiMass h hh ≤ 2 * π / 3 * C ^ 2 * c ^ (-5 : ℤ) :=
  XBD.bondiMass_le_of_deriv_bound h hh hc hd

end Christodoulou.Bondi.Provider
