module
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.BondiMass
import Christodoulou.Bondi.MassTail



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem bondiMass_eq_integral_one_sub_g {h : C(ℝ≥0, ℝ)}
    (hh : IsSlice h := by assumption) :
    IntegrableOn (fun s : ℝ => 1 - g h hh s.toNNReal) (Ioi 0) ∧
      bondiMass h hh = 1 / 2 * ∫ s in Ioi (0 : ℝ), (1 - g h hh s.toNNReal) :=
  XMT.bondiMass_eq_integral_one_sub_g h hh

end Christodoulou.Bondi.Provider
