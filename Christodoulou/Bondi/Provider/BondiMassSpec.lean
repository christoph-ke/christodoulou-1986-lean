module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.BondiMass



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem bondiMass_spec {h : C(ℝ≥0, ℝ)}
    (hh : IsSlice h := by assumption) :
    BddAbove (Set.range (mass h hh)) ∧
      Tendsto (mass h hh) atTop (𝓝 (bondiMass h hh)) ∧ 0 ≤ bondiMass h hh :=
  XBM.bondiMass_spec h hh

end Christodoulou.Bondi.Provider
