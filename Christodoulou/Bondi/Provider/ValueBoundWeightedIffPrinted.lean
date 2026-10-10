module
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Christodoulou.Bondi.PrintedDecay



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem valueBound_weighted_iff_printed {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, |H (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-3 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ → |H (u, r)| ≤ C * (r : ℝ) ^ (-3 : ℤ) :=
  XPD.valueBound_weighted_iff_printed H

end Christodoulou.Bondi.Provider
