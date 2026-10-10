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

theorem printedBound_iff_explicit {u₀ : ℝ≥0}
    {f : ℝ≥0 → ℝ≥0 → ℝ}
    {k : ℤ} :
    (∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ → |f u r| ≤ C * (r : ℝ) ^ k) ↔
      ∃ C R : ℝ, 0 < R ∧ ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, R ≤ r → |f u r| ≤ C * (r : ℝ) ^ k :=
  XPD.printedBound_iff_explicit f k

end Christodoulou.Bondi.Provider
