/-
# `Christodoulou.Bondi.valueBound_weighted_iff_printed`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Christodoulou.Bondi.Provider.ValueBoundWeightedIffPrinted



public section

open Set Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi


theorem valueBound_weighted_iff_printed {u₀ : ℝ≥0} (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, |H (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-3 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ → |H (u, r)| ≤ C * (r : ℝ) ^ (-3 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.valueBound_weighted_iff_printed



end Christodoulou.Bondi

