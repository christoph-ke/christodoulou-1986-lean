/-
# `Christodoulou.Bondi.printedBound_iff_explicit`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Christodoulou.Bondi.Provider.PrintedBoundIffExplicit



public section

open Set Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi


theorem printedBound_iff_explicit {u₀ : ℝ≥0} (f : ℝ≥0 → ℝ≥0 → ℝ) (k : ℤ) :
    (∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ → |f u r| ≤ C * (r : ℝ) ^ k) ↔
      ∃ C R : ℝ, 0 < R ∧ ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, R ≤ r → |f u r| ≤ C * (r : ℝ) ^ k :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.printedBound_iff_explicit



end Christodoulou.Bondi

