/-
# `Christodoulou.Bondi.reflectedRay`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Order.Interval.Set.Basic



public section

open Set Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] def reflectedRay (u₁ : ℝ) (χ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 u₁ ∧ p.2 = χ p.1} ∪ {p | χ u₁ = 0 ∧ p.1 = u₁ ∧ 0 ≤ p.2}

end Christodoulou.Bondi
