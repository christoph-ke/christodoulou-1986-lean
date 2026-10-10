/-
# `Christodoulou.Radial.mean`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

/-- The radial mean `f̄(r) = r⁻¹ ∫₀ʳ f` of [P] (3.7), with the centre value `f̄(0) = f(0)`
of [P] p. 344. -/
@[expose] noncomputable def mean (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : ℝ :=
  if r = 0 then f 0 else (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), f (Real.toNNReal s)

end Christodoulou.Radial
