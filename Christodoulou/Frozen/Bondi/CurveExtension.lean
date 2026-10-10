/-
# `Christodoulou.Bondi.curveExtension`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Mathlib.Order.Interval.Set.ProjIcc
public import Christodoulou.Frozen.Radial.Mean



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def curveExtension {u₀ : ℝ≥0} (u₁ : Icc (0 : ℝ) u₀)
    (χ : Icc (0 : ℝ) (u₁ : ℝ) → ℝ) (t : ℝ) : ℝ :=
  χ (Set.projIcc 0 (u₁ : ℝ) u₁.2.1 t)

end Christodoulou.Bondi
