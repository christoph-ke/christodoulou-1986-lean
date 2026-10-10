/-
# `Christodoulou.Bondi.linearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.Characteristic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def linearStep {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) (u r : ℝ≥0) : ℝ :=
  let v : Icc (0 : ℝ) u₀ := ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  let χ := characteristic hH v r
  h₀ (Real.toNNReal (χ 0)) *
      exp (∫ s in (0 : ℝ)..(v : ℝ), linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s))) +
    ∫ s in (0 : ℝ)..(v : ℝ),
      exp (∫ τ in s..(v : ℝ), linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ))) *
        linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s))

end Christodoulou.Bondi
