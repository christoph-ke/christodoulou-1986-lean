/-
# `Christodoulou.Bondi.derivLinearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.Deriv2GBarX
public import Christodoulou.Frozen.Bondi.DerivHBarX
public import Mathlib.Analysis.Calculus.Deriv.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def derivLinearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (_hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) : ℝ :=
  let v : Icc (0 : ℝ) u₀ :=
    ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  let χ := characteristic hH v r
  let A := fun s : ℝ =>
    ∫ τ in s..(v : ℝ), linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ))
  derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) (χ 0) * exp (2 * A 0) +
    ∫ s in (0 : ℝ)..(v : ℝ), exp (2 * A s) *
      ((1 / 2 * deriv2GBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))) *
          linearStep hH data (Real.toNNReal s) (Real.toNNReal (χ s)) +
        (-(1 / 2 * deriv2GBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))) *
            hBarX u₀ H (Real.toNNReal s) (Real.toNNReal (χ s)) -
          linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s)) *
            derivHBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))))

end Christodoulou.Bondi
