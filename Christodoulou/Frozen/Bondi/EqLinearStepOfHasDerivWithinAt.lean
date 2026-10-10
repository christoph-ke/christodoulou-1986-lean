/-
# `Christodoulou.Bondi.eq_linearStep_of_hasDerivWithinAt`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.EqLinearStepOfHasDerivWithinAt



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem eq_linearStep_of_hasDerivWithinAt {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) {q : ℝ≥0 → ℝ≥0 → ℝ}
    (hq₀ : ∀ r, q 0 r = h₀ r)
    (hq : ∀ (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) (χ : ℝ → ℝ), IsCharacteristic hH u₁ r₁ χ →
      ∀ t ∈ Icc 0 (u₁ : ℝ),
        HasDerivWithinAt (fun s : ℝ => q (Real.toNNReal s) (Real.toNNReal (χ s)))
          (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
              q (Real.toNNReal t) (Real.toNNReal (χ t)) +
            linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
          (Icc 0 (u₁ : ℝ)) t)
    {u : ℝ≥0} (hu : u ≤ u₀) (r : ℝ≥0) : q u r = linearStep hH h₀ u r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.eq_linearStep_of_hasDerivWithinAt



end Christodoulou.Bondi

