/-
# `Christodoulou.Bondi.charField_of_le`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.CharField
import Christodoulou.Bondi.Provider.CharFieldOfLe



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem charField_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    {t : ℝ} (ht : t ≤ u₀) (hs : IsSlice (H.curry (Real.toNNReal t))) (z : ℝ) :
    charField hH t z = -(1 / 2) * gBar (H.curry (Real.toNNReal t)) hs (Real.toNNReal z) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.charField_of_le



end Christodoulou.Bondi

