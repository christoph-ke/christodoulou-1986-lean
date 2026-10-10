/-
# `Christodoulou.Bondi.characteristic_sub_mem_Icc`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Christodoulou.Bondi.Provider.CharacteristicSubMemIcc



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem characteristic_sub_mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) {r₁ r₁' : ℝ≥0} (hr : r₁ ≤ r₁')
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    characteristic hH u₁ r₁' t - characteristic hH u₁ r₁ t ∈
      Icc ((r₁' : ℝ) - r₁) (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * ((r₁' : ℝ) - r₁)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.characteristic_sub_mem_Icc



end Christodoulou.Bondi

