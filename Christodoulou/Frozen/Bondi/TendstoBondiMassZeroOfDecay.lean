/-
# `Christodoulou.Bondi.tendsto_bondiMass_zero_of_decay`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.TendstoBondiMassZeroOfDecay



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem tendsto_bondiMass_zero_of_decay (H : C(ℝ≥0 × ℝ≥0, ℝ))
    (hs : ∀ u : ℝ≥0, IsSlice (H.curry u)) {C : ℝ}
    (hd : ∀ u r : ℝ≥0, |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) :
    Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.tendsto_bondiMass_zero_of_decay



end Christodoulou.Bondi

