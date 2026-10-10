/-
# `Christodoulou.Bondi.bondiMass_le_of_deriv_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Bondi.Provider.BondiMassLeOfDerivBound



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem bondiMass_le_of_deriv_bound (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) {C c : ℝ} (hc : 0 < c)
    (hd : ∀ r : ℝ≥0,
      |derivWithin (fun z : ℝ => h z.toNNReal) (Ici 0) r| ≤ C * (c + r) ^ (-4 : ℤ)) :
    bondiMass h hh ≤ 2 * π / 3 * C ^ 2 * c ^ (-5 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.bondiMass_le_of_deriv_bound



end Christodoulou.Bondi

