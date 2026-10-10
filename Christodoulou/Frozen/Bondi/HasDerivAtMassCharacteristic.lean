/-
# `Christodoulou.Bondi.hasDerivAt_mass_characteristic`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.Provider.HasDerivAtMassCharacteristic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem hasDerivAt_mass_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) {t : ℝ} (ht : 0 < t) (htu : t < u₁) :
    HasDerivAt (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s)))
      (-(π / g (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)))
        * xi (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)) ^ 2) t :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_mass_characteristic



end Christodoulou.Bondi

