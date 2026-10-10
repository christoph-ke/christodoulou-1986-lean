/-
# `Christodoulou.Bondi.antitoneOn_mass_characteristic`

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
import Christodoulou.Bondi.Provider.AntitoneOnMassCharacteristic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- [P] p. 344: m is monotonically nonincreasing along the incoming light rays, on the whole
time interval [0, u₁] of the characteristic through (u₁, r₁), including both endpoints. -/
theorem antitoneOn_mass_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) :
    AntitoneOn (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.antitoneOn_mass_characteristic



end Christodoulou.Bondi

