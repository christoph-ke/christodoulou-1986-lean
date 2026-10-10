/-
# `Christodoulou.Bondi.antitoneOn_bondiMass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.BondiMass
import Christodoulou.Bondi.Provider.AntitoneOnBondiMass



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Bondi's theorem ([P] p. 345, "M is a monotonically nonincreasing function of u"), on the
closed strip [0, u₀], for the class of `hasDerivAt_mass_curry`. -/
theorem antitoneOn_bondiMass {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) :
    AntitoneOn (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) (Icc 0 u₀) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.antitoneOn_bondiMass



end Christodoulou.Bondi

