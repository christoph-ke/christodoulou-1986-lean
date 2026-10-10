/-
# `Christodoulou.Bondi.bondiMass_eq_integral_one_sub_g`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.BondiMass
import Christodoulou.Bondi.Provider.BondiMassEqIntegralOneSubG



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- [P] (4.7): M = ½ ∫₀^∞ (1 − g) dr, with the integrability of 1 − g on (0, ∞). -/
theorem bondiMass_eq_integral_one_sub_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    IntegrableOn (fun s : ℝ => 1 - g h hh s.toNNReal) (Ioi 0) ∧
      bondiMass h hh = 1 / 2 * ∫ s in Ioi (0 : ℝ), (1 - g h hh s.toNNReal) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.bondiMass_eq_integral_one_sub_g



end Christodoulou.Bondi

