/-
# `Christodoulou.Bondi.existsUnique_characteristicOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.CurveExtension
import Christodoulou.Bondi.Provider.ExistsUniqueCharacteristicOn



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Well-definedness of the canonical characteristic: on the time interval `[0, u₁]` there is
exactly one curve whose constant extension is a characteristic through `(u₁, r₁)`. -/
theorem existsUnique_characteristicOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) :
    ∃! χ : Icc (0 : ℝ) (u₁ : ℝ) → ℝ, IsCharacteristic hH u₁ r₁ (curveExtension u₁ χ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.existsUnique_characteristicOn



end Christodoulou.Bondi

