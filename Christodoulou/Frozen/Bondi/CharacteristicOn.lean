/-
# `Christodoulou.Bondi.characteristicOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.CurveExtension
public import Christodoulou.Frozen.Bondi.ExistsUniqueCharacteristicOn



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The characteristic `χ(u; u₁, r₁)` through `(u₁, r₁)`, as a function on `[0, u₁]`. -/
@[expose] noncomputable def characteristicOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) : Icc (0 : ℝ) (u₁ : ℝ) → ℝ :=
  Classical.choose (existsUnique_characteristicOn hH u₁ r₁).exists

end Christodoulou.Bondi
