/-
# `Christodoulou.Bondi.radialDerivative_fieldScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.RadialDerivativeFieldScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem radialDerivative_fieldScale {b : ℝ≥0} (hb : 0 < b) (H : C(ℝ≥0 × ℝ≥0, ℝ))
    (u r : ℝ≥0) :
    radialDerivative (fieldScale b H) u r = (b : ℝ) * radialDerivative H (b * u) (b * r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.radialDerivative_fieldScale



end Christodoulou.Bondi

