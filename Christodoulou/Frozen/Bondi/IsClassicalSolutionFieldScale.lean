/-
# `Christodoulou.Bondi.isClassicalSolution_fieldScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.Provider.IsClassicalSolutionFieldScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem isClassicalSolution_fieldScale {b : ℝ≥0} (hb : 0 < b) {T : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution (b * T) H) :
    IsClassicalSolution T (fieldScale b H) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.isClassicalSolution_fieldScale



end Christodoulou.Bondi

