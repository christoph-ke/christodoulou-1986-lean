/-
# `Christodoulou.Bondi.contractionFactor_strictMonoOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.Provider.ContractionFactorStrictMonoOn



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- S is strictly increasing on [0, ∞). -/
theorem contractionFactor_strictMonoOn :
    StrictMonoOn contractionFactor (Ici 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.contractionFactor_strictMonoOn



end Christodoulou.Bondi

