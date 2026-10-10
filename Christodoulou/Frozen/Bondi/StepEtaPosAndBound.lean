/-
# `Christodoulou.Bondi.stepEta_pos_and_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.StepDerivBound
import Christodoulou.Bondi.Provider.StepEtaPosAndBound



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem stepEta_pos_and_bound (d x : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x) :
    0 < stepEta x d ∧ ∀ T : ℝ, 0 ≤ T → T < stepEta x d →
      stepValueBound x d T + stepDerivBound x d T < x :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.stepEta_pos_and_bound



end Christodoulou.Bondi

