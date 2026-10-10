/-
# `Christodoulou.Bondi.linearStep_yPrime_lipschitz`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.Provider.LinearStepYPrimeLipschitz



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The weighted (9.27)–(9.38): the linear step contracts the Y′ distance by s(x). -/
theorem linearStep_yPrime_lipschitz {T : ℝ≥0} {x y : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXPrimeBall T x H)
    (hK : MemXPrimeBall T x K) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun z : ℝ => data z.toNNReal) (Ici 0))
    (hSK : MemXPrimeBall T x (linearStepMap hK.1 data))
    (hy : YPrimeDistLe T H K y) :
    YPrimeDistLe T (linearStepMap hH.1 data) (linearStepMap hK.1 data)
      (contractionFactor x * y) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_yPrime_lipschitz



end Christodoulou.Bondi

