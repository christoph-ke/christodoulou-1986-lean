/-
# `Christodoulou.Bondi.linearStep_prime_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.Provider.LinearStepPrimeBound



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- (9.24): the linear step maps the X′ ball of radius x into the radius (2 +
πx²/6)e^{4πx²/3}(d + πx³/8), uniformly in T. -/
theorem linearStep_prime_bound {T : ℝ≥0} {x d : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXPrimeBall T x H)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hd : 0 ≤ d) (hbound : InitialBound data d) :
    MemXPrimeBall T
      ((2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3))
      (linearStepMap hH.1 data) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_prime_bound



end Christodoulou.Bondi

