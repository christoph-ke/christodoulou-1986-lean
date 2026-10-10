/-
# `Christodoulou.Bondi.global_exists_of_G`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.GlobalExistsOfG



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Global existence for d ≤ G(x), s(x) < 1: one field, classical on every strip, in X′, with
explicit decay. -/
theorem global_exists_of_G {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hsmall : d ≤ smallDataG x) (hq : contractionFactor x < 1)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (hbound : InitialBound data d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
      (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
      (∀ r, H (0, r) = data r) ∧
      ∀ u r : ℝ≥0,
        |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
        |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.global_exists_of_G



end Christodoulou.Bondi

