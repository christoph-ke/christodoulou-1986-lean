/-
# `Christodoulou.Bondi.memXPrimeBall_iff`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
import Christodoulou.Bondi.Provider.MemXPrimeBallIff



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Characterization of `MemXPrimeBall`: regularity and the X′ sum bound (the unweighted bound
is redundant). -/
theorem memXPrimeBall_iff (T : ℝ≥0) (x : ℝ) (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    MemXPrimeBall T x H ↔
      (∀ u : ℝ≥0, u ≤ T → ContDiffOn ℝ 1
        (fun z : ℝ => H (u, z.toNNReal)) (Ici 0)) ∧
      ContinuousOn (fun p : ℝ × ℝ => derivWithin
        (fun z : ℝ => H (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        (Icc 0 (T : ℝ) ×ˢ Ici 0) ∧
      ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
        primeWeight u r ^ 3 * |H (u, r)| +
          primeWeight u r ^ 4 * |radialDerivative H u r| ≤ x :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.memXPrimeBall_iff



end Christodoulou.Bondi

