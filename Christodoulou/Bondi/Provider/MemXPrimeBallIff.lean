module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
import Christodoulou.Bondi.XPrimeBasics



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem memXPrimeBall_iff {T : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} :
    MemXPrimeBall T x H ↔
      (∀ u : ℝ≥0, u ≤ T → ContDiffOn ℝ 1
        (fun z : ℝ => H (u, z.toNNReal)) (Ici 0)) ∧
      ContinuousOn (fun p : ℝ × ℝ => derivWithin
        (fun z : ℝ => H (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        (Icc 0 (T : ℝ) ×ˢ Ici 0) ∧
      ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
        primeWeight u r ^ 3 * |H (u, r)| +
          primeWeight u r ^ 4 * |radialDerivative H u r| ≤ x :=
  XPB.memXPrimeBall_iff T x H

end Christodoulou.Bondi.Provider
