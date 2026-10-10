module
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Christodoulou.Frozen.Bondi.HasDerivWithinAtGBarX
import Christodoulou.Frozen.Bondi.DerivGBarXNonneg
import Christodoulou.Frozen.Bondi.DerivGBarXLe
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Provider for `Christodoulou.Bondi.lipschitzWith_gBarX`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/LipschitzWithGBarX.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: `0 ≤ ∂_r ḡ ≤ (π/3) x² r/(1+r)³ ≤ (π/6) x²` (since `r/(1+r)³ ≤ 1/2`); the convex mean-value
inequality on `Ici 0` with the sealed within-derivative; then `ḡ(u, s⁺) = ḡ(u, (max s 0)⁺)` and
`|max a 0 − max b 0| ≤ |a − b|`.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem derivGBarX_abs_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u r : ℝ≥0) : ‖derivGBarX hH u r‖₊ ≤ Real.toNNReal (π / 6 * x ^ 2) := by
  have h0 := derivGBarX_nonneg hH u r
  have h1 := derivGBarX_le hH u r
  have hr : (0 : ℝ) ≤ r := r.2
  have hq : (r : ℝ) / (1 + r) ^ 3 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (r : ℝ), mul_nonneg hr (sq_nonneg (r : ℝ))]
  have h2 : derivGBarX hH u r ≤ π / 6 * x ^ 2 := by
    calc derivGBarX hH u r ≤ π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 := h1
      _ = π / 3 * x ^ 2 * ((r : ℝ) / (1 + (r : ℝ)) ^ 3) := by ring
      _ ≤ π / 3 * x ^ 2 * (1 / 2) := by gcongr
      _ = π / 6 * x ^ 2 := by ring
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h0,
    Real.coe_toNNReal _ (by positivity)]
  exact h2

theorem lipschitzWith_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u : ℝ≥0} :
    LipschitzWith (Real.toNNReal (π / 6 * x ^ 2))
      (fun s : ℝ => gBarX hH u (Real.toNNReal s)) := by
  set f : ℝ → ℝ := fun s => gBarX hH u (Real.toNNReal s)
  have hon : LipschitzOnWith (Real.toNNReal (π / 6 * x ^ 2)) f (Ici 0) := by
    refine (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun s => derivGBarX hH u (Real.toNNReal s)) (fun s hs => ?_) (fun s _ => ?_)
    · have := hasDerivWithinAt_gBarX hH u (Real.toNNReal s)
      rwa [Real.coe_toNNReal s hs] at this
    · exact derivGBarX_abs_le hH u _
  have heq : ∀ s : ℝ, f s = f (max s 0) := by
    intro s; simp [f, Real.toNNReal]
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [heq a, heq b]
  calc dist (f (max a 0)) (f (max b 0))
      ≤ Real.toNNReal (π / 6 * x ^ 2) * dist (max a 0) (max b 0) :=
        hon.dist_le_mul _ (le_max_right a 0) _ (le_max_right b 0)
    _ ≤ Real.toNNReal (π / 6 * x ^ 2) * dist a b := by
        gcongr
        rw [Real.dist_eq, Real.dist_eq]
        exact abs_max_sub_max_le_abs a b 0

end Christodoulou.Bondi.Provider
