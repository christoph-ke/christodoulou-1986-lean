module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Frozen.Bondi.ContinuousGBarX
import Christodoulou.Frozen.Bondi.DerivGBarXNonneg
import Christodoulou.Frozen.Bondi.DerivGBarXLe
import Christodoulou.Bondi.XBallContinuity

/-!
# Provider for `Christodoulou.Bondi.continuous_derivGBarX`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/ContinuousDerivGBarX.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: for `r > 0`, `∂_r ḡ = (g − ḡ)/r` is a quotient of jointly continuous functions (approved
helper `continuous_gX` and sealed `continuous_gBarX`); at the centre, `0 ≤ ∂_r ḡ ≤ (π/3) x² r`
(sealed `derivGBarX_nonneg`, `derivGBarX_le`) squeezes it to `0`.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_derivGBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} : Continuous (fun p : ℝ≥0 × ℝ≥0 => derivGBarX hH p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨u, r⟩
  rcases eq_or_ne r 0 with rfl | hr
  · -- centre: squeeze between 0 and (π/3) x² r
    have hb : ∀ q : ℝ≥0 × ℝ≥0, |derivGBarX hH q.1 q.2| ≤ π / 3 * x ^ 2 * (q.2 : ℝ) := by
      intro q
      rw [abs_of_nonneg (derivGBarX_nonneg hH q.1 q.2)]
      refine (derivGBarX_le hH q.1 q.2).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (1 + (q.2 : ℝ)) ^ 3 := one_le_pow₀ (by linarith [q.2.coe_nonneg])
      have h2 : 0 ≤ π / 3 * x ^ 2 * (q.2 : ℝ) := by positivity
      nlinarith
    have h0 : derivGBarX hH u 0 = 0 := by simp [derivGBarX]
    change Tendsto _ _ (𝓝 (derivGBarX hH u 0))
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun q => norm_nonneg _) (fun q => (Real.norm_eq_abs _).le.trans (hb q)) ?_
    have : Continuous (fun q : ℝ≥0 × ℝ≥0 => π / 3 * x ^ 2 * (q.2 : ℝ)) := by fun_prop
    simpa using this.tendsto (u, 0)
  · -- r > 0: the quotient (g − ḡ)/r near (u, r)
    have hev : (fun q : ℝ≥0 × ℝ≥0 => derivGBarX hH q.1 q.2)
        =ᶠ[𝓝 (u, r)] fun q => (gX hH q.1 q.2 - gBarX hH q.1 q.2) / (q.2 : ℝ) := by
      have : ∀ᶠ q : ℝ≥0 × ℝ≥0 in 𝓝 (u, r), q.2 ≠ 0 :=
        (continuous_snd.tendsto (u, r)).eventually (isOpen_ne.mem_nhds hr)
      filter_upwards [this] with q hq
      simp [derivGBarX, hq]
    refine ContinuousAt.congr ?_ hev.symm
    exact (((continuous_gX hH).sub (continuous_gBarX hH)).continuousAt).div
      ((NNReal.continuous_coe.comp continuous_snd).continuousAt) (by simpa using hr)

end Christodoulou.Bondi.Provider
