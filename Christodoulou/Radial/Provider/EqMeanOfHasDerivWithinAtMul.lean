module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Frozen.Radial.HasDerivWithinAtMulMean
import Christodoulou.Frozen.Radial.ContinuousMean
import Christodoulou.Radial.MeanBasic
import Mathlib.Analysis.Calculus.MeanValue



public section
open Set Filter Topology
open scoped NNReal
namespace Christodoulou.Radial.Provider

/-- The (3.9)-type characterization: if `φ` is continuous and `∂_r (r φ) = f` on `[0, ∞)`, then
`φ = f̄`. Graph steps `P.3.9#mul-eq-mul-mean` (uniqueness of antiderivatives, consuming the
sealed first identity of (3.8)), `P.3.9#eq-on-pos`, and `P.3.9#eq-at-zero` (consuming the sealed
continuity of the mean). -/
theorem eq_mean_of_hasDerivWithinAt_mul {f φ : C(ℝ≥0, ℝ)}
    (hφ : ∀ r : ℝ≥0, HasDerivWithinAt (fun s : ℝ => s * φ (Real.toNNReal s)) (f r)
      (Ici 0) (r : ℝ) := by assumption) :
    ⇑φ = mean f := by
  set G : ℝ → ℝ := fun s => s * φ (Real.toNNReal s)
  set M : ℝ → ℝ := fun s => s * mean f (Real.toNNReal s)
  have key : ∀ F : ℝ → ℝ, (∀ r : ℝ≥0, HasDerivWithinAt F (f r) (Ici 0) (r : ℝ)) →
      ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt F (lift f x) (Ici 0) x := by
    intro F hF x hx
    have := hF (Real.toNNReal x)
    rwa [Real.coe_toNNReal x hx] at this
  have hG := key G hφ
  have hM := key M (Christodoulou.Radial.hasDerivWithinAt_mul_mean f)
  -- `P.3.9#mul-eq-mul-mean`
  have hGM : ∀ r : ℝ≥0, G r = M r := by
    intro r
    refine eq_of_has_deriv_right_eq (a := 0) (b := r) (f' := lift f)
      (fun x hx => (hG x hx.1).mono (Ici_subset_Ici.2 hx.1))
      (fun x hx => (hM x hx.1).mono (Ici_subset_Ici.2 hx.1))
      (fun x hx => (hG x hx.1).continuousWithinAt.mono Icc_subset_Ici_self)
      (fun x hx => (hM x hx.1).continuousWithinAt.mono Icc_subset_Ici_self)
      (by simp [G, M]) r ⟨r.2, le_rfl⟩
  -- `P.3.9#eq-on-pos`
  have hpos : ∀ r : ℝ≥0, r ≠ 0 → φ r = mean f r := by
    intro r hr
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have h1 := hGM r
    simp only [G, M, Real.toNNReal_coe] at h1
    exact mul_left_cancel₀ hr' h1
  -- `P.3.9#eq-at-zero`
  exact Continuous.ext_on (dense_compl_singleton 0) φ.continuous
    (Christodoulou.Radial.continuous_mean f) fun r hr => hpos r hr

end Christodoulou.Radial.Provider
