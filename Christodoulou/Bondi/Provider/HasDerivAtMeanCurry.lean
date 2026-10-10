module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Frozen.Bondi.IntervalIntegrableXi
import Christodoulou.Frozen.Bondi.HasDerivAtXi
import Christodoulou.Frozen.Radial.ContinuousMean
import Christodoulou.Frozen.Radial.HasDerivAtMean
import Christodoulou.Frozen.Radial.MeanEqIntegral
import Christodoulou.Frozen.Radial.MeanZero
import Christodoulou.Analysis.StripDeriv
import Christodoulou.Bondi.XiBasic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi Christodoulou.Analysis

/-- The Φ step: `∫₀^r ∂_u H(u,s) ds = ½ ḡ (h − h̄) + ½ ξ`. -/
theorem integral_fst_eq {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (hs : IsSlice (H.curry u)) (r : ℝ≥0) :
    ∫ s in (0 : ℝ)..(r : ℝ), fderivWithin ℝ (fun p : ℝ × ℝ => H (Real.toNNReal p.1,
        Real.toNNReal p.2)) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ((u : ℝ), s) (1, 0)
      = 1 / 2 * gBar (H.curry u) hs r * (H (u, r) - mean (H.curry u) r)
        + 1 / 2 * xi (H.curry u) hs r := by
  obtain ⟨h1, -, h3⟩ := hH
  have huI : (u : ℝ) ∈ Ioo 0 (u₀ : ℝ) := ⟨hu, hu₀⟩
  have hu₀pos : (0 : ℝ) < u₀ := lt_trans hu hu₀
  set Fu : ℝ → ℝ := fun s => fderivWithin ℝ (fun p : ℝ × ℝ => H (Real.toNNReal p.1,
      Real.toNNReal p.2)) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ((u : ℝ), s) (1, 0) with hFu
  set Fr : ℝ → ℝ := fun s => fderivWithin ℝ (fun p : ℝ × ℝ => H (Real.toNNReal p.1,
      Real.toNNReal p.2)) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ((u : ℝ), s) (0, 1) with hFr
  have hFuc : ContinuousOn Fu (Ici 0) := by
    have := continuousOn_fderivWithin_apply_of_contDiffOn h1 hu₀pos (1, 0)
    exact this.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨⟨huI.1.le, huI.2.le⟩, hs⟩)
  set h : C(ℝ≥0, ℝ) := H.curry u with hhdef
  have hcu : Real.toNNReal (u : ℝ) = u := Real.toNNReal_coe
  -- The pieces of Φ as functions of a real radius.
  set Ψ : ℝ → ℝ := fun ρ => ∫ s in (0 : ℝ)..ρ, Fu s with hΨ
  set G : ℝ → ℝ := fun ρ => gBar h hs (Real.toNNReal ρ) with hG
  set A : ℝ → ℝ := fun ρ => h (Real.toNNReal ρ) - mean h (Real.toNNReal ρ) with hA
  set X : ℝ → ℝ := fun ρ => xi h hs (Real.toNNReal ρ) with hX
  set Φ : ℝ → ℝ := fun ρ => Ψ ρ - 1 / 2 * G ρ * A ρ - 1 / 2 * X ρ with hΦ
  -- integrand of ξ
  set f : ℝ → ℝ := fun s => gBar h hs (Real.toNNReal s) *
    (h (Real.toNNReal s) - mean h (Real.toNNReal s)) / s with hf
  have hGc : Continuous G := (continuous_mean (f := gMap h hs)).comp continuous_real_toNNReal
  have hAc : Continuous A := (h.continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean (f := h)).comp continuous_real_toNNReal)
  -- Φ is continuous on [0, r].
  have hΦc : ContinuousOn Φ (Icc 0 (r : ℝ)) := by
    have hΨc : ContinuousOn Ψ (Icc 0 (r : ℝ)) := by
      have hi : IntegrableOn Fu (uIcc 0 (r : ℝ)) := by
        rw [uIcc_of_le r.coe_nonneg]
        exact (hFuc.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
      have := intervalIntegral.continuousOn_primitive_interval hi
      rwa [uIcc_of_le r.coe_nonneg] at this
    have hXc : ContinuousOn X (Icc 0 (r : ℝ)) := by
      have hi : IntegrableOn f (uIcc 0 (r : ℝ)) := by
        rw [uIcc_of_le r.coe_nonneg, integrableOn_Icc_iff_integrableOn_Ioc]
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le r.coe_nonneg).1
          (intervalIntegrable_xi h hs r)
      have := intervalIntegral.continuousOn_primitive_interval hi
      rw [uIcc_of_le r.coe_nonneg] at this
      refine this.congr fun ρ hρ => ?_
      simp only [hX, xi, Real.coe_toNNReal ρ hρ.1, hf]
    exact (hΨc.sub ((continuous_const.mul hGc).mul hAc).continuousOn).sub
      (continuousOn_const.mul hXc)
  -- Φ has derivative 0 on (0, ∞).
  have hΦd : ∀ ρ ∈ Ioo 0 (r : ℝ), HasDerivAt Φ 0 ρ := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ.1
    set ρ' : ℝ≥0 := Real.toNNReal ρ
    have hρ'c : (ρ' : ℝ) = ρ := Real.coe_toNNReal ρ hρ0.le
    have hρ'pos : 0 < ρ' := Real.toNNReal_pos.2 hρ0
    have dΨ : HasDerivAt Ψ (Fu ρ) ρ :=
      intervalIntegral.integral_hasDerivAt_right
        ((hFuc.mono (by rw [uIcc_of_le hρ0.le]; exact Icc_subset_Ici_self)).intervalIntegrable)
        ((hFuc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi _ hρ0)
        (hFuc.continuousAt (Ici_mem_nhds hρ0))
    have dG : HasDerivAt G ((gMap h hs ρ' - mean (gMap h hs) ρ') / ρ) ρ := by
      have := hasDerivAt_mean (gMap h hs) ρ' hρ'pos
      rw [hρ'c] at this
      exact this
    have dH : HasDerivAt (fun t : ℝ => h (Real.toNNReal t)) (Fr ρ) ρ := by
      have := hasDerivAt_snd_of_contDiffOn h1 huI hρ0
      have e : (fun t : ℝ => H (Real.toNNReal (u : ℝ), Real.toNNReal t))
          = fun t : ℝ => h (Real.toNNReal t) := by
        funext t; rw [hcu]; rfl
      rw [e] at this
      exact this
    have dM : HasDerivAt (fun t : ℝ => mean h (Real.toNNReal t))
        ((h ρ' - mean h ρ') / ρ) ρ := by
      have := hasDerivAt_mean h ρ' hρ'pos
      rwa [hρ'c] at this
    have dA : HasDerivAt A (Fr ρ - (h ρ' - mean h ρ') / ρ) ρ := dH.sub dM
    have dX : HasDerivAt X (gBar h hs ρ' * (h ρ' - mean h ρ') / ρ) ρ := by
      have := hasDerivAt_xi h hs ρ' hρ'pos
      rwa [hρ'c] at this
    have hdu : deriv (fun v : ℝ => H (Real.toNNReal v, ρ')) (u : ℝ) = Fu ρ :=
      (hasDerivAt_fst_of_contDiffOn h1 huI hρ0.le).deriv
    have hdr : deriv (fun s : ℝ => H (u, Real.toNNReal s)) (ρ' : ℝ) = Fr ρ := by
      rw [hρ'c]; exact dH.deriv
    have heq := h3 u hu hu₀ hs ρ' hρ'pos
    rw [hdu, hdr, hρ'c] at heq
    have hall := (dΨ.sub ((dG.const_mul (1 / 2)).mul dA)).sub (dX.const_mul (1 / 2))
    convert hall using 1
    have e2 : mean (gMap h hs) ρ' = gBar h hs ρ' := rfl
    have e3 : gMap h hs ρ' = g h hs ρ' := rfl
    have eG : G ρ = gBar h hs ρ' := rfl
    have eA : A ρ = h ρ' - mean h ρ' := rfl
    have eH : H (u, ρ') = h ρ' := rfl
    rw [e2, e3, eG, eA]
    rw [eH] at heq
    linear_combination (-1 : ℝ) * heq
  -- Φ vanishes on [0, r].
  have hΦ0 : Φ 0 = 0 := by
    simp [hΦ, hΨ, hA, hX, xi_zero, mean_zero]
  have hΦr : Φ r = 0 := by
    rcases (r.coe_nonneg).eq_or_lt with hr0 | hrpos
    · rw [← hr0]; exact hΦ0
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Φ (fun _ => (0 : ℝ)) hrpos hΦc
        (fun x hx => hΦd x hx)
      have : Φ r - Φ 0 = 0 := by
        have hne : (r : ℝ) - 0 ≠ 0 := by linarith
        field_simp at hcd
        linarith
      linarith
  have eG : G r = gBar h hs r := by simp [hG]
  have eA : A r = H (u, r) - mean (H.curry u) r := by simp [hA, hhdef]
  have eX : X r = xi h hs r := by simp [hX]
  simp only [hΦ, eG, eA, eX] at hΦr
  simp only [hΨ] at hΦr
  linarith

theorem hasDerivAt_mean_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption) {u : ℝ≥0} (hu : 0 < u := by assumption)
    (hu₀ : u < u₀ := by assumption) {hs : IsSlice (H.curry u)} {r : ℝ≥0}
    (hr : 0 < r := by assumption) :
    HasDerivAt (fun v : ℝ => mean (H.curry (Real.toNNReal v)) r)
      (1 / 2 * gBar (H.curry u) hs r * ((H (u, r) - mean (H.curry u) r) / (r : ℝ))
        + xi (H.curry u) hs r / (2 * (r : ℝ))) (u : ℝ) := by
  have hI := integral_fst_eq hH u hu hu₀ hs r
  have huI : (u : ℝ) ∈ Ioo 0 (u₀ : ℝ) := ⟨hu, hu₀⟩
  have hd := (hasDerivAt_intervalIntegral_fst_of_contDiffOn hH.1 huI r.coe_nonneg).const_mul
    ((r : ℝ)⁻¹)
  rw [hI] at hd
  have hrpos : (0 : ℝ) < r := hr
  have heq : (fun v : ℝ => mean (H.curry (Real.toNNReal v)) r)
      = fun v : ℝ => (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ),
          H (Real.toNNReal (v, s).1, Real.toNNReal (v, s).2) := by
    funext v
    rw [mean_eq_integral _ r hr]
    rfl
  rw [heq]
  convert hd using 1
  field_simp

end Christodoulou.Bondi.Provider
