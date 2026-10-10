module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Frozen.Bondi.Lemma4
import Christodoulou.Frozen.Bondi.Lemma5
import Christodoulou.Frozen.Bondi.PrimeIterateLimit
import Christodoulou.Frozen.Bondi.IsClassicalSolutionOfLinearStepMapEq
import Christodoulou.Frozen.Bondi.Theorem2OfMemXBall
import Christodoulou.Frozen.Bondi.ExistsUniqueContractionRadius
import Christodoulou.Frozen.Bondi.ContractionFactorStrictMonoOn
import Christodoulou.Bondi.XPrimeBasics

/-!
# Global existence by gluing strips

The sealed iteration gates give solutions with one common X′ radius on all finite strips.
Theorem 2 identifies their restrictions. Local agreement then gives a continuous global
field, the classical equation on every strip, and the explicit weighted decay estimates.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XGG

private theorem classical_of_le {S T : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H) (hST : S ≤ T) : IsClassicalSolution S H := by
  refine ⟨hH.1.mono ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (show (S : ℝ) ≤ T from hST)⟩, hp.2⟩
  · obtain ⟨C, hC⟩ := hH.2.1
    exact ⟨C, fun u hu => hC u (hu.trans hST)⟩
  · intro u hu huS
    exact hH.2.2 u hu (huS.trans_le hST)

private theorem classical_congr {T : ℝ≥0} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution T H)
    (heq : ∀ u : ℝ≥0, u ≤ T → ∀ r, K (u, r) = H (u, r)) :
    IsClassicalSolution T K := by
  refine ⟨hH.1.congr ?_, ?_, ?_⟩
  · intro p hp
    exact heq _ (Real.toNNReal_le_iff_le_coe.mpr hp.1.2) _
  · obtain ⟨C, hC⟩ := hH.2.1
    exact ⟨C, fun u hu r => (heq u hu r) ▸ hC u hu r⟩
  · intro u hu huT hs r hr
    have hslice : K.curry u = H.curry u := by
      ext s
      exact heq u huT.le s
    have hrad : (fun s : ℝ => K (u, s.toNNReal)) =
        (fun s : ℝ => H (u, s.toNNReal)) := funext fun s => heq u huT.le _
    have htime : deriv (fun v : ℝ => K (v.toNNReal, r)) (u : ℝ) =
        deriv (fun v : ℝ => H (v.toNNReal, r)) (u : ℝ) := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Iio_mem_nhds (show (u : ℝ) < T from huT)] with v hv
      exact heq _ (Real.toNNReal_le_iff_le_coe.mpr hv.le) r
    have hsH : IsSlice (H.curry u) := hslice ▸ hs
    have hPDE := hH.2.2 u hu huT hsH r hr
    simpa only [hslice, hrad, htime, heq u huT.le r] using hPDE

private theorem prime_congr {T : ℝ≥0} {x : ℝ} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H)
    (heq : ∀ u : ℝ≥0, u ≤ T → ∀ r, K (u, r) = H (u, r)) :
    MemXPrimeBall T x K := by
  have hrad (u : ℝ≥0) (hu : u ≤ T) :
      (fun s : ℝ => K (u, s.toNNReal)) = (fun s : ℝ => H (u, s.toNNReal)) :=
    funext fun s => heq u hu _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    rw [hrad u hu]
    exact hH.1.1 u hu
  · apply hH.1.2.1.congr
    intro p hp
    dsimp only
    rw [hrad _ (Real.toNNReal_le_iff_le_coe.mpr hp.1.2)]
  · intro u hu r
    rw [heq u hu r, hrad u hu]
    exact hH.1.2.2 u hu r
  · intro u hu r
    simp only [radialDerivative, heq u hu r, hrad u hu]
    exact hH.2 u hu r

private theorem strip_exists {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hsmall : d ≤ smallDataG x) (hq : contractionFactor x < 1)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (hbound : InitialBound data d)
    (T : ℝ≥0) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), IsClassicalSolution T H ∧ MemXPrimeBall T x H ∧
      ∀ r, H (0, r) = data r := by
  obtain ⟨x₁, ⟨hx₁, hroot⟩, _⟩ := existsUnique_contraction_radius
  have hxx₁ : x < x₁ := by
    by_contra h
    have hle := contractionFactor_strictMonoOn.monotoneOn
      (show (x₁ : ℝ) ∈ Ici 0 from x₁.coe_nonneg) hx.le (le_of_not_gt h)
    rw [hroot] at hle
    exact (not_le_of_gt hq) hle
  obtain ⟨h, ⟨hzero, hstep⟩, _⟩ := lemma4 (T := T) hx hd hsmall data hdata hbound
  have hcontract := lemma5 x₁ hroot hx hxx₁ data hdata
    (fun n => (h n).val) (fun n => (h n).property) hstep
  obtain ⟨H, hH, _, _, hfix, htrace⟩ := primeIterate_limit hx hcontract.2.1 data hdata
    (fun n => (h n).val) (fun n => (h n).property) hzero hstep
  exact ⟨H, isClassicalSolution_of_linearStepMap_eq hH.1 data hdata.1.1 hfix, hH, htrace⟩

private theorem weighted_decay {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : ∀ T : ℝ≥0, MemXPrimeBall T x H) (u r : ℝ≥0) :
    |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
      |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  have hw : 0 < primeWeight u r := by
    dsimp only [primeWeight]
    positivity
  have hb : 0 < 1 + (u : ℝ) + (r : ℝ) := by positivity
  have hhalf : 1 + (u : ℝ) + (r : ℝ) ≤ 2 * primeWeight u r := by
    dsimp only [primeWeight]
    linarith only [r.coe_nonneg]
  have hsum := (hH u).2 u le_rfl r
  have hval : primeWeight u r ^ 3 * |H (u, r)| ≤ x :=
    (le_add_of_nonneg_right (mul_nonneg (pow_nonneg hw.le _) (abs_nonneg _))).trans hsum
  have hder : primeWeight u r ^ 4 * |radialDerivative H u r| ≤ x :=
    (le_add_of_nonneg_left (mul_nonneg (pow_nonneg hw.le _) (abs_nonneg _))).trans hsum
  have h3 : (1 + (u : ℝ) + (r : ℝ)) ^ 3 ≤ 8 * primeWeight u r ^ 3 := by
    calc
      _ ≤ (2 * primeWeight u r) ^ 3 := pow_le_pow_left₀ hb.le hhalf 3
      _ = _ := by ring
  have h4 : (1 + (u : ℝ) + (r : ℝ)) ^ 4 ≤ 16 * primeWeight u r ^ 4 := by
    calc
      _ ≤ (2 * primeWeight u r) ^ 4 := pow_le_pow_left₀ hb.le hhalf 4
      _ = _ := by ring
  have hv : |H (u, r)| * (1 + (u : ℝ) + (r : ℝ)) ^ 3 ≤ 8 * x := by
    calc
      _ ≤ |H (u, r)| * (8 * primeWeight u r ^ 3) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = 8 * (primeWeight u r ^ 3 * |H (u, r)|) := by ring
      _ ≤ 8 * x := mul_le_mul_of_nonneg_left hval (by norm_num)
  have hd : |radialDerivative H u r| * (1 + (u : ℝ) + (r : ℝ)) ^ 4 ≤ 16 * x := by
    calc
      _ ≤ |radialDerivative H u r| * (16 * primeWeight u r ^ 4) :=
        mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = 16 * (primeWeight u r ^ 4 * |radialDerivative H u r|) := by ring
      _ ≤ 16 * x := mul_le_mul_of_nonneg_left hder (by norm_num)
  constructor
  · simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using
      (le_div_iff₀ (pow_pos hb 3)).2 hv
  · simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using
      (le_div_iff₀ (pow_pos hb 4)).2 hd

/-- Glue the finite-strip solutions to obtain a global field with explicit decay. -/
theorem global_exists_of_G {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hsmall : d ≤ smallDataG x) (hq : contractionFactor x < 1)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (hbound : InitialBound data d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
      (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
      (∀ r, H (0, r) = data r) ∧
      ∀ u r : ℝ≥0,
        |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
        |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  classical
  have hex (n : ℕ) := strip_exists hx hd hsmall hq data hdata hbound (n + 1)
  choose F hclass hball htrace using hex
  have hagree (n m : ℕ) (u : ℝ≥0) (hn : u ≤ n + 1) (hm : u ≤ m + 1)
      (r : ℝ≥0) : F n (u, r) = F m (u, r) := by
    exact theorem2_of_memXBall ((hball n).of_le hn).toMemXBall
      ((hball m).of_le hm).toMemXBall (classical_of_le (hclass n) hn)
      (classical_of_le (hclass m) hm)
      (fun s => (htrace n s).trans (htrace m s).symm) u le_rfl r
  let f : ℝ≥0 × ℝ≥0 → ℝ := fun p => F ⌈p.1⌉₊ p
  have hcover (u : ℝ≥0) : u ≤ (⌈u⌉₊ : ℝ≥0) + 1 :=
    (Nat.le_ceil u).trans (le_add_of_nonneg_right zero_le_one)
  have hlocal (n : ℕ) (u r : ℝ≥0) (hu : u ≤ n + 1) :
      f (u, r) = F n (u, r) := hagree _ n u (hcover u) hu r
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨n, hn⟩ := exists_nat_gt p.1
    have hn' : p.1 < (n : ℝ≥0) + 1 := hn.trans_le
      (le_add_of_nonneg_right zero_le_one)
    apply (F n).continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds hn')] with q hq
    exact hlocal n q.1 q.2 hq.le
  let H : C(ℝ≥0 × ℝ≥0, ℝ) := ⟨f, hf⟩
  have hglobal : ∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H := by
    intro T
    have hT := hcover T
    have heq (u : ℝ≥0) (hu : u ≤ T) (r : ℝ≥0) :
        H (u, r) = F ⌈T⌉₊ (u, r) := hlocal _ u r (hu.trans hT)
    exact ⟨classical_congr (classical_of_le (hclass _) hT) heq,
      prime_congr ((hball _).of_le hT) heq⟩
  refine ⟨H, hglobal, ?_, weighted_decay (fun T => (hglobal T).2)⟩
  intro r
  exact (hlocal 0 0 r (by positivity)).trans (htrace 0 r)

end XGG
end Christodoulou.Bondi
