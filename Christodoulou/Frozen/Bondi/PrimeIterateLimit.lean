/-
# `Christodoulou.Bondi.primeIterate_limit`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Christodoulou.Bondi.Provider.PrimeIterateLimit



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem primeIterate_limit {T : ℝ≥0} {x : ℝ} (hx : 0 < x)
    (hq : contractionFactor x < 1) (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ hH : MemXPrimeBall T x H,
      (∀ n : ℕ, YPrimeDistLe T (h n) H
        (2 * x * contractionFactor x ^ n / (1 - contractionFactor x))) ∧
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => derivWithin
        (fun z : ℝ => h n (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        (fun p : ℝ × ℝ => derivWithin
          (fun z : ℝ => H (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        atTop (Icc 0 (T : ℝ) ×ˢ Ici 0) ∧
      linearStepMap hH.1 data = H ∧ ∀ r, H (0, r) = data r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.primeIterate_limit



end Christodoulou.Bondi

