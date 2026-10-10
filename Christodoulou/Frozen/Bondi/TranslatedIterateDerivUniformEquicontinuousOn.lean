/-
# `Christodoulou.Bondi.translated_iterate_deriv_uniformEquicontinuousOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.Provider.TranslatedIterateDerivUniformEquicontinuousOn



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The argument of Lemma 3 for the translated seed (9.2): uniform equicontinuity of the radial
derivatives on the strip. -/
theorem translated_iterate_deriv_uniformEquicontinuousOn {T : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data) :
    UniformEquicontinuousOn (fun n (p : ℝ × ℝ) => derivWithin
      (fun z : ℝ => h n (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
      (Icc 0 (T : ℝ) ×ˢ Ici 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.translated_iterate_deriv_uniformEquicontinuousOn



end Christodoulou.Bondi

