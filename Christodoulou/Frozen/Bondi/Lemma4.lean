/-
# `Christodoulou.Bondi.lemma4`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.Provider.Lemma4



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem lemma4 {T : ℝ≥0} {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hsmall : d ≤ smallDataG x) (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : InitialBound data d) :
    ∃! h : ℕ → {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H},
      (h 0).val = translatedDataField T data ∧
      ∀ n, (h (n + 1)).val = linearStepMap (h n).property.1 data :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.lemma4



end Christodoulou.Bondi

