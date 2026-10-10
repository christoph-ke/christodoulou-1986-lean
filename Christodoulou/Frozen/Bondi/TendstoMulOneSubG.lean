/-
# `Christodoulou.Bondi.tendsto_mul_one_sub_g`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.Provider.TendstoMulOneSubG



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem tendsto_mul_one_sub_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    Tendsto (fun r : ℝ≥0 => (r : ℝ) * (1 - g h hh r)) atTop (𝓝 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.tendsto_mul_one_sub_g



end Christodoulou.Bondi

