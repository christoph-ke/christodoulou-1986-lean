/-
# `Christodoulou.Bondi.tendsto_g_atTop`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.Provider.TendstoGAtTop



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem tendsto_g_atTop (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    Tendsto (g h hh) atTop (𝓝 1) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.tendsto_g_atTop



end Christodoulou.Bondi

