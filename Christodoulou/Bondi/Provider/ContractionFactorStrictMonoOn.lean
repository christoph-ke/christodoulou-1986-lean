module
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.SmallDataScalars



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem contractionFactor_strictMonoOn :
    StrictMonoOn contractionFactor (Ici 0) :=
  XSD.contractionFactor_strictMonoOn 

end Christodoulou.Bondi.Provider
