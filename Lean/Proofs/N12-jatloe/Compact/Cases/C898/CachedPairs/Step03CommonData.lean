import Compact.Cases.C898.CachedPairs.CommonRaw05
import Compact.Cases.C898.CachedPairs.CommonRaw06
import Compact.Cases.C898.CachedPairs.Step03Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step3CommonRawSources : Fin 7 → RawSupportFan.Context :=
  ![commonRaw343, commonRaw408, commonRaw409, commonRaw410, commonRaw411, commonRaw412, commonRaw413]
theorem step3CommonRawSources_exact (i : Fin 7) :
    step3CommonRawSources i = (step3Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw343_exact
  · exact commonRaw408_exact
  · exact commonRaw409_exact
  · exact commonRaw410_exact
  · exact commonRaw411_exact
  · exact commonRaw412_exact
  · exact commonRaw413_exact

def step3CommonSourceAngles : Fin 7 → Fin 64 :=
  ![8, 9, 10, 11, 12, 13, 14]
theorem step3CommonSourceAngles_exact (i : Fin 7) :
    step3CommonSourceAngles i = (step3Sources i).keyAngle := by
  fin_cases i <;> rfl

def step3CommonRawNeighbors : Fin 64 → RawSupportFan.Context :=
  ![commonRaw344, commonRaw345, commonRaw346, commonRaw347, commonRaw348, commonRaw349, commonRaw350, commonRaw351, commonRaw352, commonRaw353, commonRaw354, commonRaw355, commonRaw356, commonRaw357, commonRaw358, commonRaw359, commonRaw360, commonRaw361, commonRaw362, commonRaw363, commonRaw364, commonRaw365, commonRaw366, commonRaw367, commonRaw368, commonRaw369, commonRaw370, commonRaw371, commonRaw372, commonRaw373, commonRaw374, commonRaw375, commonRaw376, commonRaw377, commonRaw378, commonRaw379, commonRaw380, commonRaw381, commonRaw382, commonRaw383, commonRaw384, commonRaw385, commonRaw386, commonRaw387, commonRaw388, commonRaw389, commonRaw390, commonRaw391, commonRaw392, commonRaw393, commonRaw394, commonRaw395, commonRaw396, commonRaw397, commonRaw398, commonRaw399, commonRaw400, commonRaw401, commonRaw402, commonRaw403, commonRaw404, commonRaw405, commonRaw406, commonRaw407]
theorem step3CommonRawNeighbors_exact (i : Fin 64) :
    step3CommonRawNeighbors i = (step3Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw344_exact
  · exact commonRaw345_exact
  · exact commonRaw346_exact
  · exact commonRaw347_exact
  · exact commonRaw348_exact
  · exact commonRaw349_exact
  · exact commonRaw350_exact
  · exact commonRaw351_exact
  · exact commonRaw352_exact
  · exact commonRaw353_exact
  · exact commonRaw354_exact
  · exact commonRaw355_exact
  · exact commonRaw356_exact
  · exact commonRaw357_exact
  · exact commonRaw358_exact
  · exact commonRaw359_exact
  · exact commonRaw360_exact
  · exact commonRaw361_exact
  · exact commonRaw362_exact
  · exact commonRaw363_exact
  · exact commonRaw364_exact
  · exact commonRaw365_exact
  · exact commonRaw366_exact
  · exact commonRaw367_exact
  · exact commonRaw368_exact
  · exact commonRaw369_exact
  · exact commonRaw370_exact
  · exact commonRaw371_exact
  · exact commonRaw372_exact
  · exact commonRaw373_exact
  · exact commonRaw374_exact
  · exact commonRaw375_exact
  · exact commonRaw376_exact
  · exact commonRaw377_exact
  · exact commonRaw378_exact
  · exact commonRaw379_exact
  · exact commonRaw380_exact
  · exact commonRaw381_exact
  · exact commonRaw382_exact
  · exact commonRaw383_exact
  · exact commonRaw384_exact
  · exact commonRaw385_exact
  · exact commonRaw386_exact
  · exact commonRaw387_exact
  · exact commonRaw388_exact
  · exact commonRaw389_exact
  · exact commonRaw390_exact
  · exact commonRaw391_exact
  · exact commonRaw392_exact
  · exact commonRaw393_exact
  · exact commonRaw394_exact
  · exact commonRaw395_exact
  · exact commonRaw396_exact
  · exact commonRaw397_exact
  · exact commonRaw398_exact
  · exact commonRaw399_exact
  · exact commonRaw400_exact
  · exact commonRaw401_exact
  · exact commonRaw402_exact
  · exact commonRaw403_exact
  · exact commonRaw404_exact
  · exact commonRaw405_exact
  · exact commonRaw406_exact
  · exact commonRaw407_exact

def step3CommonNeighborAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step3CommonNeighborAngles_exact (i : Fin 64) :
    step3CommonNeighborAngles i = (step3Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step3CommonNeighborUnblocked : ∀ j, (step3Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
