import Compact.Cases.C898.CachedPairs.CommonRaw01
import Compact.Cases.C898.CachedPairs.CommonRaw02
import Compact.Cases.C898.CachedPairs.CommonRaw03
import Compact.Cases.C898.CachedPairs.Step01Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step1CommonRawSources : Fin 64 → RawSupportFan.Context :=
  ![commonRaw109, commonRaw174, commonRaw175, commonRaw176, commonRaw177, commonRaw178, commonRaw179, commonRaw180, commonRaw181, commonRaw182, commonRaw183, commonRaw184, commonRaw185, commonRaw186, commonRaw187, commonRaw188, commonRaw189, commonRaw190, commonRaw191, commonRaw192, commonRaw193, commonRaw194, commonRaw195, commonRaw196, commonRaw197, commonRaw198, commonRaw199, commonRaw200, commonRaw201, commonRaw202, commonRaw203, commonRaw204, commonRaw205, commonRaw206, commonRaw207, commonRaw208, commonRaw209, commonRaw210, commonRaw211, commonRaw212, commonRaw213, commonRaw214, commonRaw215, commonRaw216, commonRaw217, commonRaw218, commonRaw219, commonRaw220, commonRaw221, commonRaw222, commonRaw223, commonRaw224, commonRaw225, commonRaw226, commonRaw227, commonRaw228, commonRaw229, commonRaw230, commonRaw231, commonRaw232, commonRaw233, commonRaw234, commonRaw235, commonRaw236]
theorem step1CommonRawSources_exact (i : Fin 64) :
    step1CommonRawSources i = (step1Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw109_exact
  · exact commonRaw174_exact
  · exact commonRaw175_exact
  · exact commonRaw176_exact
  · exact commonRaw177_exact
  · exact commonRaw178_exact
  · exact commonRaw179_exact
  · exact commonRaw180_exact
  · exact commonRaw181_exact
  · exact commonRaw182_exact
  · exact commonRaw183_exact
  · exact commonRaw184_exact
  · exact commonRaw185_exact
  · exact commonRaw186_exact
  · exact commonRaw187_exact
  · exact commonRaw188_exact
  · exact commonRaw189_exact
  · exact commonRaw190_exact
  · exact commonRaw191_exact
  · exact commonRaw192_exact
  · exact commonRaw193_exact
  · exact commonRaw194_exact
  · exact commonRaw195_exact
  · exact commonRaw196_exact
  · exact commonRaw197_exact
  · exact commonRaw198_exact
  · exact commonRaw199_exact
  · exact commonRaw200_exact
  · exact commonRaw201_exact
  · exact commonRaw202_exact
  · exact commonRaw203_exact
  · exact commonRaw204_exact
  · exact commonRaw205_exact
  · exact commonRaw206_exact
  · exact commonRaw207_exact
  · exact commonRaw208_exact
  · exact commonRaw209_exact
  · exact commonRaw210_exact
  · exact commonRaw211_exact
  · exact commonRaw212_exact
  · exact commonRaw213_exact
  · exact commonRaw214_exact
  · exact commonRaw215_exact
  · exact commonRaw216_exact
  · exact commonRaw217_exact
  · exact commonRaw218_exact
  · exact commonRaw219_exact
  · exact commonRaw220_exact
  · exact commonRaw221_exact
  · exact commonRaw222_exact
  · exact commonRaw223_exact
  · exact commonRaw224_exact
  · exact commonRaw225_exact
  · exact commonRaw226_exact
  · exact commonRaw227_exact
  · exact commonRaw228_exact
  · exact commonRaw229_exact
  · exact commonRaw230_exact
  · exact commonRaw231_exact
  · exact commonRaw232_exact
  · exact commonRaw233_exact
  · exact commonRaw234_exact
  · exact commonRaw235_exact
  · exact commonRaw236_exact

def step1CommonSourceAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step1CommonSourceAngles_exact (i : Fin 64) :
    step1CommonSourceAngles i = (step1Sources i).keyAngle := by
  fin_cases i <;> rfl

def step1CommonRawNeighbors : Fin 64 → RawSupportFan.Context :=
  ![commonRaw110, commonRaw111, commonRaw112, commonRaw113, commonRaw114, commonRaw115, commonRaw116, commonRaw117, commonRaw118, commonRaw119, commonRaw120, commonRaw121, commonRaw122, commonRaw123, commonRaw124, commonRaw125, commonRaw126, commonRaw127, commonRaw128, commonRaw129, commonRaw130, commonRaw131, commonRaw132, commonRaw133, commonRaw134, commonRaw135, commonRaw136, commonRaw137, commonRaw138, commonRaw139, commonRaw140, commonRaw141, commonRaw142, commonRaw143, commonRaw144, commonRaw145, commonRaw146, commonRaw147, commonRaw148, commonRaw149, commonRaw150, commonRaw151, commonRaw152, commonRaw153, commonRaw154, commonRaw155, commonRaw156, commonRaw157, commonRaw158, commonRaw159, commonRaw160, commonRaw161, commonRaw162, commonRaw163, commonRaw164, commonRaw165, commonRaw166, commonRaw167, commonRaw168, commonRaw169, commonRaw170, commonRaw171, commonRaw172, commonRaw173]
theorem step1CommonRawNeighbors_exact (i : Fin 64) :
    step1CommonRawNeighbors i = (step1Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw110_exact
  · exact commonRaw111_exact
  · exact commonRaw112_exact
  · exact commonRaw113_exact
  · exact commonRaw114_exact
  · exact commonRaw115_exact
  · exact commonRaw116_exact
  · exact commonRaw117_exact
  · exact commonRaw118_exact
  · exact commonRaw119_exact
  · exact commonRaw120_exact
  · exact commonRaw121_exact
  · exact commonRaw122_exact
  · exact commonRaw123_exact
  · exact commonRaw124_exact
  · exact commonRaw125_exact
  · exact commonRaw126_exact
  · exact commonRaw127_exact
  · exact commonRaw128_exact
  · exact commonRaw129_exact
  · exact commonRaw130_exact
  · exact commonRaw131_exact
  · exact commonRaw132_exact
  · exact commonRaw133_exact
  · exact commonRaw134_exact
  · exact commonRaw135_exact
  · exact commonRaw136_exact
  · exact commonRaw137_exact
  · exact commonRaw138_exact
  · exact commonRaw139_exact
  · exact commonRaw140_exact
  · exact commonRaw141_exact
  · exact commonRaw142_exact
  · exact commonRaw143_exact
  · exact commonRaw144_exact
  · exact commonRaw145_exact
  · exact commonRaw146_exact
  · exact commonRaw147_exact
  · exact commonRaw148_exact
  · exact commonRaw149_exact
  · exact commonRaw150_exact
  · exact commonRaw151_exact
  · exact commonRaw152_exact
  · exact commonRaw153_exact
  · exact commonRaw154_exact
  · exact commonRaw155_exact
  · exact commonRaw156_exact
  · exact commonRaw157_exact
  · exact commonRaw158_exact
  · exact commonRaw159_exact
  · exact commonRaw160_exact
  · exact commonRaw161_exact
  · exact commonRaw162_exact
  · exact commonRaw163_exact
  · exact commonRaw164_exact
  · exact commonRaw165_exact
  · exact commonRaw166_exact
  · exact commonRaw167_exact
  · exact commonRaw168_exact
  · exact commonRaw169_exact
  · exact commonRaw170_exact
  · exact commonRaw171_exact
  · exact commonRaw172_exact
  · exact commonRaw173_exact

def step1CommonNeighborAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step1CommonNeighborAngles_exact (i : Fin 64) :
    step1CommonNeighborAngles i = (step1Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step1CommonNeighborUnblocked : ∀ j, (step1Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
