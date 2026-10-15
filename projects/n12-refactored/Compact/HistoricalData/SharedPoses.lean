import Compact.HistoricalData.SharedRows
import S12.OwnerEnclosure
import Compact.HistoricalData.PosesChunks.Part000000
import Compact.HistoricalData.PosesChunks.Part001586
import Compact.HistoricalData.PosesChunks.Part003171
import Compact.HistoricalData.PosesChunks.Part004757
import Compact.HistoricalData.PosesChunks.Part006342
import Compact.HistoricalData.PosesChunks.Part007928
import Compact.HistoricalData.PosesChunks.Part009513
import Compact.HistoricalData.PosesChunks.Part011098

namespace N12Compact.HistoricalData
open S12
set_option Elab.async false
noncomputable def poseData : SparseLiteral.Tree (Fin 192 × List (Fin rowCount)) :=
  (.node 6341 (27, [44331,44332,44333,44334,6862,44335,44335,44333,44332,6862,8])
  (.node 3170 (174, [21944,21945,21946,21947,21948,21949,21950,21951,21951,21947,21945,21949,8])
  (.node 1585 (15, [11584,11585,11586,11587,11588,11589,11590,11590,11587,11585,11588,8])
  PosesChunks.part000000
  PosesChunks.part001586)
  (.node 4756 (73, [32186,32187,32188,32189,32190,19831,32191,32191,32189,32187,19831,8])
  PosesChunks.part003171
  PosesChunks.part004757))
  (.node 9512 (99, [14250,15913,66326,66327,66328,29810,29810,15913,14250,66326,8])
  (.node 7927 (62, [55753,55754,2285,43737,55755,55756,55757,55758,55758,2285,55754,55756,8])
  PosesChunks.part006342
  PosesChunks.part007928)
  (.node 11097 (168, [76519,76520,76521,76522,76523,76524,76525,76526,76527,76528,76528,76523,76520,76525,8])
  PosesChunks.part009513
  PosesChunks.part011098)))
noncomputable def poseRecord (index : Nat) : Fin 192 × List (Fin rowCount) :=
  SparseLiteral.lookup (0,[]) poseData index
noncomputable def poseAngle (i : Fin poseCount) : Fin 192 := (poseRecord i.val).1
noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (poseRecord i.val).2
noncomputable def poses (angles : Fin 192 → {w : AngleEnclosure // w.Check})
    (i : Fin poseCount) : PoseLeaf :=
  ⟨angles (poseAngle i), (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩
end N12Compact.HistoricalData
