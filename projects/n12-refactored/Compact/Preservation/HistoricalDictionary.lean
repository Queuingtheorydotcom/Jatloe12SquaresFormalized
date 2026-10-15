import Compact.Cases.C713.SharedDictionary

namespace N12Compact.Preservation.HistoricalBank
abbrev rowCount := HistoricalData.rowCount
abbrev poseCount := HistoricalData.poseCount
noncomputable abbrev dictionary := C713Shared.dictionary
noncomputable abbrev poses := C713Shared.poses

theorem positive_denominators (i : Fin rowCount) :
    0 < dictionary.denominators i := HistoricalData.positive_denominators i

theorem dictionary_pose (i : Fin poseCount) : dictionary.pose i = poses i := rfl
end N12Compact.Preservation.HistoricalBank
