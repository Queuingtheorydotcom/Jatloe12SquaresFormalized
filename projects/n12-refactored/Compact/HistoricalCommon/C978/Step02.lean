import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step02
import Compact.HistoricalCommon.C978.Step02Groups00
import Compact.HistoricalCommon.C978.Step02Groups01
import Compact.HistoricalCommon.C978.Step02Groups02

namespace N12Compact.HistoricalCommon.C978.Step02
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 16 (.sourceCut 8 (.neighborCut 8 .leaf .leaf) (.sourceCut 8 .leaf (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.neighborCut 8 (.sourceCut 4 .leaf .leaf) .leaf)))))) (.neighborCut 16 .leaf .leaf))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9321_header,context9396_header,context9407_header,context9418_header,context9429_header,context9440_header,context9445_header,context9446_header,context9447_header,context9448_header,context9386_header,context9387_header,context9388_header,context9389_header,context9390_header,context9391_header,context9392_header,context9393_header,context9394_header,context9395_header,context9397_header,context9398_header,context9399_header,context9400_header,context9401_header,context9402_header,context9403_header,context9404_header,context9405_header,context9406_header,context9408_header,context9409_header,context9410_header,context9411_header,context9412_header,context9413_header,context9414_header,context9415_header,context9416_header,context9417_header,context9419_header,context9420_header,context9421_header,context9422_header,context9423_header,context9424_header,context9425_header,context9426_header,context9427_header,context9428_header,context9430_header,context9431_header,context9432_header,context9433_header,context9434_header,context9435_header,context9436_header,context9437_header,context9438_header,context9439_header,context9441_header,context9442_header,context9443_header,context9444_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8527,some (fanBlockRows 3889)),(8528,some (fanBlockRows 3890)),(8529,some (fanBlockRows 3891)),(8530,some (fanBlockRows 3892)),(8531,some (fanBlockRows 3893)),(8532,some (fanBlockRows 3894)),(8533,some (fanBlockRows 3897)),(8534,some (fanBlockRows 3898)),(8535,some (fanBlockRows 3899)),(8536,some (fanBlockRows 3900)),(8537,some (fanBlockRows 59)),(8538,some (fanBlockRows 59)),(8539,some (fanBlockRows 59)),(8540,some (fanBlockRows 59)),(8541,some (fanBlockRows 59)),(8542,some (fanBlockRows 59)),(8543,some (fanBlockRows 59)),(8544,some (fanBlockRows 59)),(8545,some (fanBlockRows 59)),(8546,some (fanBlockRows 59)),(8547,some (fanBlockRows 59)),(8548,some (fanBlockRows 59)),(8549,some (fanBlockRows 59)),(8550,some (fanBlockRows 59)),(8551,some (fanBlockRows 59)),(8552,some (fanBlockRows 59)),(8553,some (fanBlockRows 59)),(8554,some (fanBlockRows 59)),(8555,some (fanBlockRows 59)),(8556,some (fanBlockRows 59)),(8557,some (fanBlockRows 59)),(8558,some (fanBlockRows 59)),(8559,some (fanBlockRows 59)),(8560,some (fanBlockRows 59)),(8561,some (fanBlockRows 59)),(8562,some (fanBlockRows 59)),(8563,some (fanBlockRows 59)),(8564,some (fanBlockRows 59)),(8565,some (fanBlockRows 59)),(8566,some (fanBlockRows 59)),(8567,some (fanBlockRows 59)),(8568,some (fanBlockRows 59)),(8569,some (fanBlockRows 59)),(8570,some (fanBlockRows 59)),(8571,some (fanBlockRows 59)),(8572,some (fanBlockRows 59)),(8573,some (fanBlockRows 59)),(8574,some (fanBlockRows 59)),(8575,some (fanBlockRows 59)),(8576,some (fanBlockRows 59)),(8577,some (fanBlockRows 59)),(8578,some (fanBlockRows 59)),(8579,some (fanBlockRows 59)),(8580,some (fanBlockRows 59)),(8581,some (fanBlockRows 59)),(8582,some (fanBlockRows 59)),(8583,some (fanBlockRows 59)),(8584,some (fanBlockRows 59)),(8585,some (fanBlockRows 59)),(8586,some (fanBlockRows 59)),(8587,some (fanBlockRows 59)),(8588,some (fanBlockRows 59)),(8589,some (fanBlockRows 3895)),(8590,some (fanBlockRows 3896))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain11_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain11_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain11_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step02
