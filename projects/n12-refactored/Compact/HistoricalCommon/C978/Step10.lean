import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step10
import Compact.HistoricalCommon.C978.Step10Groups00
import Compact.HistoricalCommon.C978.Step10Groups01
import Compact.HistoricalCommon.C978.Step10Groups02
import Compact.HistoricalCommon.C978.Step10Groups03
import Compact.HistoricalCommon.C978.Step10Groups04
import Compact.HistoricalCommon.C978.Step10Groups05
import Compact.HistoricalCommon.C978.Step10Groups06
import Compact.HistoricalCommon.C978.Step10Groups07
import Compact.HistoricalCommon.C978.Step10Groups08
import Compact.HistoricalCommon.C978.Step10Groups09
import Compact.HistoricalCommon.C978.Step10Groups10
import Compact.HistoricalCommon.C978.Step10Groups11

namespace N12Compact.HistoricalCommon.C978.Step10
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 24 (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 4 .leaf .leaf) (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf)))) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 4 .leaf .leaf) (.sourceCut 6 .leaf .leaf))) (.neighborCut 16 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 8 .leaf .leaf) (.sourceCut 3 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))))) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 6 .leaf .leaf))) (.neighborCut 8 .leaf .leaf))))) (.neighborCut 16 (.sourceCut 12 (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf)) .leaf) (.neighborCut 16 (.sourceCut 6 (.neighborCut 8 .leaf .leaf) (.sourceCut 6 (.neighborCut 8 .leaf (.sourceCut 3 .leaf .leaf)) .leaf)) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf))) (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.sourceCut 12 .leaf (.neighborCut 4 .leaf (.sourceCut 6 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,49,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 49) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 49) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8906_header,context8980_header,context8981_header,context8988_header,context8999_header,context9010_header,context9015_header,context9016_header,context9017_header,context9018_header,context8971_header,context8972_header,context8973_header,context8974_header,context8975_header,context8976_header,context8977_header,context8978_header,context8979_header,context8982_header,context8983_header,context8984_header,context8985_header,context8986_header,context8987_header,context8989_header,context8990_header,context8991_header,context8992_header,context8993_header,context8994_header,context8995_header,context8996_header,context8997_header,context8998_header,context9000_header,context9001_header,context9002_header,context9003_header,context9004_header,context9005_header,context9006_header,context9007_header,context9008_header,context9009_header,context9011_header,context9012_header,context9013_header,context9014_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 49).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8253,some (fanBlockRows 3771)),(8254,some (fanBlockRows 3781)),(8255,some (fanBlockRows 3782)),(8256,some (fanBlockRows 3785)),(8257,some (fanBlockRows 3796)),(8258,some (fanBlockRows 3807)),(8259,some (fanBlockRows 3812)),(8260,some (fanBlockRows 3813)),(8261,some (fanBlockRows 3814)),(8262,some (fanBlockRows 3815)),(8263,some (fanBlockRows 3772)),(8264,some (fanBlockRows 3773)),(8265,some (fanBlockRows 3774)),(8266,some (fanBlockRows 3775)),(8267,some (fanBlockRows 3776)),(8268,some (fanBlockRows 3777)),(8269,some (fanBlockRows 3778)),(8270,some (fanBlockRows 3779)),(8271,some (fanBlockRows 3780)),(8272,none),(8273,none),(8274,none),(8275,none),(8276,none),(8277,none),(8278,none),(8279,none),(8280,none),(8281,none),(8282,none),(8283,none),(8284,none),(8285,none),(8286,none),(8287,some (fanBlockRows 3783)),(8288,some (fanBlockRows 59)),(8289,some (fanBlockRows 59)),(8290,some (fanBlockRows 59)),(8291,some (fanBlockRows 59)),(8292,some (fanBlockRows 3784)),(8293,some (fanBlockRows 3786)),(8294,some (fanBlockRows 3787)),(8295,some (fanBlockRows 3788)),(8296,some (fanBlockRows 3789)),(8297,some (fanBlockRows 3790)),(8298,some (fanBlockRows 3791)),(8299,some (fanBlockRows 3792)),(8300,some (fanBlockRows 3793)),(8301,some (fanBlockRows 3794)),(8302,some (fanBlockRows 3795)),(8303,some (fanBlockRows 3797)),(8304,some (fanBlockRows 3798)),(8305,some (fanBlockRows 3799)),(8306,some (fanBlockRows 3800)),(8307,some (fanBlockRows 3801)),(8308,some (fanBlockRows 3802)),(8309,some (fanBlockRows 3803)),(8310,some (fanBlockRows 3804)),(8311,some (fanBlockRows 3805)),(8312,some (fanBlockRows 3806)),(8313,some (fanBlockRows 3808)),(8314,some (fanBlockRows 3809)),(8315,some (fanBlockRows 3810)),(8316,some (fanBlockRows 3811))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step10.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step10.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step10.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step10
