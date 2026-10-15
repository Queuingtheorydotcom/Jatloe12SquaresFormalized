import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step16
import Compact.HistoricalCommon.C717.Step16Groups00
import Compact.HistoricalCommon.C717.Step16Groups01
import Compact.HistoricalCommon.C717.Step16Groups02
import Compact.HistoricalCommon.C717.Step16Groups03
import Compact.HistoricalCommon.C717.Step16Groups04
import Compact.HistoricalCommon.C717.Step16Groups05
import Compact.HistoricalCommon.C717.Step16Groups06
import Compact.HistoricalCommon.C717.Step16Groups07

namespace N12Compact.HistoricalCommon.C717.Step16
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 3 (.neighborCut 5 .leaf .leaf) (.sourceCut 4 .leaf (.sourceCut 7 .leaf (.sourceCut 7 .leaf (.sourceCut 7 (.neighborCut 5 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 28 (.neighborCut 5 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 28 (.neighborCut 5 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 14 (.neighborCut 5 .leaf .leaf) (.sourceCut 7 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf)))) (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,113,0,11⟩ scopes := by decide +kernel

theorem covered (i : Fin 113) (j : Fin 11) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 113) (j : Fin 11) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4893_header,context4928_header,context4939_header,context4950_header,context4961_header,context4972_header,context4983_header,context4994_header,context5005_header,context5016_header,context4915_header,context4919_header,context4920_header,context4921_header,context4922_header,context4923_header,context4924_header,context4925_header,context4926_header,context4927_header,context4929_header,context4930_header,context4931_header,context4932_header,context4933_header,context4934_header,context4935_header,context4936_header,context4937_header,context4938_header,context4940_header,context4941_header,context4942_header,context4943_header,context4944_header,context4945_header,context4946_header,context4947_header,context4948_header,context4949_header,context4951_header,context4952_header,context4953_header,context4954_header,context4955_header,context4956_header,context4957_header,context4958_header,context4959_header,context4960_header,context4962_header,context4963_header,context4964_header,context4965_header,context4966_header,context4967_header,context4968_header,context4969_header,context4970_header,context4971_header,context4973_header,context4974_header,context4975_header,context4976_header,context4977_header,context4978_header,context4979_header,context4980_header,context4981_header,context4982_header,context4984_header,context4985_header,context4986_header,context4987_header,context4988_header,context4989_header,context4990_header,context4991_header,context4992_header,context4993_header,context4995_header,context4996_header,context4997_header,context4998_header,context4999_header,context5000_header,context5001_header,context5002_header,context5003_header,context5004_header,context5006_header,context5007_header,context5008_header,context5009_header,context5010_header,context5011_header,context5012_header,context5013_header,context5014_header,context5015_header,context4905_header,context4906_header,context4907_header,context4908_header,context4909_header,context4910_header,context4911_header,context4912_header,context4913_header,context4914_header,context4916_header,context4917_header,context4918_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 113).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(4627,some (fanBlockRows 1845)),(4628,some (fanBlockRows 59)),(4629,some (fanBlockRows 59)),(4630,some (fanBlockRows 59)),(4631,some (fanBlockRows 59)),(4632,some (fanBlockRows 59)),(4633,some (fanBlockRows 59)),(4634,some (fanBlockRows 59)),(4635,some (fanBlockRows 59)),(4636,some (fanBlockRows 59)),(4637,some (fanBlockRows 59)),(4638,some (fanBlockRows 59)),(4639,some (fanBlockRows 59)),(4640,some (fanBlockRows 59)),(4641,some (fanBlockRows 59)),(4642,some (fanBlockRows 59)),(4643,some (fanBlockRows 59)),(4644,some (fanBlockRows 59)),(4645,some (fanBlockRows 59)),(4646,some (fanBlockRows 59)),(4647,some (fanBlockRows 59)),(4648,some (fanBlockRows 59)),(4649,some (fanBlockRows 59)),(4650,some (fanBlockRows 59)),(4651,some (fanBlockRows 59)),(4652,some (fanBlockRows 59)),(4653,some (fanBlockRows 59)),(4654,some (fanBlockRows 59)),(4655,some (fanBlockRows 59)),(4656,some (fanBlockRows 59)),(4657,some (fanBlockRows 59)),(4658,some (fanBlockRows 59)),(4659,some (fanBlockRows 59)),(4660,some (fanBlockRows 59)),(4661,some (fanBlockRows 59)),(4662,some (fanBlockRows 59)),(4663,some (fanBlockRows 59)),(4664,some (fanBlockRows 59)),(4665,some (fanBlockRows 59)),(4666,some (fanBlockRows 59)),(4667,some (fanBlockRows 59)),(4668,some (fanBlockRows 59)),(4669,some (fanBlockRows 59)),(4670,some (fanBlockRows 59)),(4671,some (fanBlockRows 59)),(4672,some (fanBlockRows 59)),(4673,some (fanBlockRows 59)),(4674,some (fanBlockRows 59)),(4675,some (fanBlockRows 59)),(4676,some (fanBlockRows 59)),(4677,some (fanBlockRows 59)),(4678,some (fanBlockRows 59)),(4679,some (fanBlockRows 59)),(4680,some (fanBlockRows 59)),(4681,some (fanBlockRows 59)),(4682,some (fanBlockRows 59)),(4683,some (fanBlockRows 59)),(4684,some (fanBlockRows 59)),(4685,some (fanBlockRows 59)),(4686,some (fanBlockRows 59)),(4687,some (fanBlockRows 59)),(4688,some (fanBlockRows 59)),(4689,some (fanBlockRows 59)),(4690,some (fanBlockRows 59)),(4691,some (fanBlockRows 59)),(4692,some (fanBlockRows 59)),(4693,some (fanBlockRows 59)),(4694,some (fanBlockRows 59)),(4695,some (fanBlockRows 59)),(4696,some (fanBlockRows 59)),(4697,some (fanBlockRows 59)),(4698,some (fanBlockRows 59)),(4699,some (fanBlockRows 59)),(4700,some (fanBlockRows 59)),(4701,some (fanBlockRows 59)),(4702,some (fanBlockRows 59)),(4703,some (fanBlockRows 59)),(4704,some (fanBlockRows 59)),(4705,some (fanBlockRows 59)),(4706,some (fanBlockRows 59)),(4707,some (fanBlockRows 59)),(4708,some (fanBlockRows 59)),(4709,some (fanBlockRows 59)),(4710,some (fanBlockRows 59)),(4711,some (fanBlockRows 59)),(4712,some (fanBlockRows 59)),(4713,some (fanBlockRows 59)),(4714,some (fanBlockRows 59)),(4715,some (fanBlockRows 59)),(4716,some (fanBlockRows 59)),(4717,some (fanBlockRows 59)),(4718,some (fanBlockRows 59)),(4719,some (fanBlockRows 59)),(4720,some (fanBlockRows 59)),(4721,some (fanBlockRows 59)),(4722,some (fanBlockRows 59)),(4723,some (fanBlockRows 59)),(4724,some (fanBlockRows 59)),(4725,some (fanBlockRows 59)),(4726,some (fanBlockRows 59)),(4727,some (fanBlockRows 59)),(4728,some (fanBlockRows 59)),(4729,some (fanBlockRows 59)),(4730,some (fanBlockRows 59)),(4731,some (fanBlockRows 59)),(4732,some (fanBlockRows 59)),(4733,some (fanBlockRows 59)),(4734,some (fanBlockRows 1846)),(4735,some (fanBlockRows 1847)),(4736,some (fanBlockRows 1848)),(4737,some (fanBlockRows 1849)),(4738,some (fanBlockRows 1850)),(4739,some (fanBlockRows 1851))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step16.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 11).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain7_11Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step16.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step16.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain7_11Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain7_11Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step16
