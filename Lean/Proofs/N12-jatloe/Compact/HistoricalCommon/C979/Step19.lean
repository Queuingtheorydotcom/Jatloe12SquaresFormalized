import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step19
import Compact.HistoricalCommon.C979.Step19Groups00

namespace N12Compact.HistoricalCommon.C979.Step19
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0]

def scopes : List Scope :=
  [group0_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  .leaf

theorem partition_checked : partition.Check ⟨0,128,0,27⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 27) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 27) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11079_header,context11145_header,context11156_header,context11172_header,context11193_header,context11214_header,context11233_header,context11244_header,context11255_header,context11266_header,context11117_header,context11128_header,context11137_header,context11138_header,context11139_header,context11140_header,context11141_header,context11142_header,context11143_header,context11144_header,context11146_header,context11147_header,context11148_header,context11149_header,context11150_header,context11151_header,context11152_header,context11153_header,context11154_header,context11155_header,context11157_header,context11158_header,context11159_header,context11160_header,context11161_header,context11163_header,context11165_header,context11167_header,context11169_header,context11171_header,context11174_header,context11176_header,context11178_header,context11180_header,context11182_header,context11184_header,context11186_header,context11188_header,context11190_header,context11192_header,context11195_header,context11197_header,context11199_header,context11201_header,context11203_header,context11205_header,context11207_header,context11209_header,context11211_header,context11213_header,context11216_header,context11218_header,context11220_header,context11222_header,context11224_header,context11226_header,context11228_header,context11230_header,context11231_header,context11232_header,context11234_header,context11235_header,context11236_header,context11237_header,context11238_header,context11239_header,context11240_header,context11241_header,context11242_header,context11243_header,context11245_header,context11246_header,context11247_header,context11248_header,context11249_header,context11250_header,context11251_header,context11252_header,context11253_header,context11254_header,context11256_header,context11257_header,context11258_header,context11259_header,context11260_header,context11261_header,context11262_header,context11263_header,context11264_header,context11265_header,context11107_header,context11108_header,context11109_header,context11110_header,context11111_header,context11112_header,context11113_header,context11114_header,context11115_header,context11116_header,context11118_header,context11119_header,context11120_header,context11121_header,context11122_header,context11123_header,context11124_header,context11125_header,context11126_header,context11127_header,context11129_header,context11130_header,context11131_header,context11132_header,context11133_header,context11134_header,context11135_header,context11136_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(9956,some (fanBlockRows 4652)),(9957,some (fanBlockRows 4691)),(9958,some (fanBlockRows 4702)),(9959,some (fanBlockRows 4708)),(9960,some (fanBlockRows 4709)),(9961,some (fanBlockRows 4710)),(9962,some (fanBlockRows 4713)),(9963,some (fanBlockRows 4724)),(9964,some (fanBlockRows 4735)),(9965,some (fanBlockRows 4746)),(9966,some (fanBlockRows 4663)),(9967,some (fanBlockRows 4674)),(9968,some (fanBlockRows 4683)),(9969,some (fanBlockRows 4684)),(9970,some (fanBlockRows 4685)),(9971,some (fanBlockRows 4686)),(9972,some (fanBlockRows 4687)),(9973,some (fanBlockRows 4688)),(9974,some (fanBlockRows 4689)),(9975,some (fanBlockRows 4690)),(9976,some (fanBlockRows 4692)),(9977,some (fanBlockRows 4693)),(9978,some (fanBlockRows 4694)),(9979,some (fanBlockRows 4695)),(9980,some (fanBlockRows 4696)),(9981,some (fanBlockRows 4697)),(9982,some (fanBlockRows 4698)),(9983,some (fanBlockRows 4699)),(9984,some (fanBlockRows 4700)),(9985,some (fanBlockRows 4701)),(9986,some (fanBlockRows 4703)),(9987,some (fanBlockRows 4704)),(9988,some (fanBlockRows 4705)),(9989,some (fanBlockRows 4706)),(9990,some (fanBlockRows 4707)),(9991,some (fanBlockRows 59)),(9992,some (fanBlockRows 59)),(9993,some (fanBlockRows 59)),(9994,some (fanBlockRows 59)),(9995,some (fanBlockRows 59)),(9996,some (fanBlockRows 59)),(9997,some (fanBlockRows 59)),(9998,some (fanBlockRows 59)),(9999,some (fanBlockRows 59)),(10000,some (fanBlockRows 59)),(10001,some (fanBlockRows 59)),(10002,some (fanBlockRows 59)),(10003,some (fanBlockRows 59)),(10004,some (fanBlockRows 59)),(10005,some (fanBlockRows 59)),(10006,some (fanBlockRows 59)),(10007,some (fanBlockRows 59)),(10008,some (fanBlockRows 59)),(10009,some (fanBlockRows 59)),(10010,some (fanBlockRows 59)),(10011,some (fanBlockRows 59)),(10012,some (fanBlockRows 59)),(10013,some (fanBlockRows 59)),(10014,some (fanBlockRows 59)),(10015,some (fanBlockRows 59)),(10016,some (fanBlockRows 59)),(10017,some (fanBlockRows 59)),(10018,some (fanBlockRows 59)),(10019,some (fanBlockRows 59)),(10020,some (fanBlockRows 59)),(10021,some (fanBlockRows 59)),(10022,some (fanBlockRows 59)),(10023,some (fanBlockRows 59)),(10024,some (fanBlockRows 4711)),(10025,some (fanBlockRows 4712)),(10026,some (fanBlockRows 4714)),(10027,some (fanBlockRows 4715)),(10028,some (fanBlockRows 4716)),(10029,some (fanBlockRows 4717)),(10030,some (fanBlockRows 4718)),(10031,some (fanBlockRows 4719)),(10032,some (fanBlockRows 4720)),(10033,some (fanBlockRows 4721)),(10034,some (fanBlockRows 4722)),(10035,some (fanBlockRows 4723)),(10036,some (fanBlockRows 4725)),(10037,some (fanBlockRows 4726)),(10038,some (fanBlockRows 4727)),(10039,some (fanBlockRows 4728)),(10040,some (fanBlockRows 4729)),(10041,some (fanBlockRows 4730)),(10042,some (fanBlockRows 4731)),(10043,some (fanBlockRows 4732)),(10044,some (fanBlockRows 4733)),(10045,some (fanBlockRows 4734)),(10046,some (fanBlockRows 4736)),(10047,some (fanBlockRows 4737)),(10048,some (fanBlockRows 4738)),(10049,some (fanBlockRows 4739)),(10050,some (fanBlockRows 4740)),(10051,some (fanBlockRows 4741)),(10052,some (fanBlockRows 4742)),(10053,some (fanBlockRows 4743)),(10054,some (fanBlockRows 4744)),(10055,some (fanBlockRows 4745)),(10056,some (fanBlockRows 4653)),(10057,some (fanBlockRows 4654)),(10058,some (fanBlockRows 4655)),(10059,some (fanBlockRows 4656)),(10060,some (fanBlockRows 4657)),(10061,some (fanBlockRows 4658)),(10062,some (fanBlockRows 4659)),(10063,some (fanBlockRows 4660)),(10064,some (fanBlockRows 4661)),(10065,some (fanBlockRows 4662)),(10066,some (fanBlockRows 4664)),(10067,some (fanBlockRows 4665)),(10068,some (fanBlockRows 4666)),(10069,some (fanBlockRows 4667)),(10070,some (fanBlockRows 4668)),(10071,some (fanBlockRows 4669)),(10072,some (fanBlockRows 4670)),(10073,some (fanBlockRows 4671)),(10074,some (fanBlockRows 4672)),(10075,some (fanBlockRows 4673)),(10076,some (fanBlockRows 4675)),(10077,some (fanBlockRows 4676)),(10078,some (fanBlockRows 4677)),(10079,some (fanBlockRows 4678)),(10080,some (fanBlockRows 4679)),(10081,some (fanBlockRows 4680)),(10082,some (fanBlockRows 4681)),(10083,some (fanBlockRows 4682))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step19.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 27).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain11_19Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step19.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step19.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain11_19Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain11_19Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step19
