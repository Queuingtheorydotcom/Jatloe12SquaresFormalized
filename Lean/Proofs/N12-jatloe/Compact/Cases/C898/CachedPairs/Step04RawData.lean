import Compact.Cases.C898.CachedPairs.Step04Data
import Compact.Core.BoundaryFanSyntax
import Compact.Bridge.CheckedCommonFanCommand

/-! Exact materialization of the already certified Step04 contexts.
The numeric views contain no dictionary functions or proof-bearing entries.
The equalities below bind every view to its original certified context.
-/

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared
noncomputable section

def step4RawContext414 : RawSupportFan.Context :=
  materialize_raw_fan% (route414.context.numeric)
theorem step4RawContext414_exact : step4RawContext414 = route414.context.numeric := by materialized_fan_rfl

def step4RawContext415 : RawSupportFan.Context :=
  materialize_raw_fan% (route415.context.numeric)
theorem step4RawContext415_exact : step4RawContext415 = route415.context.numeric := by materialized_fan_rfl

def step4RawContext416 : RawSupportFan.Context :=
  materialize_raw_fan% (route416.context.numeric)
theorem step4RawContext416_exact : step4RawContext416 = route416.context.numeric := by materialized_fan_rfl

def step4RawContext417 : RawSupportFan.Context :=
  materialize_raw_fan% (route417.context.numeric)
theorem step4RawContext417_exact : step4RawContext417 = route417.context.numeric := by materialized_fan_rfl

def step4RawContext418 : RawSupportFan.Context :=
  materialize_raw_fan% (route418.context.numeric)
theorem step4RawContext418_exact : step4RawContext418 = route418.context.numeric := by materialized_fan_rfl

def step4RawContext419 : RawSupportFan.Context :=
  materialize_raw_fan% (route419.context.numeric)
theorem step4RawContext419_exact : step4RawContext419 = route419.context.numeric := by materialized_fan_rfl

def step4RawContext420 : RawSupportFan.Context :=
  materialize_raw_fan% (route420.context.numeric)
theorem step4RawContext420_exact : step4RawContext420 = route420.context.numeric := by materialized_fan_rfl

def step4RawSources : Fin 7 → RawSupportFan.Context := ![
  step4RawContext414, step4RawContext415, step4RawContext416, step4RawContext417, step4RawContext418, step4RawContext419, step4RawContext420]

def step4RawContext110 : RawSupportFan.Context :=
  materialize_raw_fan% (route110.context.numeric)
theorem step4RawContext110_exact : step4RawContext110 = route110.context.numeric := by materialized_fan_rfl

def step4RawContext111 : RawSupportFan.Context :=
  materialize_raw_fan% (route111.context.numeric)
theorem step4RawContext111_exact : step4RawContext111 = route111.context.numeric := by materialized_fan_rfl

def step4RawContext112 : RawSupportFan.Context :=
  materialize_raw_fan% (route112.context.numeric)
theorem step4RawContext112_exact : step4RawContext112 = route112.context.numeric := by materialized_fan_rfl

def step4RawContext113 : RawSupportFan.Context :=
  materialize_raw_fan% (route113.context.numeric)
theorem step4RawContext113_exact : step4RawContext113 = route113.context.numeric := by materialized_fan_rfl

def step4RawContext114 : RawSupportFan.Context :=
  materialize_raw_fan% (route114.context.numeric)
theorem step4RawContext114_exact : step4RawContext114 = route114.context.numeric := by materialized_fan_rfl

def step4RawContext115 : RawSupportFan.Context :=
  materialize_raw_fan% (route115.context.numeric)
theorem step4RawContext115_exact : step4RawContext115 = route115.context.numeric := by materialized_fan_rfl

def step4RawContext116 : RawSupportFan.Context :=
  materialize_raw_fan% (route116.context.numeric)
theorem step4RawContext116_exact : step4RawContext116 = route116.context.numeric := by materialized_fan_rfl

def step4RawContext117 : RawSupportFan.Context :=
  materialize_raw_fan% (route117.context.numeric)
theorem step4RawContext117_exact : step4RawContext117 = route117.context.numeric := by materialized_fan_rfl

def step4RawContext118 : RawSupportFan.Context :=
  materialize_raw_fan% (route118.context.numeric)
theorem step4RawContext118_exact : step4RawContext118 = route118.context.numeric := by materialized_fan_rfl

def step4RawContext119 : RawSupportFan.Context :=
  materialize_raw_fan% (route119.context.numeric)
theorem step4RawContext119_exact : step4RawContext119 = route119.context.numeric := by materialized_fan_rfl

def step4RawContext120 : RawSupportFan.Context :=
  materialize_raw_fan% (route120.context.numeric)
theorem step4RawContext120_exact : step4RawContext120 = route120.context.numeric := by materialized_fan_rfl

def step4RawContext121 : RawSupportFan.Context :=
  materialize_raw_fan% (route121.context.numeric)
theorem step4RawContext121_exact : step4RawContext121 = route121.context.numeric := by materialized_fan_rfl

def step4RawContext122 : RawSupportFan.Context :=
  materialize_raw_fan% (route122.context.numeric)
theorem step4RawContext122_exact : step4RawContext122 = route122.context.numeric := by materialized_fan_rfl

def step4RawContext123 : RawSupportFan.Context :=
  materialize_raw_fan% (route123.context.numeric)
theorem step4RawContext123_exact : step4RawContext123 = route123.context.numeric := by materialized_fan_rfl

def step4RawContext124 : RawSupportFan.Context :=
  materialize_raw_fan% (route124.context.numeric)
theorem step4RawContext124_exact : step4RawContext124 = route124.context.numeric := by materialized_fan_rfl

def step4RawContext125 : RawSupportFan.Context :=
  materialize_raw_fan% (route125.context.numeric)
theorem step4RawContext125_exact : step4RawContext125 = route125.context.numeric := by materialized_fan_rfl

def step4RawContext126 : RawSupportFan.Context :=
  materialize_raw_fan% (route126.context.numeric)
theorem step4RawContext126_exact : step4RawContext126 = route126.context.numeric := by materialized_fan_rfl

def step4RawContext127 : RawSupportFan.Context :=
  materialize_raw_fan% (route127.context.numeric)
theorem step4RawContext127_exact : step4RawContext127 = route127.context.numeric := by materialized_fan_rfl

def step4RawContext128 : RawSupportFan.Context :=
  materialize_raw_fan% (route128.context.numeric)
theorem step4RawContext128_exact : step4RawContext128 = route128.context.numeric := by materialized_fan_rfl

def step4RawContext129 : RawSupportFan.Context :=
  materialize_raw_fan% (route129.context.numeric)
theorem step4RawContext129_exact : step4RawContext129 = route129.context.numeric := by materialized_fan_rfl

def step4RawContext130 : RawSupportFan.Context :=
  materialize_raw_fan% (route130.context.numeric)
theorem step4RawContext130_exact : step4RawContext130 = route130.context.numeric := by materialized_fan_rfl

def step4RawContext131 : RawSupportFan.Context :=
  materialize_raw_fan% (route131.context.numeric)
theorem step4RawContext131_exact : step4RawContext131 = route131.context.numeric := by materialized_fan_rfl

def step4RawContext132 : RawSupportFan.Context :=
  materialize_raw_fan% (route132.context.numeric)
theorem step4RawContext132_exact : step4RawContext132 = route132.context.numeric := by materialized_fan_rfl

def step4RawContext133 : RawSupportFan.Context :=
  materialize_raw_fan% (route133.context.numeric)
theorem step4RawContext133_exact : step4RawContext133 = route133.context.numeric := by materialized_fan_rfl

def step4RawContext134 : RawSupportFan.Context :=
  materialize_raw_fan% (route134.context.numeric)
theorem step4RawContext134_exact : step4RawContext134 = route134.context.numeric := by materialized_fan_rfl

def step4RawContext135 : RawSupportFan.Context :=
  materialize_raw_fan% (route135.context.numeric)
theorem step4RawContext135_exact : step4RawContext135 = route135.context.numeric := by materialized_fan_rfl

def step4RawContext136 : RawSupportFan.Context :=
  materialize_raw_fan% (route136.context.numeric)
theorem step4RawContext136_exact : step4RawContext136 = route136.context.numeric := by materialized_fan_rfl

def step4RawContext137 : RawSupportFan.Context :=
  materialize_raw_fan% (route137.context.numeric)
theorem step4RawContext137_exact : step4RawContext137 = route137.context.numeric := by materialized_fan_rfl

def step4RawContext138 : RawSupportFan.Context :=
  materialize_raw_fan% (route138.context.numeric)
theorem step4RawContext138_exact : step4RawContext138 = route138.context.numeric := by materialized_fan_rfl

def step4RawContext139 : RawSupportFan.Context :=
  materialize_raw_fan% (route139.context.numeric)
theorem step4RawContext139_exact : step4RawContext139 = route139.context.numeric := by materialized_fan_rfl

def step4RawContext140 : RawSupportFan.Context :=
  materialize_raw_fan% (route140.context.numeric)
theorem step4RawContext140_exact : step4RawContext140 = route140.context.numeric := by materialized_fan_rfl

def step4RawContext141 : RawSupportFan.Context :=
  materialize_raw_fan% (route141.context.numeric)
theorem step4RawContext141_exact : step4RawContext141 = route141.context.numeric := by materialized_fan_rfl

def step4RawContext142 : RawSupportFan.Context :=
  materialize_raw_fan% (route142.context.numeric)
theorem step4RawContext142_exact : step4RawContext142 = route142.context.numeric := by materialized_fan_rfl

def step4RawContext143 : RawSupportFan.Context :=
  materialize_raw_fan% (route143.context.numeric)
theorem step4RawContext143_exact : step4RawContext143 = route143.context.numeric := by materialized_fan_rfl

def step4RawContext144 : RawSupportFan.Context :=
  materialize_raw_fan% (route144.context.numeric)
theorem step4RawContext144_exact : step4RawContext144 = route144.context.numeric := by materialized_fan_rfl

def step4RawContext145 : RawSupportFan.Context :=
  materialize_raw_fan% (route145.context.numeric)
theorem step4RawContext145_exact : step4RawContext145 = route145.context.numeric := by materialized_fan_rfl

def step4RawContext146 : RawSupportFan.Context :=
  materialize_raw_fan% (route146.context.numeric)
theorem step4RawContext146_exact : step4RawContext146 = route146.context.numeric := by materialized_fan_rfl

def step4RawContext147 : RawSupportFan.Context :=
  materialize_raw_fan% (route147.context.numeric)
theorem step4RawContext147_exact : step4RawContext147 = route147.context.numeric := by materialized_fan_rfl

def step4RawContext148 : RawSupportFan.Context :=
  materialize_raw_fan% (route148.context.numeric)
theorem step4RawContext148_exact : step4RawContext148 = route148.context.numeric := by materialized_fan_rfl

def step4RawContext149 : RawSupportFan.Context :=
  materialize_raw_fan% (route149.context.numeric)
theorem step4RawContext149_exact : step4RawContext149 = route149.context.numeric := by materialized_fan_rfl

def step4RawContext150 : RawSupportFan.Context :=
  materialize_raw_fan% (route150.context.numeric)
theorem step4RawContext150_exact : step4RawContext150 = route150.context.numeric := by materialized_fan_rfl

def step4RawContext151 : RawSupportFan.Context :=
  materialize_raw_fan% (route151.context.numeric)
theorem step4RawContext151_exact : step4RawContext151 = route151.context.numeric := by materialized_fan_rfl

def step4RawContext152 : RawSupportFan.Context :=
  materialize_raw_fan% (route152.context.numeric)
theorem step4RawContext152_exact : step4RawContext152 = route152.context.numeric := by materialized_fan_rfl

def step4RawContext153 : RawSupportFan.Context :=
  materialize_raw_fan% (route153.context.numeric)
theorem step4RawContext153_exact : step4RawContext153 = route153.context.numeric := by materialized_fan_rfl

def step4RawContext154 : RawSupportFan.Context :=
  materialize_raw_fan% (route154.context.numeric)
theorem step4RawContext154_exact : step4RawContext154 = route154.context.numeric := by materialized_fan_rfl

def step4RawContext155 : RawSupportFan.Context :=
  materialize_raw_fan% (route155.context.numeric)
theorem step4RawContext155_exact : step4RawContext155 = route155.context.numeric := by materialized_fan_rfl

def step4RawContext156 : RawSupportFan.Context :=
  materialize_raw_fan% (route156.context.numeric)
theorem step4RawContext156_exact : step4RawContext156 = route156.context.numeric := by materialized_fan_rfl

def step4RawContext157 : RawSupportFan.Context :=
  materialize_raw_fan% (route157.context.numeric)
theorem step4RawContext157_exact : step4RawContext157 = route157.context.numeric := by materialized_fan_rfl

def step4RawContext158 : RawSupportFan.Context :=
  materialize_raw_fan% (route158.context.numeric)
theorem step4RawContext158_exact : step4RawContext158 = route158.context.numeric := by materialized_fan_rfl

def step4RawContext159 : RawSupportFan.Context :=
  materialize_raw_fan% (route159.context.numeric)
theorem step4RawContext159_exact : step4RawContext159 = route159.context.numeric := by materialized_fan_rfl

def step4RawContext160 : RawSupportFan.Context :=
  materialize_raw_fan% (route160.context.numeric)
theorem step4RawContext160_exact : step4RawContext160 = route160.context.numeric := by materialized_fan_rfl

def step4RawContext161 : RawSupportFan.Context :=
  materialize_raw_fan% (route161.context.numeric)
theorem step4RawContext161_exact : step4RawContext161 = route161.context.numeric := by materialized_fan_rfl

def step4RawContext162 : RawSupportFan.Context :=
  materialize_raw_fan% (route162.context.numeric)
theorem step4RawContext162_exact : step4RawContext162 = route162.context.numeric := by materialized_fan_rfl

def step4RawContext163 : RawSupportFan.Context :=
  materialize_raw_fan% (route163.context.numeric)
theorem step4RawContext163_exact : step4RawContext163 = route163.context.numeric := by materialized_fan_rfl

def step4RawContext164 : RawSupportFan.Context :=
  materialize_raw_fan% (route164.context.numeric)
theorem step4RawContext164_exact : step4RawContext164 = route164.context.numeric := by materialized_fan_rfl

def step4RawContext165 : RawSupportFan.Context :=
  materialize_raw_fan% (route165.context.numeric)
theorem step4RawContext165_exact : step4RawContext165 = route165.context.numeric := by materialized_fan_rfl

def step4RawContext166 : RawSupportFan.Context :=
  materialize_raw_fan% (route166.context.numeric)
theorem step4RawContext166_exact : step4RawContext166 = route166.context.numeric := by materialized_fan_rfl

def step4RawContext167 : RawSupportFan.Context :=
  materialize_raw_fan% (route167.context.numeric)
theorem step4RawContext167_exact : step4RawContext167 = route167.context.numeric := by materialized_fan_rfl

def step4RawContext168 : RawSupportFan.Context :=
  materialize_raw_fan% (route168.context.numeric)
theorem step4RawContext168_exact : step4RawContext168 = route168.context.numeric := by materialized_fan_rfl

def step4RawContext169 : RawSupportFan.Context :=
  materialize_raw_fan% (route169.context.numeric)
theorem step4RawContext169_exact : step4RawContext169 = route169.context.numeric := by materialized_fan_rfl

def step4RawContext170 : RawSupportFan.Context :=
  materialize_raw_fan% (route170.context.numeric)
theorem step4RawContext170_exact : step4RawContext170 = route170.context.numeric := by materialized_fan_rfl

def step4RawContext171 : RawSupportFan.Context :=
  materialize_raw_fan% (route171.context.numeric)
theorem step4RawContext171_exact : step4RawContext171 = route171.context.numeric := by materialized_fan_rfl

def step4RawContext172 : RawSupportFan.Context :=
  materialize_raw_fan% (route172.context.numeric)
theorem step4RawContext172_exact : step4RawContext172 = route172.context.numeric := by materialized_fan_rfl

def step4RawContext173 : RawSupportFan.Context :=
  materialize_raw_fan% (route173.context.numeric)
theorem step4RawContext173_exact : step4RawContext173 = route173.context.numeric := by materialized_fan_rfl

def step4RawNeighbors : Fin 64 → RawSupportFan.Context := ![
  step4RawContext110, step4RawContext111, step4RawContext112, step4RawContext113, step4RawContext114, step4RawContext115, step4RawContext116, step4RawContext117, step4RawContext118, step4RawContext119, step4RawContext120, step4RawContext121, step4RawContext122, step4RawContext123, step4RawContext124, step4RawContext125, step4RawContext126, step4RawContext127, step4RawContext128, step4RawContext129, step4RawContext130, step4RawContext131, step4RawContext132, step4RawContext133, step4RawContext134, step4RawContext135, step4RawContext136, step4RawContext137, step4RawContext138, step4RawContext139, step4RawContext140, step4RawContext141, step4RawContext142, step4RawContext143, step4RawContext144, step4RawContext145, step4RawContext146, step4RawContext147, step4RawContext148, step4RawContext149, step4RawContext150, step4RawContext151, step4RawContext152, step4RawContext153, step4RawContext154, step4RawContext155, step4RawContext156, step4RawContext157, step4RawContext158, step4RawContext159, step4RawContext160, step4RawContext161, step4RawContext162, step4RawContext163, step4RawContext164, step4RawContext165, step4RawContext166, step4RawContext167, step4RawContext168, step4RawContext169, step4RawContext170, step4RawContext171, step4RawContext172, step4RawContext173]

def step4RawSourceAngle (i : Fin 7) : Fin 64 := ⟨6 + i.val, by omega⟩

theorem step4RawSources_exact (i : Fin 7) :
    step4RawSources i = (step4Sources i).context.numeric := by
  fin_cases i
  · exact step4RawContext414_exact
  · exact step4RawContext415_exact
  · exact step4RawContext416_exact
  · exact step4RawContext417_exact
  · exact step4RawContext418_exact
  · exact step4RawContext419_exact
  · exact step4RawContext420_exact

theorem step4RawNeighbors_exact (j : Fin 64) :
    step4RawNeighbors j = (step4Neighbors j).context.numeric := by
  fin_cases j
  · exact step4RawContext110_exact
  · exact step4RawContext111_exact
  · exact step4RawContext112_exact
  · exact step4RawContext113_exact
  · exact step4RawContext114_exact
  · exact step4RawContext115_exact
  · exact step4RawContext116_exact
  · exact step4RawContext117_exact
  · exact step4RawContext118_exact
  · exact step4RawContext119_exact
  · exact step4RawContext120_exact
  · exact step4RawContext121_exact
  · exact step4RawContext122_exact
  · exact step4RawContext123_exact
  · exact step4RawContext124_exact
  · exact step4RawContext125_exact
  · exact step4RawContext126_exact
  · exact step4RawContext127_exact
  · exact step4RawContext128_exact
  · exact step4RawContext129_exact
  · exact step4RawContext130_exact
  · exact step4RawContext131_exact
  · exact step4RawContext132_exact
  · exact step4RawContext133_exact
  · exact step4RawContext134_exact
  · exact step4RawContext135_exact
  · exact step4RawContext136_exact
  · exact step4RawContext137_exact
  · exact step4RawContext138_exact
  · exact step4RawContext139_exact
  · exact step4RawContext140_exact
  · exact step4RawContext141_exact
  · exact step4RawContext142_exact
  · exact step4RawContext143_exact
  · exact step4RawContext144_exact
  · exact step4RawContext145_exact
  · exact step4RawContext146_exact
  · exact step4RawContext147_exact
  · exact step4RawContext148_exact
  · exact step4RawContext149_exact
  · exact step4RawContext150_exact
  · exact step4RawContext151_exact
  · exact step4RawContext152_exact
  · exact step4RawContext153_exact
  · exact step4RawContext154_exact
  · exact step4RawContext155_exact
  · exact step4RawContext156_exact
  · exact step4RawContext157_exact
  · exact step4RawContext158_exact
  · exact step4RawContext159_exact
  · exact step4RawContext160_exact
  · exact step4RawContext161_exact
  · exact step4RawContext162_exact
  · exact step4RawContext163_exact
  · exact step4RawContext164_exact
  · exact step4RawContext165_exact
  · exact step4RawContext166_exact
  · exact step4RawContext167_exact
  · exact step4RawContext168_exact
  · exact step4RawContext169_exact
  · exact step4RawContext170_exact
  · exact step4RawContext171_exact
  · exact step4RawContext172_exact
  · exact step4RawContext173_exact

theorem step4RawSourceAngle_exact (i : Fin 7) :
    step4RawSourceAngle i = (step4Sources i).keyAngle := by
  fin_cases i <;> rfl

theorem step4RawNeighborAngle_exact (j : Fin 64) :
    j = (step4Neighbors j).keyAngle := by
  fin_cases j <;> rfl

def step4RawPairCheck (i : Fin 7) (j : Fin 64) : Prop :=
  RawSupportFan.PairCheck (step4RawSources i) (step4RawNeighbors j)
    (fanDirectionKey (step4RawSourceAngle i) j) (fun key => (key + 128) % 256)

instance (i : Fin 7) (j : Fin 64) : Decidable (step4RawPairCheck i j) :=
  inferInstanceAs (Decidable (RawSupportFan.PairCheck _ _ _ _))

end
end N12Compact.C898Cached.AllPairs
