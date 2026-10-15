import Compact.Cases.C713.EntryQueryBase

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def query713_128 : LocalQuery := ⟨12,0,{3},.four ⟨false,true,false⟩ fourDatum10 fourDatum10_checked⟩
theorem query713_128_checked : query713_128.Check := by decide +kernel
def query713_129 : LocalQuery := ⟨12,0,{4},.four ⟨true,true,false⟩ fourDatum5 fourDatum5_checked⟩
theorem query713_129_checked : query713_129.Check := by decide +kernel
def query713_130 : LocalQuery := ⟨12,0,{5},.four ⟨false,true,false⟩ fourDatum8 fourDatum8_checked⟩
theorem query713_130_checked : query713_130.Check := by decide +kernel
def query713_131 : LocalQuery := ⟨12,0,{7},.four ⟨false,true,false⟩ fourDatum2 fourDatum2_checked⟩
theorem query713_131_checked : query713_131.Check := by decide +kernel
def query713_132 : LocalQuery := ⟨12,0,{9},.hull ⟨(3,(457/500)),(3,(113/50)),(3,(457/500)),(3,(87/50)),(413/673),0⟩⟩
theorem query713_132_checked : query713_132.Check := by decide +kernel
def query713_133 : LocalQuery := ⟨12,2,{8},.hull ⟨(3,(457/500)),(3,(87/50)),(3,(457/500)),(3,(8/5)),(49/59),0⟩⟩
theorem query713_133_checked : query713_133.Check := by decide +kernel
def query713_134 : LocalQuery := localQuery339
theorem query713_134_checked : query713_134.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨39, by decide⟩
def query713_135 : LocalQuery := localQuery340
theorem query713_135_checked : query713_135.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨40, by decide⟩
def query713_136 : LocalQuery := localQuery341
theorem query713_136_checked : query713_136.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨41, by decide⟩
def query713_137 : LocalQuery := localQuery342
theorem query713_137_checked : query713_137.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨42, by decide⟩
def query713_138 : LocalQuery := localQuery343
theorem query713_138_checked : query713_138.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨43, by decide⟩
def query713_139 : LocalQuery := localQuery344
theorem query713_139_checked : query713_139.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨44, by decide⟩
def query713_140 : LocalQuery := localQuery345
theorem query713_140_checked : query713_140.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨45, by decide⟩
def query713_141 : LocalQuery := localQuery346
theorem query713_141_checked : query713_141.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨46, by decide⟩
def query713_142 : LocalQuery := localQuery347
theorem query713_142_checked : query713_142.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨47, by decide⟩
def query713_143 : LocalQuery := localQuery348
theorem query713_143_checked : query713_143.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨48, by decide⟩
def query713_144 : LocalQuery := localQuery349
theorem query713_144_checked : query713_144.Check :=
  c713_query_at queryChunk6 queryChunk6_checked ⟨49, by decide⟩
def query713_145 : LocalQuery := localQuery350
theorem query713_145_checked : query713_145.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨0, by decide⟩
def query713_146 : LocalQuery := localQuery351
theorem query713_146_checked : query713_146.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨1, by decide⟩
def query713_147 : LocalQuery := localQuery352
theorem query713_147_checked : query713_147.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨2, by decide⟩
def query713_148 : LocalQuery := localQuery353
theorem query713_148_checked : query713_148.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨3, by decide⟩
def query713_149 : LocalQuery := localQuery354
theorem query713_149_checked : query713_149.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨4, by decide⟩
def query713_150 : LocalQuery := localQuery355
theorem query713_150_checked : query713_150.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨5, by decide⟩
def query713_151 : LocalQuery := localQuery356
theorem query713_151_checked : query713_151.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨6, by decide⟩
def query713_152 : LocalQuery := localQuery357
theorem query713_152_checked : query713_152.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨7, by decide⟩
def query713_153 : LocalQuery := localQuery358
theorem query713_153_checked : query713_153.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨8, by decide⟩
def query713_154 : LocalQuery := localQuery359
theorem query713_154_checked : query713_154.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨9, by decide⟩
def query713_155 : LocalQuery := localQuery360
theorem query713_155_checked : query713_155.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨10, by decide⟩
def query713_156 : LocalQuery := localQuery361
theorem query713_156_checked : query713_156.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨11, by decide⟩
def query713_157 : LocalQuery := localQuery362
theorem query713_157_checked : query713_157.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨12, by decide⟩
def query713_158 : LocalQuery := localQuery363
theorem query713_158_checked : query713_158.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨13, by decide⟩
def query713_159 : LocalQuery := localQuery364
theorem query713_159_checked : query713_159.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨14, by decide⟩
def query713_160 : LocalQuery := localQuery365
theorem query713_160_checked : query713_160.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨15, by decide⟩
def query713_161 : LocalQuery := localQuery366
theorem query713_161_checked : query713_161.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨16, by decide⟩
def query713_162 : LocalQuery := localQuery367
theorem query713_162_checked : query713_162.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨17, by decide⟩
def query713_163 : LocalQuery := localQuery368
theorem query713_163_checked : query713_163.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨18, by decide⟩
def query713_164 : LocalQuery := localQuery369
theorem query713_164_checked : query713_164.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨19, by decide⟩
def query713_165 : LocalQuery := localQuery370
theorem query713_165_checked : query713_165.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨20, by decide⟩
def query713_166 : LocalQuery := localQuery371
theorem query713_166_checked : query713_166.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨21, by decide⟩
def query713_167 : LocalQuery := localQuery372
theorem query713_167_checked : query713_167.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨22, by decide⟩
def query713_168 : LocalQuery := localQuery373
theorem query713_168_checked : query713_168.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨23, by decide⟩
def query713_169 : LocalQuery := localQuery374
theorem query713_169_checked : query713_169.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨24, by decide⟩
def query713_170 : LocalQuery := localQuery375
theorem query713_170_checked : query713_170.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨25, by decide⟩
def query713_171 : LocalQuery := localQuery376
theorem query713_171_checked : query713_171.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨26, by decide⟩
def query713_172 : LocalQuery := localQuery377
theorem query713_172_checked : query713_172.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨27, by decide⟩
def query713_173 : LocalQuery := localQuery378
theorem query713_173_checked : query713_173.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨28, by decide⟩
def query713_174 : LocalQuery := localQuery379
theorem query713_174_checked : query713_174.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨29, by decide⟩
def query713_175 : LocalQuery := localQuery380
theorem query713_175_checked : query713_175.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨30, by decide⟩
def query713_176 : LocalQuery := localQuery381
theorem query713_176_checked : query713_176.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨31, by decide⟩
def query713_177 : LocalQuery := localQuery382
theorem query713_177_checked : query713_177.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨32, by decide⟩
def query713_178 : LocalQuery := localQuery383
theorem query713_178_checked : query713_178.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨33, by decide⟩
def query713_179 : LocalQuery := localQuery384
theorem query713_179_checked : query713_179.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨34, by decide⟩
def query713_180 : LocalQuery := localQuery385
theorem query713_180_checked : query713_180.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨35, by decide⟩
def query713_181 : LocalQuery := localQuery386
theorem query713_181_checked : query713_181.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨36, by decide⟩
def query713_182 : LocalQuery := localQuery387
theorem query713_182_checked : query713_182.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨37, by decide⟩
def query713_183 : LocalQuery := localQuery388
theorem query713_183_checked : query713_183.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨38, by decide⟩
def query713_184 : LocalQuery := localQuery389
theorem query713_184_checked : query713_184.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨39, by decide⟩
def query713_185 : LocalQuery := localQuery390
theorem query713_185_checked : query713_185.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨40, by decide⟩
def query713_186 : LocalQuery := localQuery391
theorem query713_186_checked : query713_186.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨41, by decide⟩
def query713_187 : LocalQuery := localQuery392
theorem query713_187_checked : query713_187.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨42, by decide⟩
def query713_188 : LocalQuery := localQuery393
theorem query713_188_checked : query713_188.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨43, by decide⟩
def query713_189 : LocalQuery := localQuery394
theorem query713_189_checked : query713_189.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨44, by decide⟩
def query713_190 : LocalQuery := localQuery395
theorem query713_190_checked : query713_190.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨45, by decide⟩
def query713_191 : LocalQuery := localQuery396
theorem query713_191_checked : query713_191.Check :=
  c713_query_at queryChunk7 queryChunk7_checked ⟨46, by decide⟩

end
end S12
