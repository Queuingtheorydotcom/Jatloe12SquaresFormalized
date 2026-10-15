import Compact.Bridge.C981DomainReuse.Queries00
import Compact.Bridge.C981DomainReuse.Queries01
import Compact.Bridge.C981DomainReuse.Queries02
import Compact.Bridge.C981DomainReuse.Queries03
import Compact.Bridge.C981DomainReuse.Queries04
import Compact.Bridge.C981DomainReuse.Queries05
import Compact.Bridge.C981DomainReuse.Queries06
import Compact.Bridge.C981DomainReuse.Queries07
import Compact.Bridge.C981DomainReuse.Queries08
import Compact.Bridge.SmallOwnerDomain

/-! The unchanged direct domains selected by C981. Exact signatures
are checked over all cardinality-at-most-two labels; the symbolic
SmallOwnerDomain theorem recovers the original full statement. -/
namespace N12Compact.C981DomainSubset
open S12 S12Pilot
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section

def case976Family : Finset Nat := {1,2,12,48,192,256,512,1024,6144,8192,16384,32768}
def single976_2_0 : DirectSingleDomain := ⟨12,0,1,[∅,{6},{8}],[⟨query976_214,query976_214_checked⟩,⟨query976_215,query976_215_checked⟩,⟨query976_216,query976_216_checked⟩,⟨query976_217,query976_217_checked⟩,⟨query976_218,query976_218_checked⟩,⟨query976_219,query976_219_checked⟩,⟨query976_220,query976_220_checked⟩,⟨query976_221,query976_221_checked⟩]⟩
def single976_2_0_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,0,{0}),(12,0,{1}),(12,0,{2}),(12,0,{3}),(12,0,{4}),(12,0,{5}),(12,0,{7}),(12,0,{9})]
theorem single976_2_0_checked : single976_2_0.Check case976Family 0 := by
  apply N12Compact.SmallOwnerDomain.checked single976_2_0 case976Family 0
    single976_2_0_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_2_1 : DirectSingleDomain := ⟨12,0,1,[∅,{5},{8}],[⟨query976_222,query976_222_checked⟩,⟨query976_223,query976_223_checked⟩,⟨query976_224,query976_224_checked⟩,⟨query976_225,query976_225_checked⟩,⟨query976_226,query976_226_checked⟩,⟨query976_227,query976_227_checked⟩,⟨query976_228,query976_228_checked⟩,⟨query976_229,query976_229_checked⟩]⟩
def single976_2_1_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,1,{0}),(12,1,{1}),(12,1,{2}),(12,1,{3}),(12,1,{4}),(12,1,{6}),(12,1,{7}),(12,1,{9})]
theorem single976_2_1_checked : single976_2_1.Check case976Family 1 := by
  apply N12Compact.SmallOwnerDomain.checked single976_2_1 case976Family 1
    single976_2_1_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_3_0 : DirectSingleDomain := ⟨48,0,1,[∅,{7},{9}],[⟨query976_233,query976_233_checked⟩,⟨query976_234,query976_234_checked⟩,⟨query976_235,query976_235_checked⟩,⟨query976_236,query976_236_checked⟩,⟨query976_237,query976_237_checked⟩,⟨query976_238,query976_238_checked⟩,⟨query976_239,query976_239_checked⟩,⟨query976_240,query976_240_checked⟩]⟩
def single976_3_0_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(48,0,{0}),(48,0,{1}),(48,0,{2}),(48,0,{3}),(48,0,{4}),(48,0,{5}),(48,0,{6}),(48,0,{8})]
theorem single976_3_0_checked : single976_3_0.Check case976Family 0 := by
  apply N12Compact.SmallOwnerDomain.checked single976_3_0 case976Family 0
    single976_3_0_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_3_1 : DirectSingleDomain := ⟨48,0,1,[∅,{7},{9}],[⟨query976_241,query976_241_checked⟩,⟨query976_242,query976_242_checked⟩,⟨query976_243,query976_243_checked⟩,⟨query976_244,query976_244_checked⟩,⟨query976_245,query976_245_checked⟩,⟨query976_246,query976_246_checked⟩,⟨query976_247,query976_247_checked⟩,⟨query976_248,query976_248_checked⟩]⟩
def single976_3_1_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(48,1,{0}),(48,1,{1}),(48,1,{2}),(48,1,{3}),(48,1,{4}),(48,1,{5}),(48,1,{6}),(48,1,{8})]
theorem single976_3_1_checked : single976_3_1.Check case976Family 1 := by
  apply N12Compact.SmallOwnerDomain.checked single976_3_1 case976Family 1
    single976_3_1_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_4_0 : DirectSingleDomain := ⟨192,0,1,[∅,{1},{3}],[⟨query976_252,query976_252_checked⟩,⟨query976_253,query976_253_checked⟩,⟨query976_254,query976_254_checked⟩,⟨query976_255,query976_255_checked⟩,⟨query976_256,query976_256_checked⟩,⟨query976_257,query976_257_checked⟩,⟨query976_258,query976_258_checked⟩,⟨query976_259,query976_259_checked⟩]⟩
def single976_4_0_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,0,{0}),(192,0,{2}),(192,0,{4}),(192,0,{5}),(192,0,{6}),(192,0,{7}),(192,0,{8}),(192,0,{9})]
theorem single976_4_0_checked : single976_4_0.Check case976Family 0 := by
  apply N12Compact.SmallOwnerDomain.checked single976_4_0 case976Family 0
    single976_4_0_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_4_1 : DirectSingleDomain := ⟨192,0,1,[∅,{1},{4}],[⟨query976_260,query976_260_checked⟩,⟨query976_261,query976_261_checked⟩,⟨query976_262,query976_262_checked⟩,⟨query976_263,query976_263_checked⟩,⟨query976_264,query976_264_checked⟩,⟨query976_265,query976_265_checked⟩,⟨query976_266,query976_266_checked⟩,⟨query976_267,query976_267_checked⟩]⟩
def single976_4_1_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,1,{0}),(192,1,{2}),(192,1,{3}),(192,1,{5}),(192,1,{6}),(192,1,{7}),(192,1,{8}),(192,1,{9})]
theorem single976_4_1_checked : single976_4_1.Check case976Family 1 := by
  apply N12Compact.SmallOwnerDomain.checked single976_4_1 case976Family 1
    single976_4_1_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_7_0 : DirectSingleDomain := ⟨1024,1,2,[{5},{3,5},{4,5},{7},{5,7},{5,8},{9},{4,9},{5,9},{7,9},{8,9}],[⟨query976_561,query976_561_checked⟩,⟨query976_562,query976_562_checked⟩,⟨query976_563,query976_563_checked⟩,⟨query976_564,query976_564_checked⟩,⟨query976_565,query976_565_checked⟩,⟨query976_566,query976_566_checked⟩,⟨query976_567,query976_567_checked⟩,⟨query976_568,query976_568_checked⟩,⟨query976_569,query976_569_checked⟩,⟨query976_570,query976_570_checked⟩,⟨query976_571,query976_571_checked⟩,⟨query976_572,query976_572_checked⟩,⟨query976_573,query976_573_checked⟩,⟨query976_574,query976_574_checked⟩,⟨query976_575,query976_575_checked⟩,⟨query976_576,query976_576_checked⟩,⟨query976_577,query976_577_checked⟩,⟨query976_578,query976_578_checked⟩,⟨query976_579,query976_579_checked⟩,⟨query976_580,query976_580_checked⟩,⟨query976_581,query976_581_checked⟩,⟨query976_582,query976_582_checked⟩,⟨query976_583,query976_583_checked⟩,⟨query976_584,query976_584_checked⟩,⟨query976_585,query976_585_checked⟩,⟨query976_586,query976_586_checked⟩,⟨query976_587,query976_587_checked⟩,⟨query976_588,query976_588_checked⟩,⟨query976_589,query976_589_checked⟩,⟨query976_590,query976_590_checked⟩,⟨query976_591,query976_591_checked⟩,⟨query976_592,query976_592_checked⟩,⟨query976_593,query976_593_checked⟩,⟨query976_594,query976_594_checked⟩,⟨query976_595,query976_595_checked⟩,⟨query976_596,query976_596_checked⟩,⟨query976_597,query976_597_checked⟩,⟨query976_598,query976_598_checked⟩,⟨query976_599,query976_599_checked⟩,⟨query976_600,query976_600_checked⟩,⟨query976_601,query976_601_checked⟩,⟨query976_602,query976_602_checked⟩,⟨query976_603,query976_603_checked⟩,⟨query976_604,query976_604_checked⟩]⟩
def single976_7_0_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1024,0,{0}),(1024,0,{1}),(1024,0,{0,1}),(1024,0,{2}),(1024,0,{0,2}),(1024,0,{1,2}),(1024,0,{3}),(1024,0,{0,3}),(1024,0,{1,3}),(1024,0,{2,3}),(1024,0,{4}),(1024,0,{0,4}),(1024,0,{1,4}),(1024,0,{2,4}),(1024,0,{3,4}),(1024,0,{0,5}),(1024,0,{1,5}),(1024,0,{2,5}),(1024,0,{6}),(1024,0,{0,6}),(1024,0,{1,6}),(1024,0,{2,6}),(1024,0,{3,6}),(1024,0,{4,6}),(1024,0,{5,6}),(1024,0,{0,7}),(1024,0,{1,7}),(1024,0,{2,7}),(1024,0,{3,7}),(1024,0,{4,7}),(1024,0,{6,7}),(1024,0,{8}),(1024,0,{0,8}),(1024,0,{1,8}),(1024,0,{2,8}),(1024,0,{3,8}),(1024,0,{4,8}),(1024,0,{6,8}),(1024,0,{7,8}),(1024,0,{0,9}),(1024,0,{1,9}),(1024,0,{2,9}),(1024,0,{3,9}),(1024,0,{6,9})]
theorem single976_7_0_checked : single976_7_0.Check case976Family 0 := by
  apply N12Compact.SmallOwnerDomain.checked single976_7_0 case976Family 0
    single976_7_0_signatures
  · rfl
  · decide +kernel
  · decide +kernel

def single976_7_1 : DirectSingleDomain := ⟨1024,1,2,[{6},{3,6},{4,6},{7},{3,7},{4,7},{6,7},{6,8},{9},{6,9},{7,9}],[⟨query976_605,query976_605_checked⟩,⟨query976_606,query976_606_checked⟩,⟨query976_607,query976_607_checked⟩,⟨query976_608,query976_608_checked⟩,⟨query976_609,query976_609_checked⟩,⟨query976_610,query976_610_checked⟩,⟨query976_611,query976_611_checked⟩,⟨query976_612,query976_612_checked⟩,⟨query976_613,query976_613_checked⟩,⟨query976_614,query976_614_checked⟩,⟨query976_615,query976_615_checked⟩,⟨query976_616,query976_616_checked⟩,⟨query976_617,query976_617_checked⟩,⟨query976_618,query976_618_checked⟩,⟨query976_619,query976_619_checked⟩,⟨query976_620,query976_620_checked⟩,⟨query976_621,query976_621_checked⟩,⟨query976_622,query976_622_checked⟩,⟨query976_623,query976_623_checked⟩,⟨query976_624,query976_624_checked⟩,⟨query976_625,query976_625_checked⟩,⟨query976_626,query976_626_checked⟩,⟨query976_627,query976_627_checked⟩,⟨query976_628,query976_628_checked⟩,⟨query976_629,query976_629_checked⟩,⟨query976_630,query976_630_checked⟩,⟨query976_631,query976_631_checked⟩,⟨query976_632,query976_632_checked⟩,⟨query976_633,query976_633_checked⟩,⟨query976_634,query976_634_checked⟩,⟨query976_635,query976_635_checked⟩,⟨query976_636,query976_636_checked⟩,⟨query976_637,query976_637_checked⟩,⟨query976_638,query976_638_checked⟩,⟨query976_639,query976_639_checked⟩,⟨query976_640,query976_640_checked⟩,⟨query976_641,query976_641_checked⟩,⟨query976_642,query976_642_checked⟩,⟨query976_643,query976_643_checked⟩,⟨query976_644,query976_644_checked⟩,⟨query976_645,query976_645_checked⟩,⟨query976_646,query976_646_checked⟩,⟨query976_647,query976_647_checked⟩,⟨query976_648,query976_648_checked⟩]⟩
def single976_7_1_signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1024,1,{0}),(1024,1,{1}),(1024,1,{0,1}),(1024,1,{2}),(1024,1,{0,2}),(1024,1,{1,2}),(1024,1,{3}),(1024,1,{0,3}),(1024,1,{1,3}),(1024,1,{2,3}),(1024,1,{4}),(1024,1,{0,4}),(1024,1,{1,4}),(1024,1,{2,4}),(1024,1,{3,4}),(1024,1,{5}),(1024,1,{0,5}),(1024,1,{1,5}),(1024,1,{2,5}),(1024,1,{3,5}),(1024,1,{4,5}),(1024,1,{0,6}),(1024,1,{1,6}),(1024,1,{2,6}),(1024,1,{5,6}),(1024,1,{0,7}),(1024,1,{1,7}),(1024,1,{2,7}),(1024,1,{5,7}),(1024,1,{8}),(1024,1,{0,8}),(1024,1,{1,8}),(1024,1,{2,8}),(1024,1,{3,8}),(1024,1,{4,8}),(1024,1,{5,8}),(1024,1,{7,8}),(1024,1,{0,9}),(1024,1,{1,9}),(1024,1,{2,9}),(1024,1,{3,9}),(1024,1,{4,9}),(1024,1,{5,9}),(1024,1,{8,9})]
theorem single976_7_1_checked : single976_7_1.Check case976Family 1 := by
  apply N12Compact.SmallOwnerDomain.checked single976_7_1 case976Family 1
    single976_7_1_signatures
  · rfl
  · decide +kernel
  · decide +kernel

#print axioms single976_7_0_checked
#print axioms single976_7_1_checked
end
end N12Compact.C981DomainSubset
