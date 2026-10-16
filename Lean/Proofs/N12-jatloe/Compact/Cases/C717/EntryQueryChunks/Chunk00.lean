import Compact.Core.FiniteKernelDecision
import Compact.Bridge.SharedLocalQueries
import Compact.Cases.C717.EntryQueryBase
import Compact.HistoricalOwnership.Queries004
import Compact.HistoricalOwnership.Queries005
import Compact.HistoricalOwnership.Queries006
import Compact.HistoricalOwnership.Queries007
import Compact.HistoricalOwnership.Queries008
import Compact.HistoricalOwnership.Queries009
import Compact.HistoricalOwnership.Queries010
import Compact.HistoricalOwnership.Queries011
import Compact.HistoricalOwnership.Queries012
import Compact.HistoricalOwnership.Queries013
import Compact.HistoricalOwnership.Queries014
import Compact.HistoricalOwnership.Queries015
import Compact.HistoricalOwnership.Queries016
import Compact.HistoricalOwnership.Queries017
import Compact.HistoricalOwnership.Queries018
import Compact.HistoricalOwnership.Queries019
import Compact.HistoricalOwnership.Queries020
import Compact.HistoricalOwnership.Queries021
import Compact.HistoricalOwnership.Queries022
import Compact.HistoricalOwnership.Queries023
import Compact.HistoricalOwnership.Queries024
import Compact.HistoricalOwnership.Queries025
import Compact.HistoricalOwnership.Queries026
import Compact.HistoricalOwnership.Queries027
import Compact.HistoricalOwnership.Queries028
import Compact.HistoricalOwnership.Queries029
import Compact.HistoricalOwnership.Queries030
import Compact.HistoricalOwnership.Queries031
import Compact.HistoricalOwnership.Queries032
import Compact.HistoricalOwnership.Queries033
import Compact.HistoricalOwnership.Queries034
import Compact.HistoricalOwnership.Queries035
import Compact.HistoricalOwnership.Queries036
import Compact.HistoricalOwnership.Queries037
import Compact.HistoricalOwnership.Queries038
import Compact.HistoricalOwnership.Queries039
import Compact.HistoricalOwnership.Queries040
import Compact.HistoricalOwnership.Queries041
import Compact.HistoricalOwnership.Queries042
import Compact.HistoricalOwnership.Queries043
import Compact.Bridge.SmallOwnerDomainThree

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single717_0_0 : DirectSingleDomain := ⟨1,1,1,[{2}],[(certified_query% 0),(certified_query% 1),(certified_query% 5),(certified_query% 9),(certified_query% 14),(certified_query% 20),(certified_query% 27),(certified_query% 35),(certified_query% 44)]⟩
private def single717_0_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,0,{0}),(1,0,{1}),(1,0,{3}),(1,0,{4}),(1,0,{5}),(1,0,{6}),(1,0,{7}),(1,0,{8}),(1,0,{9})]
theorem single717_0_0_checked : single717_0_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_0_0 case717Family 0
    single717_0_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_0_1 : DirectSingleDomain := ⟨1,1,3,[{2},{0,2}],[(certified_query% 54),(certified_query% 55),(certified_query% 56),(certified_query% 57),N12Compact.HistoricalOwnership.Queries.query146_certified,(certified_query% 58),(certified_query% 59),(certified_query% 60),N12Compact.HistoricalOwnership.Queries.query147_certified,(certified_query% 61),N12Compact.HistoricalOwnership.Queries.query148_certified,N12Compact.HistoricalOwnership.Queries.query149_certified,(certified_query% 62),(certified_query% 63),(certified_query% 64),N12Compact.HistoricalOwnership.Queries.query150_certified,(certified_query% 65),N12Compact.HistoricalOwnership.Queries.query151_certified,N12Compact.HistoricalOwnership.Queries.query152_certified,(certified_query% 66),N12Compact.HistoricalOwnership.Queries.query153_certified,N12Compact.HistoricalOwnership.Queries.query154_certified,N12Compact.HistoricalOwnership.Queries.query155_certified,(certified_query% 67),(certified_query% 68),(certified_query% 69),N12Compact.HistoricalOwnership.Queries.query156_certified,(certified_query% 70),N12Compact.HistoricalOwnership.Queries.query157_certified,N12Compact.HistoricalOwnership.Queries.query158_certified,(certified_query% 71),N12Compact.HistoricalOwnership.Queries.query159_certified,N12Compact.HistoricalOwnership.Queries.query160_certified,N12Compact.HistoricalOwnership.Queries.query161_certified,(certified_query% 72),N12Compact.HistoricalOwnership.Queries.query162_certified,N12Compact.HistoricalOwnership.Queries.query163_certified,N12Compact.HistoricalOwnership.Queries.query164_certified,N12Compact.HistoricalOwnership.Queries.query165_certified,(certified_query% 73),(certified_query% 74),(certified_query% 75),N12Compact.HistoricalOwnership.Queries.query166_certified,(certified_query% 76),N12Compact.HistoricalOwnership.Queries.query167_certified,N12Compact.HistoricalOwnership.Queries.query168_certified,(certified_query% 77),N12Compact.HistoricalOwnership.Queries.query169_certified,N12Compact.HistoricalOwnership.Queries.query170_certified,N12Compact.HistoricalOwnership.Queries.query171_certified,(certified_query% 78),N12Compact.HistoricalOwnership.Queries.query172_certified,N12Compact.HistoricalOwnership.Queries.query173_certified,N12Compact.HistoricalOwnership.Queries.query174_certified,N12Compact.HistoricalOwnership.Queries.query175_certified,(certified_query% 79),N12Compact.HistoricalOwnership.Queries.query176_certified,N12Compact.HistoricalOwnership.Queries.query177_certified,N12Compact.HistoricalOwnership.Queries.query178_certified,N12Compact.HistoricalOwnership.Queries.query179_certified,N12Compact.HistoricalOwnership.Queries.query180_certified,(certified_query% 80),(certified_query% 81),(certified_query% 82),N12Compact.HistoricalOwnership.Queries.query181_certified,(certified_query% 83),N12Compact.HistoricalOwnership.Queries.query182_certified,N12Compact.HistoricalOwnership.Queries.query183_certified,(certified_query% 84),N12Compact.HistoricalOwnership.Queries.query184_certified,N12Compact.HistoricalOwnership.Queries.query185_certified,N12Compact.HistoricalOwnership.Queries.query186_certified,(certified_query% 85),N12Compact.HistoricalOwnership.Queries.query187_certified,N12Compact.HistoricalOwnership.Queries.query188_certified,N12Compact.HistoricalOwnership.Queries.query189_certified,N12Compact.HistoricalOwnership.Queries.query190_certified,(certified_query% 86),N12Compact.HistoricalOwnership.Queries.query191_certified,N12Compact.HistoricalOwnership.Queries.query192_certified,N12Compact.HistoricalOwnership.Queries.query193_certified,N12Compact.HistoricalOwnership.Queries.query194_certified,N12Compact.HistoricalOwnership.Queries.query195_certified,(certified_query% 87),N12Compact.HistoricalOwnership.Queries.query196_certified,N12Compact.HistoricalOwnership.Queries.query197_certified,N12Compact.HistoricalOwnership.Queries.query198_certified,N12Compact.HistoricalOwnership.Queries.query199_certified,N12Compact.HistoricalOwnership.Queries.query200_certified,N12Compact.HistoricalOwnership.Queries.query201_certified,(certified_query% 88),(certified_query% 89),(certified_query% 90),N12Compact.HistoricalOwnership.Queries.query202_certified,(certified_query% 91),N12Compact.HistoricalOwnership.Queries.query203_certified,N12Compact.HistoricalOwnership.Queries.query204_certified,(certified_query% 92),N12Compact.HistoricalOwnership.Queries.query205_certified,N12Compact.HistoricalOwnership.Queries.query206_certified,N12Compact.HistoricalOwnership.Queries.query207_certified,(certified_query% 93),N12Compact.HistoricalOwnership.Queries.query208_certified,N12Compact.HistoricalOwnership.Queries.query209_certified,N12Compact.HistoricalOwnership.Queries.query210_certified,N12Compact.HistoricalOwnership.Queries.query211_certified,(certified_query% 94),N12Compact.HistoricalOwnership.Queries.query212_certified,N12Compact.HistoricalOwnership.Queries.query213_certified,N12Compact.HistoricalOwnership.Queries.query214_certified,N12Compact.HistoricalOwnership.Queries.query215_certified,N12Compact.HistoricalOwnership.Queries.query216_certified,(certified_query% 95),N12Compact.HistoricalOwnership.Queries.query217_certified,N12Compact.HistoricalOwnership.Queries.query218_certified,N12Compact.HistoricalOwnership.Queries.query219_certified,N12Compact.HistoricalOwnership.Queries.query220_certified,N12Compact.HistoricalOwnership.Queries.query221_certified,N12Compact.HistoricalOwnership.Queries.query222_certified,(certified_query% 96),N12Compact.HistoricalOwnership.Queries.query223_certified,N12Compact.HistoricalOwnership.Queries.query224_certified,N12Compact.HistoricalOwnership.Queries.query225_certified,N12Compact.HistoricalOwnership.Queries.query226_certified,N12Compact.HistoricalOwnership.Queries.query227_certified,N12Compact.HistoricalOwnership.Queries.query228_certified,N12Compact.HistoricalOwnership.Queries.query229_certified,(certified_query% 97),(certified_query% 98),(certified_query% 99),N12Compact.HistoricalOwnership.Queries.query230_certified,(certified_query% 100),N12Compact.HistoricalOwnership.Queries.query231_certified,N12Compact.HistoricalOwnership.Queries.query232_certified,(certified_query% 101),N12Compact.HistoricalOwnership.Queries.query233_certified,N12Compact.HistoricalOwnership.Queries.query234_certified,N12Compact.HistoricalOwnership.Queries.query235_certified,(certified_query% 102),N12Compact.HistoricalOwnership.Queries.query236_certified,N12Compact.HistoricalOwnership.Queries.query237_certified,N12Compact.HistoricalOwnership.Queries.query238_certified,N12Compact.HistoricalOwnership.Queries.query239_certified,(certified_query% 103),N12Compact.HistoricalOwnership.Queries.query240_certified,N12Compact.HistoricalOwnership.Queries.query241_certified,N12Compact.HistoricalOwnership.Queries.query242_certified,N12Compact.HistoricalOwnership.Queries.query243_certified,N12Compact.HistoricalOwnership.Queries.query244_certified,(certified_query% 104),N12Compact.HistoricalOwnership.Queries.query245_certified,N12Compact.HistoricalOwnership.Queries.query246_certified,N12Compact.HistoricalOwnership.Queries.query247_certified,N12Compact.HistoricalOwnership.Queries.query248_certified,N12Compact.HistoricalOwnership.Queries.query249_certified,N12Compact.HistoricalOwnership.Queries.query250_certified,(certified_query% 105),N12Compact.HistoricalOwnership.Queries.query251_certified,N12Compact.HistoricalOwnership.Queries.query252_certified,N12Compact.HistoricalOwnership.Queries.query253_certified,N12Compact.HistoricalOwnership.Queries.query254_certified,N12Compact.HistoricalOwnership.Queries.query255_certified,N12Compact.HistoricalOwnership.Queries.query256_certified,N12Compact.HistoricalOwnership.Queries.query257_certified,(certified_query% 106),N12Compact.HistoricalOwnership.Queries.query258_certified,N12Compact.HistoricalOwnership.Queries.query259_certified,N12Compact.HistoricalOwnership.Queries.query260_certified,N12Compact.HistoricalOwnership.Queries.query261_certified,N12Compact.HistoricalOwnership.Queries.query262_certified,N12Compact.HistoricalOwnership.Queries.query263_certified,N12Compact.HistoricalOwnership.Queries.query264_certified,N12Compact.HistoricalOwnership.Queries.query265_certified]⟩
private def single717_0_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,1,{0}),(1,1,{1}),(1,1,{0,1}),(1,1,{1,2}),(1,1,{0,1,2}),(1,1,{3}),(1,1,{0,3}),(1,1,{1,3}),(1,1,{0,1,3}),(1,1,{2,3}),(1,1,{0,2,3}),(1,1,{1,2,3}),(1,1,{4}),(1,1,{0,4}),(1,1,{1,4}),(1,1,{0,1,4}),(1,1,{2,4}),(1,1,{0,2,4}),(1,1,{1,2,4}),(1,1,{3,4}),(1,1,{0,3,4}),(1,1,{1,3,4}),(1,1,{2,3,4}),(1,1,{5}),(1,1,{0,5}),(1,1,{1,5}),(1,1,{0,1,5}),(1,1,{2,5}),(1,1,{0,2,5}),(1,1,{1,2,5}),(1,1,{3,5}),(1,1,{0,3,5}),(1,1,{1,3,5}),(1,1,{2,3,5}),(1,1,{4,5}),(1,1,{0,4,5}),(1,1,{1,4,5}),(1,1,{2,4,5}),(1,1,{3,4,5}),(1,1,{6}),(1,1,{0,6}),(1,1,{1,6}),(1,1,{0,1,6}),(1,1,{2,6}),(1,1,{0,2,6}),(1,1,{1,2,6}),(1,1,{3,6}),(1,1,{0,3,6}),(1,1,{1,3,6}),(1,1,{2,3,6}),(1,1,{4,6}),(1,1,{0,4,6}),(1,1,{1,4,6}),(1,1,{2,4,6}),(1,1,{3,4,6}),(1,1,{5,6}),(1,1,{0,5,6}),(1,1,{1,5,6}),(1,1,{2,5,6}),(1,1,{3,5,6}),(1,1,{4,5,6}),(1,1,{7}),(1,1,{0,7}),(1,1,{1,7}),(1,1,{0,1,7}),(1,1,{2,7}),(1,1,{0,2,7}),(1,1,{1,2,7}),(1,1,{3,7}),(1,1,{0,3,7}),(1,1,{1,3,7}),(1,1,{2,3,7}),(1,1,{4,7}),(1,1,{0,4,7}),(1,1,{1,4,7}),(1,1,{2,4,7}),(1,1,{3,4,7}),(1,1,{5,7}),(1,1,{0,5,7}),(1,1,{1,5,7}),(1,1,{2,5,7}),(1,1,{3,5,7}),(1,1,{4,5,7}),(1,1,{6,7}),(1,1,{0,6,7}),(1,1,{1,6,7}),(1,1,{2,6,7}),(1,1,{3,6,7}),(1,1,{4,6,7}),(1,1,{5,6,7}),(1,1,{8}),(1,1,{0,8}),(1,1,{1,8}),(1,1,{0,1,8}),(1,1,{2,8}),(1,1,{0,2,8}),(1,1,{1,2,8}),(1,1,{3,8}),(1,1,{0,3,8}),(1,1,{1,3,8}),(1,1,{2,3,8}),(1,1,{4,8}),(1,1,{0,4,8}),(1,1,{1,4,8}),(1,1,{2,4,8}),(1,1,{3,4,8}),(1,1,{5,8}),(1,1,{0,5,8}),(1,1,{1,5,8}),(1,1,{2,5,8}),(1,1,{3,5,8}),(1,1,{4,5,8}),(1,1,{6,8}),(1,1,{0,6,8}),(1,1,{1,6,8}),(1,1,{2,6,8}),(1,1,{3,6,8}),(1,1,{4,6,8}),(1,1,{5,6,8}),(1,1,{7,8}),(1,1,{0,7,8}),(1,1,{1,7,8}),(1,1,{2,7,8}),(1,1,{3,7,8}),(1,1,{4,7,8}),(1,1,{5,7,8}),(1,1,{6,7,8}),(1,1,{9}),(1,1,{0,9}),(1,1,{1,9}),(1,1,{0,1,9}),(1,1,{2,9}),(1,1,{0,2,9}),(1,1,{1,2,9}),(1,1,{3,9}),(1,1,{0,3,9}),(1,1,{1,3,9}),(1,1,{2,3,9}),(1,1,{4,9}),(1,1,{0,4,9}),(1,1,{1,4,9}),(1,1,{2,4,9}),(1,1,{3,4,9}),(1,1,{5,9}),(1,1,{0,5,9}),(1,1,{1,5,9}),(1,1,{2,5,9}),(1,1,{3,5,9}),(1,1,{4,5,9}),(1,1,{6,9}),(1,1,{0,6,9}),(1,1,{1,6,9}),(1,1,{2,6,9}),(1,1,{3,6,9}),(1,1,{4,6,9}),(1,1,{5,6,9}),(1,1,{7,9}),(1,1,{0,7,9}),(1,1,{1,7,9}),(1,1,{2,7,9}),(1,1,{3,7,9}),(1,1,{4,7,9}),(1,1,{5,7,9}),(1,1,{6,7,9}),(1,1,{8,9}),(1,1,{0,8,9}),(1,1,{1,8,9}),(1,1,{2,8,9}),(1,1,{3,8,9}),(1,1,{4,8,9}),(1,1,{5,8,9}),(1,1,{6,8,9}),(1,1,{7,8,9})]
private theorem single717_0_1_queries_exact :
    single717_0_1Signatures = single717_0_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_0_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{2},{0,2}] : List (Finset Nat)) ∨ (1,1,owned) ∈ single717_0_1Signatures

private instance : DecidablePred single717_0_1_owned_claim := fun index => by
  unfold single717_0_1_owned_claim
  infer_instance

private theorem single717_0_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_0_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_0_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_0_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_0_1 case717Family 1 single717_0_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨1,1,3,[{2},{0,2}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_0_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_0_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_0_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_0_1_owned_block0
      · exact single717_0_1_owned_block1
      · exact single717_0_1_owned_block2
      · exact single717_0_1_owned_block3
      · exact single717_0_1_owned_block4
      · exact single717_0_1_owned_block5
      · exact single717_0_1_owned_block6
      · exact single717_0_1_owned_block7
      · exact single717_0_1_owned_block8
      · exact single717_0_1_owned_block9
      · exact single717_0_1_owned_block10
      · exact single717_0_1_owned_block11
      · exact single717_0_1_owned_block12
      · exact single717_0_1_owned_block13
      · exact single717_0_1_owned_block14
      · exact single717_0_1_owned_block15
      · exact single717_0_1_owned_block16
      · exact single717_0_1_owned_block17
      · exact single717_0_1_owned_block18
      · exact single717_0_1_owned_block19
      · exact single717_0_1_owned_block20
      · exact single717_0_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_0_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_0_1_checked : single717_0_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_0_1 case717Family 1
    single717_0_1Signatures single717_0_1_queries_exact (by decide) single717_0_1_metadata

def single717_1_0 : DirectSingleDomain := ⟨2,1,1,[{0}],[(certified_query% 107),(certified_query% 109),(certified_query% 111),(certified_query% 115),(certified_query% 120),(certified_query% 126),(certified_query% 133),(certified_query% 141),(certified_query% 150)]⟩
private def single717_1_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,0,{1}),(2,0,{2}),(2,0,{3}),(2,0,{4}),(2,0,{5}),(2,0,{6}),(2,0,{7}),(2,0,{8}),(2,0,{9})]
theorem single717_1_0_checked : single717_1_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_1_0 case717Family 0
    single717_1_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_1_1 : DirectSingleDomain := ⟨2,1,3,[{0}],[(certified_query% 160),(certified_query% 161),(certified_query% 162),(certified_query% 163),(certified_query% 164),N12Compact.HistoricalOwnership.Queries.query266_certified,(certified_query% 165),(certified_query% 166),(certified_query% 167),N12Compact.HistoricalOwnership.Queries.query267_certified,(certified_query% 168),N12Compact.HistoricalOwnership.Queries.query268_certified,N12Compact.HistoricalOwnership.Queries.query269_certified,(certified_query% 169),(certified_query% 170),(certified_query% 171),N12Compact.HistoricalOwnership.Queries.query270_certified,(certified_query% 172),N12Compact.HistoricalOwnership.Queries.query271_certified,N12Compact.HistoricalOwnership.Queries.query272_certified,(certified_query% 173),N12Compact.HistoricalOwnership.Queries.query273_certified,N12Compact.HistoricalOwnership.Queries.query274_certified,N12Compact.HistoricalOwnership.Queries.query275_certified,(certified_query% 174),(certified_query% 175),(certified_query% 176),N12Compact.HistoricalOwnership.Queries.query276_certified,(certified_query% 177),N12Compact.HistoricalOwnership.Queries.query277_certified,N12Compact.HistoricalOwnership.Queries.query278_certified,(certified_query% 178),N12Compact.HistoricalOwnership.Queries.query279_certified,N12Compact.HistoricalOwnership.Queries.query280_certified,N12Compact.HistoricalOwnership.Queries.query281_certified,(certified_query% 179),N12Compact.HistoricalOwnership.Queries.query282_certified,N12Compact.HistoricalOwnership.Queries.query283_certified,N12Compact.HistoricalOwnership.Queries.query284_certified,N12Compact.HistoricalOwnership.Queries.query285_certified,(certified_query% 180),(certified_query% 181),(certified_query% 182),N12Compact.HistoricalOwnership.Queries.query286_certified,(certified_query% 183),N12Compact.HistoricalOwnership.Queries.query287_certified,N12Compact.HistoricalOwnership.Queries.query288_certified,(certified_query% 184),N12Compact.HistoricalOwnership.Queries.query289_certified,N12Compact.HistoricalOwnership.Queries.query290_certified,N12Compact.HistoricalOwnership.Queries.query291_certified,(certified_query% 185),N12Compact.HistoricalOwnership.Queries.query292_certified,N12Compact.HistoricalOwnership.Queries.query293_certified,N12Compact.HistoricalOwnership.Queries.query294_certified,N12Compact.HistoricalOwnership.Queries.query295_certified,(certified_query% 186),N12Compact.HistoricalOwnership.Queries.query296_certified,N12Compact.HistoricalOwnership.Queries.query297_certified,N12Compact.HistoricalOwnership.Queries.query298_certified,N12Compact.HistoricalOwnership.Queries.query299_certified,N12Compact.HistoricalOwnership.Queries.query300_certified,(certified_query% 187),(certified_query% 188),(certified_query% 189),N12Compact.HistoricalOwnership.Queries.query301_certified,(certified_query% 190),N12Compact.HistoricalOwnership.Queries.query302_certified,N12Compact.HistoricalOwnership.Queries.query303_certified,(certified_query% 191),N12Compact.HistoricalOwnership.Queries.query304_certified,N12Compact.HistoricalOwnership.Queries.query305_certified,N12Compact.HistoricalOwnership.Queries.query306_certified,(certified_query% 192),N12Compact.HistoricalOwnership.Queries.query307_certified,N12Compact.HistoricalOwnership.Queries.query308_certified,N12Compact.HistoricalOwnership.Queries.query309_certified,N12Compact.HistoricalOwnership.Queries.query310_certified,(certified_query% 193),N12Compact.HistoricalOwnership.Queries.query311_certified,N12Compact.HistoricalOwnership.Queries.query312_certified,N12Compact.HistoricalOwnership.Queries.query313_certified,N12Compact.HistoricalOwnership.Queries.query314_certified,N12Compact.HistoricalOwnership.Queries.query315_certified,(certified_query% 194),N12Compact.HistoricalOwnership.Queries.query316_certified,N12Compact.HistoricalOwnership.Queries.query317_certified,N12Compact.HistoricalOwnership.Queries.query318_certified,N12Compact.HistoricalOwnership.Queries.query319_certified,N12Compact.HistoricalOwnership.Queries.query320_certified,N12Compact.HistoricalOwnership.Queries.query321_certified,(certified_query% 195),(certified_query% 196),(certified_query% 197),N12Compact.HistoricalOwnership.Queries.query322_certified,(certified_query% 198),N12Compact.HistoricalOwnership.Queries.query323_certified,N12Compact.HistoricalOwnership.Queries.query324_certified,(certified_query% 199),N12Compact.HistoricalOwnership.Queries.query325_certified,N12Compact.HistoricalOwnership.Queries.query326_certified,N12Compact.HistoricalOwnership.Queries.query327_certified,(certified_query% 200),N12Compact.HistoricalOwnership.Queries.query328_certified,N12Compact.HistoricalOwnership.Queries.query329_certified,N12Compact.HistoricalOwnership.Queries.query330_certified,N12Compact.HistoricalOwnership.Queries.query331_certified,(certified_query% 201),N12Compact.HistoricalOwnership.Queries.query332_certified,N12Compact.HistoricalOwnership.Queries.query333_certified,N12Compact.HistoricalOwnership.Queries.query334_certified,N12Compact.HistoricalOwnership.Queries.query335_certified,N12Compact.HistoricalOwnership.Queries.query336_certified,(certified_query% 202),N12Compact.HistoricalOwnership.Queries.query337_certified,N12Compact.HistoricalOwnership.Queries.query338_certified,N12Compact.HistoricalOwnership.Queries.query339_certified,N12Compact.HistoricalOwnership.Queries.query340_certified,N12Compact.HistoricalOwnership.Queries.query341_certified,N12Compact.HistoricalOwnership.Queries.query342_certified,(certified_query% 203),N12Compact.HistoricalOwnership.Queries.query343_certified,N12Compact.HistoricalOwnership.Queries.query344_certified,N12Compact.HistoricalOwnership.Queries.query345_certified,N12Compact.HistoricalOwnership.Queries.query346_certified,N12Compact.HistoricalOwnership.Queries.query347_certified,N12Compact.HistoricalOwnership.Queries.query348_certified,N12Compact.HistoricalOwnership.Queries.query349_certified,(certified_query% 204),(certified_query% 205),(certified_query% 206),N12Compact.HistoricalOwnership.Queries.query350_certified,(certified_query% 207),N12Compact.HistoricalOwnership.Queries.query351_certified,N12Compact.HistoricalOwnership.Queries.query352_certified,(certified_query% 208),N12Compact.HistoricalOwnership.Queries.query353_certified,N12Compact.HistoricalOwnership.Queries.query354_certified,N12Compact.HistoricalOwnership.Queries.query355_certified,(certified_query% 209),N12Compact.HistoricalOwnership.Queries.query356_certified,N12Compact.HistoricalOwnership.Queries.query357_certified,N12Compact.HistoricalOwnership.Queries.query358_certified,N12Compact.HistoricalOwnership.Queries.query359_certified,(certified_query% 210),N12Compact.HistoricalOwnership.Queries.query360_certified,N12Compact.HistoricalOwnership.Queries.query361_certified,N12Compact.HistoricalOwnership.Queries.query362_certified,N12Compact.HistoricalOwnership.Queries.query363_certified,N12Compact.HistoricalOwnership.Queries.query364_certified,(certified_query% 211),N12Compact.HistoricalOwnership.Queries.query365_certified,N12Compact.HistoricalOwnership.Queries.query366_certified,N12Compact.HistoricalOwnership.Queries.query367_certified,N12Compact.HistoricalOwnership.Queries.query368_certified,N12Compact.HistoricalOwnership.Queries.query369_certified,N12Compact.HistoricalOwnership.Queries.query370_certified,(certified_query% 212),N12Compact.HistoricalOwnership.Queries.query371_certified,N12Compact.HistoricalOwnership.Queries.query372_certified,N12Compact.HistoricalOwnership.Queries.query373_certified,N12Compact.HistoricalOwnership.Queries.query374_certified,N12Compact.HistoricalOwnership.Queries.query375_certified,N12Compact.HistoricalOwnership.Queries.query376_certified,N12Compact.HistoricalOwnership.Queries.query377_certified,(certified_query% 213),N12Compact.HistoricalOwnership.Queries.query378_certified,N12Compact.HistoricalOwnership.Queries.query379_certified,N12Compact.HistoricalOwnership.Queries.query380_certified,N12Compact.HistoricalOwnership.Queries.query381_certified,N12Compact.HistoricalOwnership.Queries.query382_certified,N12Compact.HistoricalOwnership.Queries.query383_certified,N12Compact.HistoricalOwnership.Queries.query384_certified,N12Compact.HistoricalOwnership.Queries.query385_certified]⟩
private def single717_1_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,1,{1}),(2,1,{0,1}),(2,1,{2}),(2,1,{0,2}),(2,1,{1,2}),(2,1,{0,1,2}),(2,1,{3}),(2,1,{0,3}),(2,1,{1,3}),(2,1,{0,1,3}),(2,1,{2,3}),(2,1,{0,2,3}),(2,1,{1,2,3}),(2,1,{4}),(2,1,{0,4}),(2,1,{1,4}),(2,1,{0,1,4}),(2,1,{2,4}),(2,1,{0,2,4}),(2,1,{1,2,4}),(2,1,{3,4}),(2,1,{0,3,4}),(2,1,{1,3,4}),(2,1,{2,3,4}),(2,1,{5}),(2,1,{0,5}),(2,1,{1,5}),(2,1,{0,1,5}),(2,1,{2,5}),(2,1,{0,2,5}),(2,1,{1,2,5}),(2,1,{3,5}),(2,1,{0,3,5}),(2,1,{1,3,5}),(2,1,{2,3,5}),(2,1,{4,5}),(2,1,{0,4,5}),(2,1,{1,4,5}),(2,1,{2,4,5}),(2,1,{3,4,5}),(2,1,{6}),(2,1,{0,6}),(2,1,{1,6}),(2,1,{0,1,6}),(2,1,{2,6}),(2,1,{0,2,6}),(2,1,{1,2,6}),(2,1,{3,6}),(2,1,{0,3,6}),(2,1,{1,3,6}),(2,1,{2,3,6}),(2,1,{4,6}),(2,1,{0,4,6}),(2,1,{1,4,6}),(2,1,{2,4,6}),(2,1,{3,4,6}),(2,1,{5,6}),(2,1,{0,5,6}),(2,1,{1,5,6}),(2,1,{2,5,6}),(2,1,{3,5,6}),(2,1,{4,5,6}),(2,1,{7}),(2,1,{0,7}),(2,1,{1,7}),(2,1,{0,1,7}),(2,1,{2,7}),(2,1,{0,2,7}),(2,1,{1,2,7}),(2,1,{3,7}),(2,1,{0,3,7}),(2,1,{1,3,7}),(2,1,{2,3,7}),(2,1,{4,7}),(2,1,{0,4,7}),(2,1,{1,4,7}),(2,1,{2,4,7}),(2,1,{3,4,7}),(2,1,{5,7}),(2,1,{0,5,7}),(2,1,{1,5,7}),(2,1,{2,5,7}),(2,1,{3,5,7}),(2,1,{4,5,7}),(2,1,{6,7}),(2,1,{0,6,7}),(2,1,{1,6,7}),(2,1,{2,6,7}),(2,1,{3,6,7}),(2,1,{4,6,7}),(2,1,{5,6,7}),(2,1,{8}),(2,1,{0,8}),(2,1,{1,8}),(2,1,{0,1,8}),(2,1,{2,8}),(2,1,{0,2,8}),(2,1,{1,2,8}),(2,1,{3,8}),(2,1,{0,3,8}),(2,1,{1,3,8}),(2,1,{2,3,8}),(2,1,{4,8}),(2,1,{0,4,8}),(2,1,{1,4,8}),(2,1,{2,4,8}),(2,1,{3,4,8}),(2,1,{5,8}),(2,1,{0,5,8}),(2,1,{1,5,8}),(2,1,{2,5,8}),(2,1,{3,5,8}),(2,1,{4,5,8}),(2,1,{6,8}),(2,1,{0,6,8}),(2,1,{1,6,8}),(2,1,{2,6,8}),(2,1,{3,6,8}),(2,1,{4,6,8}),(2,1,{5,6,8}),(2,1,{7,8}),(2,1,{0,7,8}),(2,1,{1,7,8}),(2,1,{2,7,8}),(2,1,{3,7,8}),(2,1,{4,7,8}),(2,1,{5,7,8}),(2,1,{6,7,8}),(2,1,{9}),(2,1,{0,9}),(2,1,{1,9}),(2,1,{0,1,9}),(2,1,{2,9}),(2,1,{0,2,9}),(2,1,{1,2,9}),(2,1,{3,9}),(2,1,{0,3,9}),(2,1,{1,3,9}),(2,1,{2,3,9}),(2,1,{4,9}),(2,1,{0,4,9}),(2,1,{1,4,9}),(2,1,{2,4,9}),(2,1,{3,4,9}),(2,1,{5,9}),(2,1,{0,5,9}),(2,1,{1,5,9}),(2,1,{2,5,9}),(2,1,{3,5,9}),(2,1,{4,5,9}),(2,1,{6,9}),(2,1,{0,6,9}),(2,1,{1,6,9}),(2,1,{2,6,9}),(2,1,{3,6,9}),(2,1,{4,6,9}),(2,1,{5,6,9}),(2,1,{7,9}),(2,1,{0,7,9}),(2,1,{1,7,9}),(2,1,{2,7,9}),(2,1,{3,7,9}),(2,1,{4,7,9}),(2,1,{5,7,9}),(2,1,{6,7,9}),(2,1,{8,9}),(2,1,{0,8,9}),(2,1,{1,8,9}),(2,1,{2,8,9}),(2,1,{3,8,9}),(2,1,{4,8,9}),(2,1,{5,8,9}),(2,1,{6,8,9}),(2,1,{7,8,9})]
private theorem single717_1_1_queries_exact :
    single717_1_1Signatures = single717_1_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_1_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{0}] : List (Finset Nat)) ∨ (2,1,owned) ∈ single717_1_1Signatures

private instance : DecidablePred single717_1_1_owned_claim := fun index => by
  unfold single717_1_1_owned_claim
  infer_instance

private theorem single717_1_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_1_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_1_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_1_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_1_1 case717Family 1 single717_1_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨2,1,3,[{0}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_1_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_1_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_1_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_1_1_owned_block0
      · exact single717_1_1_owned_block1
      · exact single717_1_1_owned_block2
      · exact single717_1_1_owned_block3
      · exact single717_1_1_owned_block4
      · exact single717_1_1_owned_block5
      · exact single717_1_1_owned_block6
      · exact single717_1_1_owned_block7
      · exact single717_1_1_owned_block8
      · exact single717_1_1_owned_block9
      · exact single717_1_1_owned_block10
      · exact single717_1_1_owned_block11
      · exact single717_1_1_owned_block12
      · exact single717_1_1_owned_block13
      · exact single717_1_1_owned_block14
      · exact single717_1_1_owned_block15
      · exact single717_1_1_owned_block16
      · exact single717_1_1_owned_block17
      · exact single717_1_1_owned_block18
      · exact single717_1_1_owned_block19
      · exact single717_1_1_owned_block20
      · exact single717_1_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_1_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_1_1_checked : single717_1_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_1_1 case717Family 1
    single717_1_1Signatures single717_1_1_queries_exact (by decide) single717_1_1_metadata

def single717_2_0 : DirectSingleDomain := ⟨12,0,0,[∅],[]⟩
private def single717_2_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  []
theorem single717_2_0_checked : single717_2_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_2_0 case717Family 0
    single717_2_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_2_1 : DirectSingleDomain := ⟨12,0,2,[∅,{5},{8},{5,8}],[N12Compact.HistoricalOwnership.Queries.query386_certified,N12Compact.HistoricalOwnership.Queries.query387_certified,N12Compact.HistoricalOwnership.Queries.query388_certified,N12Compact.HistoricalOwnership.Queries.query389_certified,N12Compact.HistoricalOwnership.Queries.query390_certified,N12Compact.HistoricalOwnership.Queries.query391_certified,N12Compact.HistoricalOwnership.Queries.query392_certified,N12Compact.HistoricalOwnership.Queries.query393_certified,N12Compact.HistoricalOwnership.Queries.query394_certified,N12Compact.HistoricalOwnership.Queries.query395_certified,N12Compact.HistoricalOwnership.Queries.query396_certified,N12Compact.HistoricalOwnership.Queries.query397_certified,N12Compact.HistoricalOwnership.Queries.query398_certified,N12Compact.HistoricalOwnership.Queries.query399_certified,N12Compact.HistoricalOwnership.Queries.query400_certified,N12Compact.HistoricalOwnership.Queries.query401_certified,N12Compact.HistoricalOwnership.Queries.query402_certified,N12Compact.HistoricalOwnership.Queries.query403_certified,N12Compact.HistoricalOwnership.Queries.query404_certified,N12Compact.HistoricalOwnership.Queries.query405_certified,N12Compact.HistoricalOwnership.Queries.query406_certified,N12Compact.HistoricalOwnership.Queries.query407_certified,N12Compact.HistoricalOwnership.Queries.query408_certified,N12Compact.HistoricalOwnership.Queries.query409_certified,N12Compact.HistoricalOwnership.Queries.query410_certified,N12Compact.HistoricalOwnership.Queries.query411_certified,N12Compact.HistoricalOwnership.Queries.query412_certified,N12Compact.HistoricalOwnership.Queries.query413_certified,N12Compact.HistoricalOwnership.Queries.query414_certified,N12Compact.HistoricalOwnership.Queries.query415_certified,N12Compact.HistoricalOwnership.Queries.query416_certified,N12Compact.HistoricalOwnership.Queries.query417_certified,N12Compact.HistoricalOwnership.Queries.query418_certified,N12Compact.HistoricalOwnership.Queries.query419_certified,N12Compact.HistoricalOwnership.Queries.query420_certified,N12Compact.HistoricalOwnership.Queries.query421_certified,N12Compact.HistoricalOwnership.Queries.query422_certified,N12Compact.HistoricalOwnership.Queries.query423_certified,N12Compact.HistoricalOwnership.Queries.query424_certified,N12Compact.HistoricalOwnership.Queries.query425_certified,N12Compact.HistoricalOwnership.Queries.query426_certified,N12Compact.HistoricalOwnership.Queries.query427_certified,N12Compact.HistoricalOwnership.Queries.query428_certified,N12Compact.HistoricalOwnership.Queries.query429_certified,N12Compact.HistoricalOwnership.Queries.query430_certified,N12Compact.HistoricalOwnership.Queries.query431_certified,N12Compact.HistoricalOwnership.Queries.query432_certified,N12Compact.HistoricalOwnership.Queries.query433_certified,N12Compact.HistoricalOwnership.Queries.query434_certified,N12Compact.HistoricalOwnership.Queries.query435_certified,N12Compact.HistoricalOwnership.Queries.query436_certified,N12Compact.HistoricalOwnership.Queries.query437_certified]⟩
private def single717_2_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,1,{0}),(12,1,{1}),(12,1,{0,1}),(12,1,{2}),(12,1,{0,2}),(12,1,{1,2}),(12,1,{3}),(12,1,{0,3}),(12,1,{1,3}),(12,1,{2,3}),(12,1,{4}),(12,1,{0,4}),(12,1,{1,4}),(12,1,{2,4}),(12,1,{3,4}),(12,1,{0,5}),(12,1,{1,5}),(12,1,{2,5}),(12,1,{3,5}),(12,1,{4,5}),(12,1,{6}),(12,1,{0,6}),(12,1,{1,6}),(12,1,{2,6}),(12,1,{3,6}),(12,1,{4,6}),(12,1,{5,6}),(12,1,{7}),(12,1,{0,7}),(12,1,{1,7}),(12,1,{2,7}),(12,1,{3,7}),(12,1,{4,7}),(12,1,{5,7}),(12,1,{6,7}),(12,1,{0,8}),(12,1,{1,8}),(12,1,{2,8}),(12,1,{3,8}),(12,1,{4,8}),(12,1,{6,8}),(12,1,{7,8}),(12,1,{9}),(12,1,{0,9}),(12,1,{1,9}),(12,1,{2,9}),(12,1,{3,9}),(12,1,{4,9}),(12,1,{5,9}),(12,1,{6,9}),(12,1,{7,9}),(12,1,{8,9})]
theorem single717_2_1_checked : single717_2_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomain.checked single717_2_1 case717Family 1
    single717_2_1Signatures (by rfl) (by decide) (by decide +kernel)

def single717_3_0 : DirectSingleDomain := ⟨16,1,1,[{7}],[(certified_query% 339),(certified_query% 340),(certified_query% 342),(certified_query% 345),(certified_query% 349),(certified_query% 354),(certified_query% 360),(certified_query% 374),(certified_query% 383)]⟩
private def single717_3_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16,0,{0}),(16,0,{1}),(16,0,{2}),(16,0,{3}),(16,0,{4}),(16,0,{5}),(16,0,{6}),(16,0,{8}),(16,0,{9})]
theorem single717_3_0_checked : single717_3_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_3_0 case717Family 0
    single717_3_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_3_1 : DirectSingleDomain := ⟨16,1,3,[{7},{7,9}],[(certified_query% 393),(certified_query% 394),N12Compact.HistoricalOwnership.Queries.query440_certified,(certified_query% 395),N12Compact.HistoricalOwnership.Queries.query441_certified,N12Compact.HistoricalOwnership.Queries.query442_certified,N12Compact.HistoricalOwnership.Queries.query443_certified,(certified_query% 396),N12Compact.HistoricalOwnership.Queries.query444_certified,N12Compact.HistoricalOwnership.Queries.query445_certified,N12Compact.HistoricalOwnership.Queries.query446_certified,N12Compact.HistoricalOwnership.Queries.query447_certified,N12Compact.HistoricalOwnership.Queries.query448_certified,N12Compact.HistoricalOwnership.Queries.query449_certified,(certified_query% 397),N12Compact.HistoricalOwnership.Queries.query450_certified,N12Compact.HistoricalOwnership.Queries.query451_certified,N12Compact.HistoricalOwnership.Queries.query452_certified,N12Compact.HistoricalOwnership.Queries.query453_certified,N12Compact.HistoricalOwnership.Queries.query454_certified,N12Compact.HistoricalOwnership.Queries.query455_certified,N12Compact.HistoricalOwnership.Queries.query456_certified,N12Compact.HistoricalOwnership.Queries.query457_certified,N12Compact.HistoricalOwnership.Queries.query458_certified,N12Compact.HistoricalOwnership.Queries.query459_certified,(certified_query% 398),N12Compact.HistoricalOwnership.Queries.query460_certified,N12Compact.HistoricalOwnership.Queries.query461_certified,N12Compact.HistoricalOwnership.Queries.query462_certified,N12Compact.HistoricalOwnership.Queries.query463_certified,N12Compact.HistoricalOwnership.Queries.query464_certified,N12Compact.HistoricalOwnership.Queries.query465_certified,N12Compact.HistoricalOwnership.Queries.query466_certified,N12Compact.HistoricalOwnership.Queries.query467_certified,N12Compact.HistoricalOwnership.Queries.query468_certified,N12Compact.HistoricalOwnership.Queries.query469_certified,N12Compact.HistoricalOwnership.Queries.query470_certified,N12Compact.HistoricalOwnership.Queries.query471_certified,N12Compact.HistoricalOwnership.Queries.query472_certified,N12Compact.HistoricalOwnership.Queries.query473_certified,N12Compact.HistoricalOwnership.Queries.query474_certified,(certified_query% 399),N12Compact.HistoricalOwnership.Queries.query475_certified,N12Compact.HistoricalOwnership.Queries.query476_certified,N12Compact.HistoricalOwnership.Queries.query477_certified,N12Compact.HistoricalOwnership.Queries.query478_certified,N12Compact.HistoricalOwnership.Queries.query479_certified,N12Compact.HistoricalOwnership.Queries.query480_certified,N12Compact.HistoricalOwnership.Queries.query481_certified,N12Compact.HistoricalOwnership.Queries.query482_certified,N12Compact.HistoricalOwnership.Queries.query483_certified,N12Compact.HistoricalOwnership.Queries.query484_certified,N12Compact.HistoricalOwnership.Queries.query485_certified,N12Compact.HistoricalOwnership.Queries.query486_certified,N12Compact.HistoricalOwnership.Queries.query487_certified,N12Compact.HistoricalOwnership.Queries.query488_certified,N12Compact.HistoricalOwnership.Queries.query489_certified,N12Compact.HistoricalOwnership.Queries.query490_certified,N12Compact.HistoricalOwnership.Queries.query491_certified,N12Compact.HistoricalOwnership.Queries.query492_certified,N12Compact.HistoricalOwnership.Queries.query493_certified,N12Compact.HistoricalOwnership.Queries.query494_certified,N12Compact.HistoricalOwnership.Queries.query495_certified,N12Compact.HistoricalOwnership.Queries.query496_certified,N12Compact.HistoricalOwnership.Queries.query497_certified,N12Compact.HistoricalOwnership.Queries.query498_certified,N12Compact.HistoricalOwnership.Queries.query499_certified,N12Compact.HistoricalOwnership.Queries.query500_certified,N12Compact.HistoricalOwnership.Queries.query501_certified,N12Compact.HistoricalOwnership.Queries.query502_certified,N12Compact.HistoricalOwnership.Queries.query503_certified,N12Compact.HistoricalOwnership.Queries.query504_certified,N12Compact.HistoricalOwnership.Queries.query505_certified,N12Compact.HistoricalOwnership.Queries.query506_certified,N12Compact.HistoricalOwnership.Queries.query507_certified,N12Compact.HistoricalOwnership.Queries.query508_certified,N12Compact.HistoricalOwnership.Queries.query509_certified,N12Compact.HistoricalOwnership.Queries.query510_certified,N12Compact.HistoricalOwnership.Queries.query511_certified,N12Compact.HistoricalOwnership.Queries.query512_certified,N12Compact.HistoricalOwnership.Queries.query513_certified,N12Compact.HistoricalOwnership.Queries.query514_certified,N12Compact.HistoricalOwnership.Queries.query515_certified,N12Compact.HistoricalOwnership.Queries.query516_certified,N12Compact.HistoricalOwnership.Queries.query517_certified,N12Compact.HistoricalOwnership.Queries.query518_certified,N12Compact.HistoricalOwnership.Queries.query519_certified,N12Compact.HistoricalOwnership.Queries.query520_certified,N12Compact.HistoricalOwnership.Queries.query521_certified,N12Compact.HistoricalOwnership.Queries.query522_certified,N12Compact.HistoricalOwnership.Queries.query523_certified,(certified_query% 400),N12Compact.HistoricalOwnership.Queries.query524_certified,N12Compact.HistoricalOwnership.Queries.query525_certified,N12Compact.HistoricalOwnership.Queries.query526_certified,N12Compact.HistoricalOwnership.Queries.query527_certified,N12Compact.HistoricalOwnership.Queries.query528_certified,N12Compact.HistoricalOwnership.Queries.query529_certified,N12Compact.HistoricalOwnership.Queries.query530_certified,N12Compact.HistoricalOwnership.Queries.query531_certified,N12Compact.HistoricalOwnership.Queries.query532_certified,N12Compact.HistoricalOwnership.Queries.query533_certified,N12Compact.HistoricalOwnership.Queries.query534_certified,N12Compact.HistoricalOwnership.Queries.query535_certified,N12Compact.HistoricalOwnership.Queries.query536_certified,N12Compact.HistoricalOwnership.Queries.query537_certified,N12Compact.HistoricalOwnership.Queries.query538_certified,N12Compact.HistoricalOwnership.Queries.query539_certified,N12Compact.HistoricalOwnership.Queries.query540_certified,N12Compact.HistoricalOwnership.Queries.query541_certified,N12Compact.HistoricalOwnership.Queries.query542_certified,N12Compact.HistoricalOwnership.Queries.query543_certified,N12Compact.HistoricalOwnership.Queries.query544_certified,N12Compact.HistoricalOwnership.Queries.query545_certified,N12Compact.HistoricalOwnership.Queries.query546_certified,N12Compact.HistoricalOwnership.Queries.query547_certified,N12Compact.HistoricalOwnership.Queries.query548_certified,N12Compact.HistoricalOwnership.Queries.query549_certified,N12Compact.HistoricalOwnership.Queries.query550_certified,N12Compact.HistoricalOwnership.Queries.query551_certified,N12Compact.HistoricalOwnership.Queries.query552_certified,N12Compact.HistoricalOwnership.Queries.query553_certified,N12Compact.HistoricalOwnership.Queries.query554_certified,N12Compact.HistoricalOwnership.Queries.query555_certified,N12Compact.HistoricalOwnership.Queries.query556_certified,N12Compact.HistoricalOwnership.Queries.query557_certified,N12Compact.HistoricalOwnership.Queries.query558_certified,N12Compact.HistoricalOwnership.Queries.query559_certified,(certified_query% 401),N12Compact.HistoricalOwnership.Queries.query560_certified,N12Compact.HistoricalOwnership.Queries.query561_certified,N12Compact.HistoricalOwnership.Queries.query562_certified,N12Compact.HistoricalOwnership.Queries.query563_certified,N12Compact.HistoricalOwnership.Queries.query564_certified,N12Compact.HistoricalOwnership.Queries.query565_certified,N12Compact.HistoricalOwnership.Queries.query566_certified,N12Compact.HistoricalOwnership.Queries.query567_certified,N12Compact.HistoricalOwnership.Queries.query568_certified,N12Compact.HistoricalOwnership.Queries.query569_certified,N12Compact.HistoricalOwnership.Queries.query570_certified,N12Compact.HistoricalOwnership.Queries.query571_certified,N12Compact.HistoricalOwnership.Queries.query572_certified,N12Compact.HistoricalOwnership.Queries.query573_certified,N12Compact.HistoricalOwnership.Queries.query574_certified,N12Compact.HistoricalOwnership.Queries.query575_certified,N12Compact.HistoricalOwnership.Queries.query576_certified,N12Compact.HistoricalOwnership.Queries.query577_certified,N12Compact.HistoricalOwnership.Queries.query578_certified,N12Compact.HistoricalOwnership.Queries.query579_certified,N12Compact.HistoricalOwnership.Queries.query580_certified,N12Compact.HistoricalOwnership.Queries.query581_certified,N12Compact.HistoricalOwnership.Queries.query582_certified,N12Compact.HistoricalOwnership.Queries.query583_certified,N12Compact.HistoricalOwnership.Queries.query584_certified,N12Compact.HistoricalOwnership.Queries.query585_certified,N12Compact.HistoricalOwnership.Queries.query586_certified,N12Compact.HistoricalOwnership.Queries.query587_certified,N12Compact.HistoricalOwnership.Queries.query588_certified,N12Compact.HistoricalOwnership.Queries.query589_certified,N12Compact.HistoricalOwnership.Queries.query590_certified,N12Compact.HistoricalOwnership.Queries.query591_certified,N12Compact.HistoricalOwnership.Queries.query592_certified,N12Compact.HistoricalOwnership.Queries.query593_certified,N12Compact.HistoricalOwnership.Queries.query594_certified,N12Compact.HistoricalOwnership.Queries.query595_certified,N12Compact.HistoricalOwnership.Queries.query596_certified,N12Compact.HistoricalOwnership.Queries.query597_certified,N12Compact.HistoricalOwnership.Queries.query598_certified,N12Compact.HistoricalOwnership.Queries.query599_certified,N12Compact.HistoricalOwnership.Queries.query600_certified,N12Compact.HistoricalOwnership.Queries.query601_certified,N12Compact.HistoricalOwnership.Queries.query602_certified,N12Compact.HistoricalOwnership.Queries.query603_certified]⟩
private def single717_3_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16,1,{0}),(16,1,{1}),(16,1,{0,1}),(16,1,{2}),(16,1,{0,2}),(16,1,{1,2}),(16,1,{0,1,2}),(16,1,{3}),(16,1,{0,3}),(16,1,{1,3}),(16,1,{0,1,3}),(16,1,{2,3}),(16,1,{0,2,3}),(16,1,{1,2,3}),(16,1,{4}),(16,1,{0,4}),(16,1,{1,4}),(16,1,{0,1,4}),(16,1,{2,4}),(16,1,{0,2,4}),(16,1,{1,2,4}),(16,1,{3,4}),(16,1,{0,3,4}),(16,1,{1,3,4}),(16,1,{2,3,4}),(16,1,{5}),(16,1,{0,5}),(16,1,{1,5}),(16,1,{0,1,5}),(16,1,{2,5}),(16,1,{0,2,5}),(16,1,{1,2,5}),(16,1,{3,5}),(16,1,{0,3,5}),(16,1,{1,3,5}),(16,1,{2,3,5}),(16,1,{4,5}),(16,1,{0,4,5}),(16,1,{1,4,5}),(16,1,{2,4,5}),(16,1,{3,4,5}),(16,1,{6}),(16,1,{0,6}),(16,1,{1,6}),(16,1,{0,1,6}),(16,1,{2,6}),(16,1,{0,2,6}),(16,1,{1,2,6}),(16,1,{3,6}),(16,1,{0,3,6}),(16,1,{1,3,6}),(16,1,{2,3,6}),(16,1,{4,6}),(16,1,{0,4,6}),(16,1,{1,4,6}),(16,1,{2,4,6}),(16,1,{3,4,6}),(16,1,{5,6}),(16,1,{0,5,6}),(16,1,{1,5,6}),(16,1,{2,5,6}),(16,1,{3,5,6}),(16,1,{4,5,6}),(16,1,{0,7}),(16,1,{1,7}),(16,1,{0,1,7}),(16,1,{2,7}),(16,1,{0,2,7}),(16,1,{1,2,7}),(16,1,{3,7}),(16,1,{0,3,7}),(16,1,{1,3,7}),(16,1,{2,3,7}),(16,1,{4,7}),(16,1,{0,4,7}),(16,1,{1,4,7}),(16,1,{2,4,7}),(16,1,{3,4,7}),(16,1,{5,7}),(16,1,{0,5,7}),(16,1,{1,5,7}),(16,1,{2,5,7}),(16,1,{3,5,7}),(16,1,{4,5,7}),(16,1,{6,7}),(16,1,{0,6,7}),(16,1,{1,6,7}),(16,1,{2,6,7}),(16,1,{3,6,7}),(16,1,{4,6,7}),(16,1,{5,6,7}),(16,1,{8}),(16,1,{0,8}),(16,1,{1,8}),(16,1,{0,1,8}),(16,1,{2,8}),(16,1,{0,2,8}),(16,1,{1,2,8}),(16,1,{3,8}),(16,1,{0,3,8}),(16,1,{1,3,8}),(16,1,{2,3,8}),(16,1,{4,8}),(16,1,{0,4,8}),(16,1,{1,4,8}),(16,1,{2,4,8}),(16,1,{3,4,8}),(16,1,{5,8}),(16,1,{0,5,8}),(16,1,{1,5,8}),(16,1,{2,5,8}),(16,1,{3,5,8}),(16,1,{4,5,8}),(16,1,{6,8}),(16,1,{0,6,8}),(16,1,{1,6,8}),(16,1,{2,6,8}),(16,1,{3,6,8}),(16,1,{4,6,8}),(16,1,{5,6,8}),(16,1,{7,8}),(16,1,{0,7,8}),(16,1,{1,7,8}),(16,1,{2,7,8}),(16,1,{3,7,8}),(16,1,{4,7,8}),(16,1,{5,7,8}),(16,1,{6,7,8}),(16,1,{9}),(16,1,{0,9}),(16,1,{1,9}),(16,1,{0,1,9}),(16,1,{2,9}),(16,1,{0,2,9}),(16,1,{1,2,9}),(16,1,{3,9}),(16,1,{0,3,9}),(16,1,{1,3,9}),(16,1,{2,3,9}),(16,1,{4,9}),(16,1,{0,4,9}),(16,1,{1,4,9}),(16,1,{2,4,9}),(16,1,{3,4,9}),(16,1,{5,9}),(16,1,{0,5,9}),(16,1,{1,5,9}),(16,1,{2,5,9}),(16,1,{3,5,9}),(16,1,{4,5,9}),(16,1,{6,9}),(16,1,{0,6,9}),(16,1,{1,6,9}),(16,1,{2,6,9}),(16,1,{3,6,9}),(16,1,{4,6,9}),(16,1,{5,6,9}),(16,1,{0,7,9}),(16,1,{1,7,9}),(16,1,{2,7,9}),(16,1,{3,7,9}),(16,1,{4,7,9}),(16,1,{5,7,9}),(16,1,{6,7,9}),(16,1,{8,9}),(16,1,{0,8,9}),(16,1,{1,8,9}),(16,1,{2,8,9}),(16,1,{3,8,9}),(16,1,{4,8,9}),(16,1,{5,8,9}),(16,1,{6,8,9}),(16,1,{7,8,9})]
private theorem single717_3_1_queries_exact :
    single717_3_1Signatures = single717_3_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_3_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{7},{7,9}] : List (Finset Nat)) ∨ (16,1,owned) ∈ single717_3_1Signatures

private instance : DecidablePred single717_3_1_owned_claim := fun index => by
  unfold single717_3_1_owned_claim
  infer_instance

private theorem single717_3_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_3_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_3_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_3_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_3_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_3_1 case717Family 1 single717_3_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨16,1,3,[{7},{7,9}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_3_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_3_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_3_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_3_1_owned_block0
      · exact single717_3_1_owned_block1
      · exact single717_3_1_owned_block2
      · exact single717_3_1_owned_block3
      · exact single717_3_1_owned_block4
      · exact single717_3_1_owned_block5
      · exact single717_3_1_owned_block6
      · exact single717_3_1_owned_block7
      · exact single717_3_1_owned_block8
      · exact single717_3_1_owned_block9
      · exact single717_3_1_owned_block10
      · exact single717_3_1_owned_block11
      · exact single717_3_1_owned_block12
      · exact single717_3_1_owned_block13
      · exact single717_3_1_owned_block14
      · exact single717_3_1_owned_block15
      · exact single717_3_1_owned_block16
      · exact single717_3_1_owned_block17
      · exact single717_3_1_owned_block18
      · exact single717_3_1_owned_block19
      · exact single717_3_1_owned_block20
      · exact single717_3_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_3_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_3_1_checked : single717_3_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_3_1 case717Family 1
    single717_3_1Signatures single717_3_1_queries_exact (by decide) single717_3_1_metadata

def single717_4_0 : DirectSingleDomain := ⟨32,1,1,[{9}],[(certified_query% 402),(certified_query% 403),(certified_query% 404),(certified_query% 405),(certified_query% 406),(certified_query% 407),(certified_query% 408),(certified_query% 409),(certified_query% 410)]⟩
private def single717_4_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32,0,{0}),(32,0,{1}),(32,0,{2}),(32,0,{3}),(32,0,{4}),(32,0,{5}),(32,0,{6}),(32,0,{7}),(32,0,{8})]
theorem single717_4_0_checked : single717_4_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_4_0 case717Family 0
    single717_4_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_4_1 : DirectSingleDomain := ⟨32,1,3,[{9}],[(certified_query% 411),(certified_query% 412),N12Compact.HistoricalOwnership.Queries.query604_certified,(certified_query% 413),N12Compact.HistoricalOwnership.Queries.query605_certified,N12Compact.HistoricalOwnership.Queries.query606_certified,N12Compact.HistoricalOwnership.Queries.query607_certified,(certified_query% 414),N12Compact.HistoricalOwnership.Queries.query608_certified,N12Compact.HistoricalOwnership.Queries.query609_certified,N12Compact.HistoricalOwnership.Queries.query610_certified,N12Compact.HistoricalOwnership.Queries.query611_certified,N12Compact.HistoricalOwnership.Queries.query612_certified,N12Compact.HistoricalOwnership.Queries.query613_certified,(certified_query% 415),N12Compact.HistoricalOwnership.Queries.query614_certified,N12Compact.HistoricalOwnership.Queries.query615_certified,N12Compact.HistoricalOwnership.Queries.query616_certified,N12Compact.HistoricalOwnership.Queries.query617_certified,N12Compact.HistoricalOwnership.Queries.query618_certified,N12Compact.HistoricalOwnership.Queries.query619_certified,N12Compact.HistoricalOwnership.Queries.query620_certified,N12Compact.HistoricalOwnership.Queries.query621_certified,N12Compact.HistoricalOwnership.Queries.query622_certified,N12Compact.HistoricalOwnership.Queries.query623_certified,(certified_query% 416),N12Compact.HistoricalOwnership.Queries.query624_certified,N12Compact.HistoricalOwnership.Queries.query625_certified,N12Compact.HistoricalOwnership.Queries.query626_certified,N12Compact.HistoricalOwnership.Queries.query627_certified,N12Compact.HistoricalOwnership.Queries.query628_certified,N12Compact.HistoricalOwnership.Queries.query629_certified,N12Compact.HistoricalOwnership.Queries.query630_certified,N12Compact.HistoricalOwnership.Queries.query631_certified,N12Compact.HistoricalOwnership.Queries.query632_certified,N12Compact.HistoricalOwnership.Queries.query633_certified,N12Compact.HistoricalOwnership.Queries.query634_certified,N12Compact.HistoricalOwnership.Queries.query635_certified,N12Compact.HistoricalOwnership.Queries.query636_certified,N12Compact.HistoricalOwnership.Queries.query637_certified,N12Compact.HistoricalOwnership.Queries.query638_certified,(certified_query% 417),N12Compact.HistoricalOwnership.Queries.query639_certified,N12Compact.HistoricalOwnership.Queries.query640_certified,N12Compact.HistoricalOwnership.Queries.query641_certified,N12Compact.HistoricalOwnership.Queries.query642_certified,N12Compact.HistoricalOwnership.Queries.query643_certified,N12Compact.HistoricalOwnership.Queries.query644_certified,N12Compact.HistoricalOwnership.Queries.query645_certified,N12Compact.HistoricalOwnership.Queries.query646_certified,N12Compact.HistoricalOwnership.Queries.query647_certified,N12Compact.HistoricalOwnership.Queries.query648_certified,N12Compact.HistoricalOwnership.Queries.query649_certified,N12Compact.HistoricalOwnership.Queries.query650_certified,N12Compact.HistoricalOwnership.Queries.query651_certified,N12Compact.HistoricalOwnership.Queries.query652_certified,N12Compact.HistoricalOwnership.Queries.query653_certified,N12Compact.HistoricalOwnership.Queries.query654_certified,N12Compact.HistoricalOwnership.Queries.query655_certified,N12Compact.HistoricalOwnership.Queries.query656_certified,N12Compact.HistoricalOwnership.Queries.query657_certified,N12Compact.HistoricalOwnership.Queries.query658_certified,N12Compact.HistoricalOwnership.Queries.query659_certified,(certified_query% 418),N12Compact.HistoricalOwnership.Queries.query660_certified,N12Compact.HistoricalOwnership.Queries.query661_certified,N12Compact.HistoricalOwnership.Queries.query662_certified,N12Compact.HistoricalOwnership.Queries.query663_certified,N12Compact.HistoricalOwnership.Queries.query664_certified,N12Compact.HistoricalOwnership.Queries.query665_certified,N12Compact.HistoricalOwnership.Queries.query666_certified,N12Compact.HistoricalOwnership.Queries.query667_certified,N12Compact.HistoricalOwnership.Queries.query668_certified,N12Compact.HistoricalOwnership.Queries.query669_certified,N12Compact.HistoricalOwnership.Queries.query670_certified,N12Compact.HistoricalOwnership.Queries.query671_certified,N12Compact.HistoricalOwnership.Queries.query672_certified,N12Compact.HistoricalOwnership.Queries.query673_certified,N12Compact.HistoricalOwnership.Queries.query674_certified,N12Compact.HistoricalOwnership.Queries.query675_certified,N12Compact.HistoricalOwnership.Queries.query676_certified,N12Compact.HistoricalOwnership.Queries.query677_certified,N12Compact.HistoricalOwnership.Queries.query678_certified,N12Compact.HistoricalOwnership.Queries.query679_certified,N12Compact.HistoricalOwnership.Queries.query680_certified,N12Compact.HistoricalOwnership.Queries.query681_certified,N12Compact.HistoricalOwnership.Queries.query682_certified,N12Compact.HistoricalOwnership.Queries.query683_certified,N12Compact.HistoricalOwnership.Queries.query684_certified,N12Compact.HistoricalOwnership.Queries.query685_certified,N12Compact.HistoricalOwnership.Queries.query686_certified,N12Compact.HistoricalOwnership.Queries.query687_certified,(certified_query% 419),N12Compact.HistoricalOwnership.Queries.query688_certified,N12Compact.HistoricalOwnership.Queries.query689_certified,N12Compact.HistoricalOwnership.Queries.query690_certified,N12Compact.HistoricalOwnership.Queries.query691_certified,N12Compact.HistoricalOwnership.Queries.query692_certified,N12Compact.HistoricalOwnership.Queries.query693_certified,N12Compact.HistoricalOwnership.Queries.query694_certified,N12Compact.HistoricalOwnership.Queries.query695_certified,N12Compact.HistoricalOwnership.Queries.query696_certified,N12Compact.HistoricalOwnership.Queries.query697_certified,N12Compact.HistoricalOwnership.Queries.query698_certified,N12Compact.HistoricalOwnership.Queries.query699_certified,N12Compact.HistoricalOwnership.Queries.query700_certified,N12Compact.HistoricalOwnership.Queries.query701_certified,N12Compact.HistoricalOwnership.Queries.query702_certified,N12Compact.HistoricalOwnership.Queries.query703_certified,N12Compact.HistoricalOwnership.Queries.query704_certified,N12Compact.HistoricalOwnership.Queries.query705_certified,N12Compact.HistoricalOwnership.Queries.query706_certified,N12Compact.HistoricalOwnership.Queries.query707_certified,N12Compact.HistoricalOwnership.Queries.query708_certified,N12Compact.HistoricalOwnership.Queries.query709_certified,N12Compact.HistoricalOwnership.Queries.query710_certified,N12Compact.HistoricalOwnership.Queries.query711_certified,N12Compact.HistoricalOwnership.Queries.query712_certified,N12Compact.HistoricalOwnership.Queries.query713_certified,N12Compact.HistoricalOwnership.Queries.query714_certified,N12Compact.HistoricalOwnership.Queries.query715_certified,N12Compact.HistoricalOwnership.Queries.query716_certified,N12Compact.HistoricalOwnership.Queries.query717_certified,N12Compact.HistoricalOwnership.Queries.query718_certified,N12Compact.HistoricalOwnership.Queries.query719_certified,N12Compact.HistoricalOwnership.Queries.query720_certified,N12Compact.HistoricalOwnership.Queries.query721_certified,N12Compact.HistoricalOwnership.Queries.query722_certified,N12Compact.HistoricalOwnership.Queries.query723_certified,N12Compact.HistoricalOwnership.Queries.query724_certified,N12Compact.HistoricalOwnership.Queries.query725_certified,N12Compact.HistoricalOwnership.Queries.query726_certified,N12Compact.HistoricalOwnership.Queries.query727_certified,N12Compact.HistoricalOwnership.Queries.query728_certified,N12Compact.HistoricalOwnership.Queries.query729_certified,N12Compact.HistoricalOwnership.Queries.query730_certified,N12Compact.HistoricalOwnership.Queries.query731_certified,N12Compact.HistoricalOwnership.Queries.query732_certified,N12Compact.HistoricalOwnership.Queries.query733_certified,N12Compact.HistoricalOwnership.Queries.query734_certified,N12Compact.HistoricalOwnership.Queries.query735_certified,N12Compact.HistoricalOwnership.Queries.query736_certified,N12Compact.HistoricalOwnership.Queries.query737_certified,N12Compact.HistoricalOwnership.Queries.query738_certified,N12Compact.HistoricalOwnership.Queries.query739_certified,N12Compact.HistoricalOwnership.Queries.query740_certified,N12Compact.HistoricalOwnership.Queries.query741_certified,N12Compact.HistoricalOwnership.Queries.query742_certified,N12Compact.HistoricalOwnership.Queries.query743_certified,N12Compact.HistoricalOwnership.Queries.query744_certified,N12Compact.HistoricalOwnership.Queries.query745_certified,N12Compact.HistoricalOwnership.Queries.query746_certified,N12Compact.HistoricalOwnership.Queries.query747_certified,N12Compact.HistoricalOwnership.Queries.query748_certified,N12Compact.HistoricalOwnership.Queries.query749_certified,N12Compact.HistoricalOwnership.Queries.query750_certified,N12Compact.HistoricalOwnership.Queries.query751_certified,N12Compact.HistoricalOwnership.Queries.query752_certified,N12Compact.HistoricalOwnership.Queries.query753_certified,N12Compact.HistoricalOwnership.Queries.query754_certified,N12Compact.HistoricalOwnership.Queries.query755_certified,N12Compact.HistoricalOwnership.Queries.query756_certified,N12Compact.HistoricalOwnership.Queries.query757_certified,N12Compact.HistoricalOwnership.Queries.query758_certified,N12Compact.HistoricalOwnership.Queries.query759_certified,N12Compact.HistoricalOwnership.Queries.query760_certified,N12Compact.HistoricalOwnership.Queries.query761_certified,N12Compact.HistoricalOwnership.Queries.query762_certified,N12Compact.HistoricalOwnership.Queries.query763_certified,N12Compact.HistoricalOwnership.Queries.query764_certified,N12Compact.HistoricalOwnership.Queries.query765_certified,N12Compact.HistoricalOwnership.Queries.query766_certified,N12Compact.HistoricalOwnership.Queries.query767_certified,N12Compact.HistoricalOwnership.Queries.query768_certified]⟩
private def single717_4_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32,1,{0}),(32,1,{1}),(32,1,{0,1}),(32,1,{2}),(32,1,{0,2}),(32,1,{1,2}),(32,1,{0,1,2}),(32,1,{3}),(32,1,{0,3}),(32,1,{1,3}),(32,1,{0,1,3}),(32,1,{2,3}),(32,1,{0,2,3}),(32,1,{1,2,3}),(32,1,{4}),(32,1,{0,4}),(32,1,{1,4}),(32,1,{0,1,4}),(32,1,{2,4}),(32,1,{0,2,4}),(32,1,{1,2,4}),(32,1,{3,4}),(32,1,{0,3,4}),(32,1,{1,3,4}),(32,1,{2,3,4}),(32,1,{5}),(32,1,{0,5}),(32,1,{1,5}),(32,1,{0,1,5}),(32,1,{2,5}),(32,1,{0,2,5}),(32,1,{1,2,5}),(32,1,{3,5}),(32,1,{0,3,5}),(32,1,{1,3,5}),(32,1,{2,3,5}),(32,1,{4,5}),(32,1,{0,4,5}),(32,1,{1,4,5}),(32,1,{2,4,5}),(32,1,{3,4,5}),(32,1,{6}),(32,1,{0,6}),(32,1,{1,6}),(32,1,{0,1,6}),(32,1,{2,6}),(32,1,{0,2,6}),(32,1,{1,2,6}),(32,1,{3,6}),(32,1,{0,3,6}),(32,1,{1,3,6}),(32,1,{2,3,6}),(32,1,{4,6}),(32,1,{0,4,6}),(32,1,{1,4,6}),(32,1,{2,4,6}),(32,1,{3,4,6}),(32,1,{5,6}),(32,1,{0,5,6}),(32,1,{1,5,6}),(32,1,{2,5,6}),(32,1,{3,5,6}),(32,1,{4,5,6}),(32,1,{7}),(32,1,{0,7}),(32,1,{1,7}),(32,1,{0,1,7}),(32,1,{2,7}),(32,1,{0,2,7}),(32,1,{1,2,7}),(32,1,{3,7}),(32,1,{0,3,7}),(32,1,{1,3,7}),(32,1,{2,3,7}),(32,1,{4,7}),(32,1,{0,4,7}),(32,1,{1,4,7}),(32,1,{2,4,7}),(32,1,{3,4,7}),(32,1,{5,7}),(32,1,{0,5,7}),(32,1,{1,5,7}),(32,1,{2,5,7}),(32,1,{3,5,7}),(32,1,{4,5,7}),(32,1,{6,7}),(32,1,{0,6,7}),(32,1,{1,6,7}),(32,1,{2,6,7}),(32,1,{3,6,7}),(32,1,{4,6,7}),(32,1,{5,6,7}),(32,1,{8}),(32,1,{0,8}),(32,1,{1,8}),(32,1,{0,1,8}),(32,1,{2,8}),(32,1,{0,2,8}),(32,1,{1,2,8}),(32,1,{3,8}),(32,1,{0,3,8}),(32,1,{1,3,8}),(32,1,{2,3,8}),(32,1,{4,8}),(32,1,{0,4,8}),(32,1,{1,4,8}),(32,1,{2,4,8}),(32,1,{3,4,8}),(32,1,{5,8}),(32,1,{0,5,8}),(32,1,{1,5,8}),(32,1,{2,5,8}),(32,1,{3,5,8}),(32,1,{4,5,8}),(32,1,{6,8}),(32,1,{0,6,8}),(32,1,{1,6,8}),(32,1,{2,6,8}),(32,1,{3,6,8}),(32,1,{4,6,8}),(32,1,{5,6,8}),(32,1,{7,8}),(32,1,{0,7,8}),(32,1,{1,7,8}),(32,1,{2,7,8}),(32,1,{3,7,8}),(32,1,{4,7,8}),(32,1,{5,7,8}),(32,1,{6,7,8}),(32,1,{0,9}),(32,1,{1,9}),(32,1,{0,1,9}),(32,1,{2,9}),(32,1,{0,2,9}),(32,1,{1,2,9}),(32,1,{3,9}),(32,1,{0,3,9}),(32,1,{1,3,9}),(32,1,{2,3,9}),(32,1,{4,9}),(32,1,{0,4,9}),(32,1,{1,4,9}),(32,1,{2,4,9}),(32,1,{3,4,9}),(32,1,{5,9}),(32,1,{0,5,9}),(32,1,{1,5,9}),(32,1,{2,5,9}),(32,1,{3,5,9}),(32,1,{4,5,9}),(32,1,{6,9}),(32,1,{0,6,9}),(32,1,{1,6,9}),(32,1,{2,6,9}),(32,1,{3,6,9}),(32,1,{4,6,9}),(32,1,{5,6,9}),(32,1,{7,9}),(32,1,{0,7,9}),(32,1,{1,7,9}),(32,1,{2,7,9}),(32,1,{3,7,9}),(32,1,{4,7,9}),(32,1,{5,7,9}),(32,1,{6,7,9}),(32,1,{8,9}),(32,1,{0,8,9}),(32,1,{1,8,9}),(32,1,{2,8,9}),(32,1,{3,8,9}),(32,1,{4,8,9}),(32,1,{5,8,9}),(32,1,{6,8,9}),(32,1,{7,8,9})]
private theorem single717_4_1_queries_exact :
    single717_4_1Signatures = single717_4_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_4_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{9}] : List (Finset Nat)) ∨ (32,1,owned) ∈ single717_4_1Signatures

private instance : DecidablePred single717_4_1_owned_claim := fun index => by
  unfold single717_4_1_owned_claim
  infer_instance

private theorem single717_4_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_4_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_4_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_4_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_4_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_4_1 case717Family 1 single717_4_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨32,1,3,[{9}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_4_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_4_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_4_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_4_1_owned_block0
      · exact single717_4_1_owned_block1
      · exact single717_4_1_owned_block2
      · exact single717_4_1_owned_block3
      · exact single717_4_1_owned_block4
      · exact single717_4_1_owned_block5
      · exact single717_4_1_owned_block6
      · exact single717_4_1_owned_block7
      · exact single717_4_1_owned_block8
      · exact single717_4_1_owned_block9
      · exact single717_4_1_owned_block10
      · exact single717_4_1_owned_block11
      · exact single717_4_1_owned_block12
      · exact single717_4_1_owned_block13
      · exact single717_4_1_owned_block14
      · exact single717_4_1_owned_block15
      · exact single717_4_1_owned_block16
      · exact single717_4_1_owned_block17
      · exact single717_4_1_owned_block18
      · exact single717_4_1_owned_block19
      · exact single717_4_1_owned_block20
      · exact single717_4_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_4_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_4_1_checked : single717_4_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_4_1 case717Family 1
    single717_4_1Signatures single717_4_1_queries_exact (by decide) single717_4_1_metadata

def single717_5_0 : DirectSingleDomain := ⟨192,0,0,[∅],[]⟩
private def single717_5_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  []
theorem single717_5_0_checked : single717_5_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_5_0 case717Family 0
    single717_5_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_5_1 : DirectSingleDomain := ⟨192,0,2,[∅,{1},{4},{1,4}],[N12Compact.HistoricalOwnership.Queries.query769_certified,N12Compact.HistoricalOwnership.Queries.query770_certified,N12Compact.HistoricalOwnership.Queries.query771_certified,N12Compact.HistoricalOwnership.Queries.query772_certified,N12Compact.HistoricalOwnership.Queries.query773_certified,N12Compact.HistoricalOwnership.Queries.query774_certified,N12Compact.HistoricalOwnership.Queries.query775_certified,N12Compact.HistoricalOwnership.Queries.query776_certified,N12Compact.HistoricalOwnership.Queries.query777_certified,N12Compact.HistoricalOwnership.Queries.query778_certified,N12Compact.HistoricalOwnership.Queries.query779_certified,N12Compact.HistoricalOwnership.Queries.query780_certified,N12Compact.HistoricalOwnership.Queries.query781_certified,N12Compact.HistoricalOwnership.Queries.query782_certified,N12Compact.HistoricalOwnership.Queries.query783_certified,N12Compact.HistoricalOwnership.Queries.query784_certified,N12Compact.HistoricalOwnership.Queries.query785_certified,N12Compact.HistoricalOwnership.Queries.query786_certified,N12Compact.HistoricalOwnership.Queries.query787_certified,N12Compact.HistoricalOwnership.Queries.query788_certified,N12Compact.HistoricalOwnership.Queries.query789_certified,N12Compact.HistoricalOwnership.Queries.query790_certified,N12Compact.HistoricalOwnership.Queries.query791_certified,N12Compact.HistoricalOwnership.Queries.query792_certified,N12Compact.HistoricalOwnership.Queries.query793_certified,N12Compact.HistoricalOwnership.Queries.query794_certified,N12Compact.HistoricalOwnership.Queries.query795_certified,N12Compact.HistoricalOwnership.Queries.query796_certified,N12Compact.HistoricalOwnership.Queries.query797_certified,N12Compact.HistoricalOwnership.Queries.query798_certified,N12Compact.HistoricalOwnership.Queries.query799_certified,N12Compact.HistoricalOwnership.Queries.query800_certified,N12Compact.HistoricalOwnership.Queries.query801_certified,N12Compact.HistoricalOwnership.Queries.query802_certified,N12Compact.HistoricalOwnership.Queries.query803_certified,N12Compact.HistoricalOwnership.Queries.query804_certified,N12Compact.HistoricalOwnership.Queries.query805_certified,N12Compact.HistoricalOwnership.Queries.query806_certified,N12Compact.HistoricalOwnership.Queries.query807_certified,N12Compact.HistoricalOwnership.Queries.query808_certified,N12Compact.HistoricalOwnership.Queries.query809_certified,N12Compact.HistoricalOwnership.Queries.query810_certified,N12Compact.HistoricalOwnership.Queries.query811_certified,N12Compact.HistoricalOwnership.Queries.query812_certified,N12Compact.HistoricalOwnership.Queries.query813_certified,N12Compact.HistoricalOwnership.Queries.query814_certified,N12Compact.HistoricalOwnership.Queries.query815_certified,N12Compact.HistoricalOwnership.Queries.query816_certified,N12Compact.HistoricalOwnership.Queries.query817_certified,N12Compact.HistoricalOwnership.Queries.query818_certified,N12Compact.HistoricalOwnership.Queries.query819_certified,N12Compact.HistoricalOwnership.Queries.query820_certified]⟩
private def single717_5_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,1,{0}),(192,1,{0,1}),(192,1,{2}),(192,1,{0,2}),(192,1,{1,2}),(192,1,{3}),(192,1,{0,3}),(192,1,{1,3}),(192,1,{2,3}),(192,1,{0,4}),(192,1,{2,4}),(192,1,{3,4}),(192,1,{5}),(192,1,{0,5}),(192,1,{1,5}),(192,1,{2,5}),(192,1,{3,5}),(192,1,{4,5}),(192,1,{6}),(192,1,{0,6}),(192,1,{1,6}),(192,1,{2,6}),(192,1,{3,6}),(192,1,{4,6}),(192,1,{5,6}),(192,1,{7}),(192,1,{0,7}),(192,1,{1,7}),(192,1,{2,7}),(192,1,{3,7}),(192,1,{4,7}),(192,1,{5,7}),(192,1,{6,7}),(192,1,{8}),(192,1,{0,8}),(192,1,{1,8}),(192,1,{2,8}),(192,1,{3,8}),(192,1,{4,8}),(192,1,{5,8}),(192,1,{6,8}),(192,1,{7,8}),(192,1,{9}),(192,1,{0,9}),(192,1,{1,9}),(192,1,{2,9}),(192,1,{3,9}),(192,1,{4,9}),(192,1,{5,9}),(192,1,{6,9}),(192,1,{7,9}),(192,1,{8,9})]
theorem single717_5_1_checked : single717_5_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomain.checked single717_5_1 case717Family 1
    single717_5_1Signatures (by rfl) (by decide) (by decide +kernel)

end
end S12
