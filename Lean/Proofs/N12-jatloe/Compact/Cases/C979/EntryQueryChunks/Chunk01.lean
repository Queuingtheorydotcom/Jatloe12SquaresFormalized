import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_0_1 : DirectSingleDomain := ⟨1,1,3,[{2},{0,2}],[N12Compact.C979SharedSelections.selected54,N12Compact.C979SharedSelections.selected55,N12Compact.C979SharedSelections.selected56,N12Compact.C979SharedSelections.selected57,N12Compact.HistoricalOwnership.Queries.query146_certified,N12Compact.C979SharedSelections.selected58,N12Compact.C979SharedSelections.selected59,N12Compact.C979SharedSelections.selected60,N12Compact.HistoricalOwnership.Queries.query147_certified,N12Compact.C979SharedSelections.selected61,N12Compact.HistoricalOwnership.Queries.query148_certified,N12Compact.HistoricalOwnership.Queries.query149_certified,N12Compact.C979SharedSelections.selected62,N12Compact.C979SharedSelections.selected63,N12Compact.C979SharedSelections.selected64,N12Compact.HistoricalOwnership.Queries.query150_certified,N12Compact.C979SharedSelections.selected65,N12Compact.HistoricalOwnership.Queries.query151_certified,N12Compact.HistoricalOwnership.Queries.query152_certified,N12Compact.C979SharedSelections.selected66,N12Compact.HistoricalOwnership.Queries.query153_certified,N12Compact.HistoricalOwnership.Queries.query154_certified,N12Compact.HistoricalOwnership.Queries.query155_certified,N12Compact.C979SharedSelections.selected67,N12Compact.C979SharedSelections.selected68,N12Compact.C979SharedSelections.selected69,N12Compact.HistoricalOwnership.Queries.query156_certified,N12Compact.C979SharedSelections.selected70,N12Compact.HistoricalOwnership.Queries.query157_certified,N12Compact.HistoricalOwnership.Queries.query158_certified,N12Compact.C979SharedSelections.selected71,N12Compact.HistoricalOwnership.Queries.query159_certified,N12Compact.HistoricalOwnership.Queries.query160_certified,N12Compact.HistoricalOwnership.Queries.query161_certified,N12Compact.C979SharedSelections.selected72,N12Compact.HistoricalOwnership.Queries.query162_certified,N12Compact.HistoricalOwnership.Queries.query163_certified,N12Compact.HistoricalOwnership.Queries.query164_certified,N12Compact.HistoricalOwnership.Queries.query165_certified,N12Compact.C979SharedSelections.selected73,N12Compact.C979SharedSelections.selected74,N12Compact.C979SharedSelections.selected75,N12Compact.HistoricalOwnership.Queries.query166_certified,N12Compact.C979SharedSelections.selected76,N12Compact.HistoricalOwnership.Queries.query167_certified,N12Compact.HistoricalOwnership.Queries.query168_certified,N12Compact.C979SharedSelections.selected77,N12Compact.HistoricalOwnership.Queries.query169_certified,N12Compact.HistoricalOwnership.Queries.query170_certified,N12Compact.HistoricalOwnership.Queries.query171_certified,N12Compact.C979SharedSelections.selected78,N12Compact.HistoricalOwnership.Queries.query172_certified,N12Compact.HistoricalOwnership.Queries.query173_certified,N12Compact.HistoricalOwnership.Queries.query174_certified,N12Compact.HistoricalOwnership.Queries.query175_certified,N12Compact.C979SharedSelections.selected79,N12Compact.HistoricalOwnership.Queries.query176_certified,N12Compact.HistoricalOwnership.Queries.query177_certified,N12Compact.HistoricalOwnership.Queries.query178_certified,N12Compact.HistoricalOwnership.Queries.query179_certified,N12Compact.HistoricalOwnership.Queries.query180_certified,N12Compact.C979SharedSelections.selected80,N12Compact.C979SharedSelections.selected81,N12Compact.C979SharedSelections.selected82,N12Compact.HistoricalOwnership.Queries.query181_certified,N12Compact.C979SharedSelections.selected83,N12Compact.HistoricalOwnership.Queries.query182_certified,N12Compact.HistoricalOwnership.Queries.query183_certified,N12Compact.C979SharedSelections.selected84,N12Compact.HistoricalOwnership.Queries.query184_certified,N12Compact.HistoricalOwnership.Queries.query185_certified,N12Compact.HistoricalOwnership.Queries.query186_certified,N12Compact.C979SharedSelections.selected85,N12Compact.HistoricalOwnership.Queries.query187_certified,N12Compact.HistoricalOwnership.Queries.query188_certified,N12Compact.HistoricalOwnership.Queries.query189_certified,N12Compact.HistoricalOwnership.Queries.query190_certified,N12Compact.C979SharedSelections.selected86,N12Compact.HistoricalOwnership.Queries.query191_certified,N12Compact.HistoricalOwnership.Queries.query192_certified,N12Compact.HistoricalOwnership.Queries.query193_certified,N12Compact.HistoricalOwnership.Queries.query194_certified,N12Compact.HistoricalOwnership.Queries.query195_certified,N12Compact.C979SharedSelections.selected87,N12Compact.HistoricalOwnership.Queries.query196_certified,N12Compact.HistoricalOwnership.Queries.query197_certified,N12Compact.HistoricalOwnership.Queries.query198_certified,N12Compact.HistoricalOwnership.Queries.query199_certified,N12Compact.HistoricalOwnership.Queries.query200_certified,N12Compact.HistoricalOwnership.Queries.query201_certified,N12Compact.C979SharedSelections.selected88,N12Compact.C979SharedSelections.selected89,N12Compact.C979SharedSelections.selected90,N12Compact.HistoricalOwnership.Queries.query202_certified,N12Compact.C979SharedSelections.selected91,N12Compact.HistoricalOwnership.Queries.query203_certified,N12Compact.HistoricalOwnership.Queries.query204_certified,N12Compact.C979SharedSelections.selected92,N12Compact.HistoricalOwnership.Queries.query205_certified,N12Compact.HistoricalOwnership.Queries.query206_certified,N12Compact.HistoricalOwnership.Queries.query207_certified,N12Compact.C979SharedSelections.selected93,N12Compact.HistoricalOwnership.Queries.query208_certified,N12Compact.HistoricalOwnership.Queries.query209_certified,N12Compact.HistoricalOwnership.Queries.query210_certified,N12Compact.HistoricalOwnership.Queries.query211_certified,N12Compact.C979SharedSelections.selected94,N12Compact.HistoricalOwnership.Queries.query212_certified,N12Compact.HistoricalOwnership.Queries.query213_certified,N12Compact.HistoricalOwnership.Queries.query214_certified,N12Compact.HistoricalOwnership.Queries.query215_certified,N12Compact.HistoricalOwnership.Queries.query216_certified,N12Compact.C979SharedSelections.selected95,N12Compact.HistoricalOwnership.Queries.query217_certified,N12Compact.HistoricalOwnership.Queries.query218_certified,N12Compact.HistoricalOwnership.Queries.query219_certified,N12Compact.HistoricalOwnership.Queries.query220_certified,N12Compact.HistoricalOwnership.Queries.query221_certified,N12Compact.HistoricalOwnership.Queries.query222_certified,N12Compact.C979SharedSelections.selected96,N12Compact.HistoricalOwnership.Queries.query223_certified,N12Compact.HistoricalOwnership.Queries.query224_certified,N12Compact.HistoricalOwnership.Queries.query225_certified,N12Compact.HistoricalOwnership.Queries.query226_certified,N12Compact.HistoricalOwnership.Queries.query227_certified,N12Compact.HistoricalOwnership.Queries.query228_certified,N12Compact.HistoricalOwnership.Queries.query229_certified,N12Compact.C979SharedSelections.selected97,N12Compact.C979SharedSelections.selected98,N12Compact.C979SharedSelections.selected99,N12Compact.HistoricalOwnership.Queries.query230_certified,N12Compact.C979SharedSelections.selected100,N12Compact.HistoricalOwnership.Queries.query231_certified,N12Compact.HistoricalOwnership.Queries.query232_certified,N12Compact.C979SharedSelections.selected101,N12Compact.HistoricalOwnership.Queries.query233_certified,N12Compact.HistoricalOwnership.Queries.query234_certified,N12Compact.HistoricalOwnership.Queries.query235_certified,N12Compact.C979SharedSelections.selected102,N12Compact.HistoricalOwnership.Queries.query236_certified,N12Compact.HistoricalOwnership.Queries.query237_certified,N12Compact.HistoricalOwnership.Queries.query238_certified,N12Compact.HistoricalOwnership.Queries.query239_certified,N12Compact.C979SharedSelections.selected103,N12Compact.HistoricalOwnership.Queries.query240_certified,N12Compact.HistoricalOwnership.Queries.query241_certified,N12Compact.HistoricalOwnership.Queries.query242_certified,N12Compact.HistoricalOwnership.Queries.query243_certified,N12Compact.HistoricalOwnership.Queries.query244_certified,N12Compact.C979SharedSelections.selected104,N12Compact.HistoricalOwnership.Queries.query245_certified,N12Compact.HistoricalOwnership.Queries.query246_certified,N12Compact.HistoricalOwnership.Queries.query247_certified,N12Compact.HistoricalOwnership.Queries.query248_certified,N12Compact.HistoricalOwnership.Queries.query249_certified,N12Compact.HistoricalOwnership.Queries.query250_certified,N12Compact.C979SharedSelections.selected105,N12Compact.HistoricalOwnership.Queries.query251_certified,N12Compact.HistoricalOwnership.Queries.query252_certified,N12Compact.HistoricalOwnership.Queries.query253_certified,N12Compact.HistoricalOwnership.Queries.query254_certified,N12Compact.HistoricalOwnership.Queries.query255_certified,N12Compact.HistoricalOwnership.Queries.query256_certified,N12Compact.HistoricalOwnership.Queries.query257_certified,N12Compact.C979SharedSelections.selected106,N12Compact.HistoricalOwnership.Queries.query258_certified,N12Compact.HistoricalOwnership.Queries.query259_certified,N12Compact.HistoricalOwnership.Queries.query260_certified,N12Compact.HistoricalOwnership.Queries.query261_certified,N12Compact.HistoricalOwnership.Queries.query262_certified,N12Compact.HistoricalOwnership.Queries.query263_certified,N12Compact.HistoricalOwnership.Queries.query264_certified,N12Compact.HistoricalOwnership.Queries.query265_certified]⟩
#check single979_0_1

private def single979_0_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,1,{0}),(1,1,{1}),(1,1,{0,1}),(1,1,{1,2}),(1,1,{0,1,2}),(1,1,{3}),(1,1,{0,3}),(1,1,{1,3}),(1,1,{0,1,3}),(1,1,{2,3}),(1,1,{0,2,3}),(1,1,{1,2,3}),(1,1,{4}),(1,1,{0,4}),(1,1,{1,4}),(1,1,{0,1,4}),(1,1,{2,4}),(1,1,{0,2,4}),(1,1,{1,2,4}),(1,1,{3,4}),(1,1,{0,3,4}),(1,1,{1,3,4}),(1,1,{2,3,4}),(1,1,{5}),(1,1,{0,5}),(1,1,{1,5}),(1,1,{0,1,5}),(1,1,{2,5}),(1,1,{0,2,5}),(1,1,{1,2,5}),(1,1,{3,5}),(1,1,{0,3,5}),(1,1,{1,3,5}),(1,1,{2,3,5}),(1,1,{4,5}),(1,1,{0,4,5}),(1,1,{1,4,5}),(1,1,{2,4,5}),(1,1,{3,4,5}),(1,1,{6}),(1,1,{0,6}),(1,1,{1,6}),(1,1,{0,1,6}),(1,1,{2,6}),(1,1,{0,2,6}),(1,1,{1,2,6}),(1,1,{3,6}),(1,1,{0,3,6}),(1,1,{1,3,6}),(1,1,{2,3,6}),(1,1,{4,6}),(1,1,{0,4,6}),(1,1,{1,4,6}),(1,1,{2,4,6}),(1,1,{3,4,6}),(1,1,{5,6}),(1,1,{0,5,6}),(1,1,{1,5,6}),(1,1,{2,5,6}),(1,1,{3,5,6}),(1,1,{4,5,6}),(1,1,{7}),(1,1,{0,7}),(1,1,{1,7}),(1,1,{0,1,7}),(1,1,{2,7}),(1,1,{0,2,7}),(1,1,{1,2,7}),(1,1,{3,7}),(1,1,{0,3,7}),(1,1,{1,3,7}),(1,1,{2,3,7}),(1,1,{4,7}),(1,1,{0,4,7}),(1,1,{1,4,7}),(1,1,{2,4,7}),(1,1,{3,4,7}),(1,1,{5,7}),(1,1,{0,5,7}),(1,1,{1,5,7}),(1,1,{2,5,7}),(1,1,{3,5,7}),(1,1,{4,5,7}),(1,1,{6,7}),(1,1,{0,6,7}),(1,1,{1,6,7}),(1,1,{2,6,7}),(1,1,{3,6,7}),(1,1,{4,6,7}),(1,1,{5,6,7}),(1,1,{8}),(1,1,{0,8}),(1,1,{1,8}),(1,1,{0,1,8}),(1,1,{2,8}),(1,1,{0,2,8}),(1,1,{1,2,8}),(1,1,{3,8}),(1,1,{0,3,8}),(1,1,{1,3,8}),(1,1,{2,3,8}),(1,1,{4,8}),(1,1,{0,4,8}),(1,1,{1,4,8}),(1,1,{2,4,8}),(1,1,{3,4,8}),(1,1,{5,8}),(1,1,{0,5,8}),(1,1,{1,5,8}),(1,1,{2,5,8}),(1,1,{3,5,8}),(1,1,{4,5,8}),(1,1,{6,8}),(1,1,{0,6,8}),(1,1,{1,6,8}),(1,1,{2,6,8}),(1,1,{3,6,8}),(1,1,{4,6,8}),(1,1,{5,6,8}),(1,1,{7,8}),(1,1,{0,7,8}),(1,1,{1,7,8}),(1,1,{2,7,8}),(1,1,{3,7,8}),(1,1,{4,7,8}),(1,1,{5,7,8}),(1,1,{6,7,8}),(1,1,{9}),(1,1,{0,9}),(1,1,{1,9}),(1,1,{0,1,9}),(1,1,{2,9}),(1,1,{0,2,9}),(1,1,{1,2,9}),(1,1,{3,9}),(1,1,{0,3,9}),(1,1,{1,3,9}),(1,1,{2,3,9}),(1,1,{4,9}),(1,1,{0,4,9}),(1,1,{1,4,9}),(1,1,{2,4,9}),(1,1,{3,4,9}),(1,1,{5,9}),(1,1,{0,5,9}),(1,1,{1,5,9}),(1,1,{2,5,9}),(1,1,{3,5,9}),(1,1,{4,5,9}),(1,1,{6,9}),(1,1,{0,6,9}),(1,1,{1,6,9}),(1,1,{2,6,9}),(1,1,{3,6,9}),(1,1,{4,6,9}),(1,1,{5,6,9}),(1,1,{7,9}),(1,1,{0,7,9}),(1,1,{1,7,9}),(1,1,{2,7,9}),(1,1,{3,7,9}),(1,1,{4,7,9}),(1,1,{5,7,9}),(1,1,{6,7,9}),(1,1,{8,9}),(1,1,{0,8,9}),(1,1,{1,8,9}),(1,1,{2,8,9}),(1,1,{3,8,9}),(1,1,{4,8,9}),(1,1,{5,8,9}),(1,1,{6,8,9}),(1,1,{7,8,9})]
#check single979_0_1Signatures

private theorem single979_0_1_queries_exact :
    single979_0_1Signatures = single979_0_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_0_1_queries_exact

private def single979_0_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{2},{0,2}] : List (Finset Nat)) ∨ (1,1,owned) ∈ single979_0_1Signatures

private instance : DecidablePred single979_0_1_owned_claim := fun index => by
  unfold single979_0_1_owned_claim
  infer_instance

private theorem single979_0_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_0_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_0_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_0_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_0_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_0_1 case979Family 1 single979_0_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨1,1,3,[{2},{0,2}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_0_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_0_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_0_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_0_1_owned_block0
      · exact single979_0_1_owned_block1
      · exact single979_0_1_owned_block2
      · exact single979_0_1_owned_block3
      · exact single979_0_1_owned_block4
      · exact single979_0_1_owned_block5
      · exact single979_0_1_owned_block6
      · exact single979_0_1_owned_block7
      · exact single979_0_1_owned_block8
      · exact single979_0_1_owned_block9
      · exact single979_0_1_owned_block10
      · exact single979_0_1_owned_block11
      · exact single979_0_1_owned_block12
      · exact single979_0_1_owned_block13
      · exact single979_0_1_owned_block14
      · exact single979_0_1_owned_block15
      · exact single979_0_1_owned_block16
      · exact single979_0_1_owned_block17
      · exact single979_0_1_owned_block18
      · exact single979_0_1_owned_block19
      · exact single979_0_1_owned_block20
      · exact single979_0_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_0_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_0_1_metadata

theorem single979_0_1_checked : single979_0_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_0_1 case979Family 1
    single979_0_1Signatures single979_0_1_queries_exact (by decide) single979_0_1_metadata

end
end S12
