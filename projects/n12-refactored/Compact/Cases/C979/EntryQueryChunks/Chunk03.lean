import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_1_1 : DirectSingleDomain := ⟨2,1,3,[{0}],[N12Compact.C979SharedSelections.selected160,N12Compact.C979SharedSelections.selected161,N12Compact.C979SharedSelections.selected162,N12Compact.C979SharedSelections.selected163,N12Compact.C979SharedSelections.selected164,N12Compact.HistoricalOwnership.Queries.query266_certified,N12Compact.C979SharedSelections.selected165,N12Compact.C979SharedSelections.selected166,N12Compact.C979SharedSelections.selected167,N12Compact.HistoricalOwnership.Queries.query267_certified,N12Compact.C979SharedSelections.selected168,N12Compact.HistoricalOwnership.Queries.query268_certified,N12Compact.HistoricalOwnership.Queries.query269_certified,N12Compact.C979SharedSelections.selected169,N12Compact.C979SharedSelections.selected170,N12Compact.C979SharedSelections.selected171,N12Compact.HistoricalOwnership.Queries.query270_certified,N12Compact.C979SharedSelections.selected172,N12Compact.HistoricalOwnership.Queries.query271_certified,N12Compact.HistoricalOwnership.Queries.query272_certified,N12Compact.C979SharedSelections.selected173,N12Compact.HistoricalOwnership.Queries.query273_certified,N12Compact.HistoricalOwnership.Queries.query274_certified,N12Compact.HistoricalOwnership.Queries.query275_certified,N12Compact.C979SharedSelections.selected174,N12Compact.C979SharedSelections.selected175,N12Compact.C979SharedSelections.selected176,N12Compact.HistoricalOwnership.Queries.query276_certified,N12Compact.C979SharedSelections.selected177,N12Compact.HistoricalOwnership.Queries.query277_certified,N12Compact.HistoricalOwnership.Queries.query278_certified,N12Compact.C979SharedSelections.selected178,N12Compact.HistoricalOwnership.Queries.query279_certified,N12Compact.HistoricalOwnership.Queries.query280_certified,N12Compact.HistoricalOwnership.Queries.query281_certified,N12Compact.C979SharedSelections.selected179,N12Compact.HistoricalOwnership.Queries.query282_certified,N12Compact.HistoricalOwnership.Queries.query283_certified,N12Compact.HistoricalOwnership.Queries.query284_certified,N12Compact.HistoricalOwnership.Queries.query285_certified,N12Compact.C979SharedSelections.selected180,N12Compact.C979SharedSelections.selected181,N12Compact.C979SharedSelections.selected182,N12Compact.HistoricalOwnership.Queries.query286_certified,N12Compact.C979SharedSelections.selected183,N12Compact.HistoricalOwnership.Queries.query287_certified,N12Compact.HistoricalOwnership.Queries.query288_certified,N12Compact.C979SharedSelections.selected184,N12Compact.HistoricalOwnership.Queries.query289_certified,N12Compact.HistoricalOwnership.Queries.query290_certified,N12Compact.HistoricalOwnership.Queries.query291_certified,N12Compact.C979SharedSelections.selected185,N12Compact.HistoricalOwnership.Queries.query292_certified,N12Compact.HistoricalOwnership.Queries.query293_certified,N12Compact.HistoricalOwnership.Queries.query294_certified,N12Compact.HistoricalOwnership.Queries.query295_certified,N12Compact.C979SharedSelections.selected186,N12Compact.HistoricalOwnership.Queries.query296_certified,N12Compact.HistoricalOwnership.Queries.query297_certified,N12Compact.HistoricalOwnership.Queries.query298_certified,N12Compact.HistoricalOwnership.Queries.query299_certified,N12Compact.HistoricalOwnership.Queries.query300_certified,N12Compact.C979SharedSelections.selected187,N12Compact.C979SharedSelections.selected188,N12Compact.C979SharedSelections.selected189,N12Compact.HistoricalOwnership.Queries.query301_certified,N12Compact.C979SharedSelections.selected190,N12Compact.HistoricalOwnership.Queries.query302_certified,N12Compact.HistoricalOwnership.Queries.query303_certified,N12Compact.C979SharedSelections.selected191,N12Compact.HistoricalOwnership.Queries.query304_certified,N12Compact.HistoricalOwnership.Queries.query305_certified,N12Compact.HistoricalOwnership.Queries.query306_certified,N12Compact.C979SharedSelections.selected192,N12Compact.HistoricalOwnership.Queries.query307_certified,N12Compact.HistoricalOwnership.Queries.query308_certified,N12Compact.HistoricalOwnership.Queries.query309_certified,N12Compact.HistoricalOwnership.Queries.query310_certified,N12Compact.C979SharedSelections.selected193,N12Compact.HistoricalOwnership.Queries.query311_certified,N12Compact.HistoricalOwnership.Queries.query312_certified,N12Compact.HistoricalOwnership.Queries.query313_certified,N12Compact.HistoricalOwnership.Queries.query314_certified,N12Compact.HistoricalOwnership.Queries.query315_certified,N12Compact.C979SharedSelections.selected194,N12Compact.HistoricalOwnership.Queries.query316_certified,N12Compact.HistoricalOwnership.Queries.query317_certified,N12Compact.HistoricalOwnership.Queries.query318_certified,N12Compact.HistoricalOwnership.Queries.query319_certified,N12Compact.HistoricalOwnership.Queries.query320_certified,N12Compact.HistoricalOwnership.Queries.query321_certified,N12Compact.C979SharedSelections.selected195,N12Compact.C979SharedSelections.selected196,N12Compact.C979SharedSelections.selected197,N12Compact.HistoricalOwnership.Queries.query322_certified,N12Compact.C979SharedSelections.selected198,N12Compact.HistoricalOwnership.Queries.query323_certified,N12Compact.HistoricalOwnership.Queries.query324_certified,N12Compact.C979SharedSelections.selected199,N12Compact.HistoricalOwnership.Queries.query325_certified,N12Compact.HistoricalOwnership.Queries.query326_certified,N12Compact.HistoricalOwnership.Queries.query327_certified,N12Compact.C979SharedSelections.selected200,N12Compact.HistoricalOwnership.Queries.query328_certified,N12Compact.HistoricalOwnership.Queries.query329_certified,N12Compact.HistoricalOwnership.Queries.query330_certified,N12Compact.HistoricalOwnership.Queries.query331_certified,N12Compact.C979SharedSelections.selected201,N12Compact.HistoricalOwnership.Queries.query332_certified,N12Compact.HistoricalOwnership.Queries.query333_certified,N12Compact.HistoricalOwnership.Queries.query334_certified,N12Compact.HistoricalOwnership.Queries.query335_certified,N12Compact.HistoricalOwnership.Queries.query336_certified,N12Compact.C979SharedSelections.selected202,N12Compact.HistoricalOwnership.Queries.query337_certified,N12Compact.HistoricalOwnership.Queries.query338_certified,N12Compact.HistoricalOwnership.Queries.query339_certified,N12Compact.HistoricalOwnership.Queries.query340_certified,N12Compact.HistoricalOwnership.Queries.query341_certified,N12Compact.HistoricalOwnership.Queries.query342_certified,N12Compact.C979SharedSelections.selected203,N12Compact.HistoricalOwnership.Queries.query343_certified,N12Compact.HistoricalOwnership.Queries.query344_certified,N12Compact.HistoricalOwnership.Queries.query345_certified,N12Compact.HistoricalOwnership.Queries.query346_certified,N12Compact.HistoricalOwnership.Queries.query347_certified,N12Compact.HistoricalOwnership.Queries.query348_certified,N12Compact.HistoricalOwnership.Queries.query349_certified,N12Compact.C979SharedSelections.selected204,N12Compact.C979SharedSelections.selected205,N12Compact.C979SharedSelections.selected206,N12Compact.HistoricalOwnership.Queries.query350_certified,N12Compact.C979SharedSelections.selected207,N12Compact.HistoricalOwnership.Queries.query351_certified,N12Compact.HistoricalOwnership.Queries.query352_certified,N12Compact.C979SharedSelections.selected208,N12Compact.HistoricalOwnership.Queries.query353_certified,N12Compact.HistoricalOwnership.Queries.query354_certified,N12Compact.HistoricalOwnership.Queries.query355_certified,N12Compact.C979SharedSelections.selected209,N12Compact.HistoricalOwnership.Queries.query356_certified,N12Compact.HistoricalOwnership.Queries.query357_certified,N12Compact.HistoricalOwnership.Queries.query358_certified,N12Compact.HistoricalOwnership.Queries.query359_certified,N12Compact.C979SharedSelections.selected210,N12Compact.HistoricalOwnership.Queries.query360_certified,N12Compact.HistoricalOwnership.Queries.query361_certified,N12Compact.HistoricalOwnership.Queries.query362_certified,N12Compact.HistoricalOwnership.Queries.query363_certified,N12Compact.HistoricalOwnership.Queries.query364_certified,N12Compact.C979SharedSelections.selected211,N12Compact.HistoricalOwnership.Queries.query365_certified,N12Compact.HistoricalOwnership.Queries.query366_certified,N12Compact.HistoricalOwnership.Queries.query367_certified,N12Compact.HistoricalOwnership.Queries.query368_certified,N12Compact.HistoricalOwnership.Queries.query369_certified,N12Compact.HistoricalOwnership.Queries.query370_certified,N12Compact.C979SharedSelections.selected212,N12Compact.HistoricalOwnership.Queries.query371_certified,N12Compact.HistoricalOwnership.Queries.query372_certified,N12Compact.HistoricalOwnership.Queries.query373_certified,N12Compact.HistoricalOwnership.Queries.query374_certified,N12Compact.HistoricalOwnership.Queries.query375_certified,N12Compact.HistoricalOwnership.Queries.query376_certified,N12Compact.HistoricalOwnership.Queries.query377_certified,N12Compact.C979SharedSelections.selected213,N12Compact.HistoricalOwnership.Queries.query378_certified,N12Compact.HistoricalOwnership.Queries.query379_certified,N12Compact.HistoricalOwnership.Queries.query380_certified,N12Compact.HistoricalOwnership.Queries.query381_certified,N12Compact.HistoricalOwnership.Queries.query382_certified,N12Compact.HistoricalOwnership.Queries.query383_certified,N12Compact.HistoricalOwnership.Queries.query384_certified,N12Compact.HistoricalOwnership.Queries.query385_certified]⟩
private def single979_1_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,1,{1}),(2,1,{0,1}),(2,1,{2}),(2,1,{0,2}),(2,1,{1,2}),(2,1,{0,1,2}),(2,1,{3}),(2,1,{0,3}),(2,1,{1,3}),(2,1,{0,1,3}),(2,1,{2,3}),(2,1,{0,2,3}),(2,1,{1,2,3}),(2,1,{4}),(2,1,{0,4}),(2,1,{1,4}),(2,1,{0,1,4}),(2,1,{2,4}),(2,1,{0,2,4}),(2,1,{1,2,4}),(2,1,{3,4}),(2,1,{0,3,4}),(2,1,{1,3,4}),(2,1,{2,3,4}),(2,1,{5}),(2,1,{0,5}),(2,1,{1,5}),(2,1,{0,1,5}),(2,1,{2,5}),(2,1,{0,2,5}),(2,1,{1,2,5}),(2,1,{3,5}),(2,1,{0,3,5}),(2,1,{1,3,5}),(2,1,{2,3,5}),(2,1,{4,5}),(2,1,{0,4,5}),(2,1,{1,4,5}),(2,1,{2,4,5}),(2,1,{3,4,5}),(2,1,{6}),(2,1,{0,6}),(2,1,{1,6}),(2,1,{0,1,6}),(2,1,{2,6}),(2,1,{0,2,6}),(2,1,{1,2,6}),(2,1,{3,6}),(2,1,{0,3,6}),(2,1,{1,3,6}),(2,1,{2,3,6}),(2,1,{4,6}),(2,1,{0,4,6}),(2,1,{1,4,6}),(2,1,{2,4,6}),(2,1,{3,4,6}),(2,1,{5,6}),(2,1,{0,5,6}),(2,1,{1,5,6}),(2,1,{2,5,6}),(2,1,{3,5,6}),(2,1,{4,5,6}),(2,1,{7}),(2,1,{0,7}),(2,1,{1,7}),(2,1,{0,1,7}),(2,1,{2,7}),(2,1,{0,2,7}),(2,1,{1,2,7}),(2,1,{3,7}),(2,1,{0,3,7}),(2,1,{1,3,7}),(2,1,{2,3,7}),(2,1,{4,7}),(2,1,{0,4,7}),(2,1,{1,4,7}),(2,1,{2,4,7}),(2,1,{3,4,7}),(2,1,{5,7}),(2,1,{0,5,7}),(2,1,{1,5,7}),(2,1,{2,5,7}),(2,1,{3,5,7}),(2,1,{4,5,7}),(2,1,{6,7}),(2,1,{0,6,7}),(2,1,{1,6,7}),(2,1,{2,6,7}),(2,1,{3,6,7}),(2,1,{4,6,7}),(2,1,{5,6,7}),(2,1,{8}),(2,1,{0,8}),(2,1,{1,8}),(2,1,{0,1,8}),(2,1,{2,8}),(2,1,{0,2,8}),(2,1,{1,2,8}),(2,1,{3,8}),(2,1,{0,3,8}),(2,1,{1,3,8}),(2,1,{2,3,8}),(2,1,{4,8}),(2,1,{0,4,8}),(2,1,{1,4,8}),(2,1,{2,4,8}),(2,1,{3,4,8}),(2,1,{5,8}),(2,1,{0,5,8}),(2,1,{1,5,8}),(2,1,{2,5,8}),(2,1,{3,5,8}),(2,1,{4,5,8}),(2,1,{6,8}),(2,1,{0,6,8}),(2,1,{1,6,8}),(2,1,{2,6,8}),(2,1,{3,6,8}),(2,1,{4,6,8}),(2,1,{5,6,8}),(2,1,{7,8}),(2,1,{0,7,8}),(2,1,{1,7,8}),(2,1,{2,7,8}),(2,1,{3,7,8}),(2,1,{4,7,8}),(2,1,{5,7,8}),(2,1,{6,7,8}),(2,1,{9}),(2,1,{0,9}),(2,1,{1,9}),(2,1,{0,1,9}),(2,1,{2,9}),(2,1,{0,2,9}),(2,1,{1,2,9}),(2,1,{3,9}),(2,1,{0,3,9}),(2,1,{1,3,9}),(2,1,{2,3,9}),(2,1,{4,9}),(2,1,{0,4,9}),(2,1,{1,4,9}),(2,1,{2,4,9}),(2,1,{3,4,9}),(2,1,{5,9}),(2,1,{0,5,9}),(2,1,{1,5,9}),(2,1,{2,5,9}),(2,1,{3,5,9}),(2,1,{4,5,9}),(2,1,{6,9}),(2,1,{0,6,9}),(2,1,{1,6,9}),(2,1,{2,6,9}),(2,1,{3,6,9}),(2,1,{4,6,9}),(2,1,{5,6,9}),(2,1,{7,9}),(2,1,{0,7,9}),(2,1,{1,7,9}),(2,1,{2,7,9}),(2,1,{3,7,9}),(2,1,{4,7,9}),(2,1,{5,7,9}),(2,1,{6,7,9}),(2,1,{8,9}),(2,1,{0,8,9}),(2,1,{1,8,9}),(2,1,{2,8,9}),(2,1,{3,8,9}),(2,1,{4,8,9}),(2,1,{5,8,9}),(2,1,{6,8,9}),(2,1,{7,8,9})]
private theorem single979_1_1_queries_exact :
    single979_1_1Signatures = single979_1_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_1_1_queries_exact

private def single979_1_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{0}] : List (Finset Nat)) ∨ (2,1,owned) ∈ single979_1_1Signatures

private instance : DecidablePred single979_1_1_owned_claim := fun index => by
  unfold single979_1_1_owned_claim
  infer_instance

private theorem single979_1_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_1_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_1_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_1_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_1_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_1_1 case979Family 1 single979_1_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨2,1,3,[{0}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_1_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_1_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_1_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_1_1_owned_block0
      · exact single979_1_1_owned_block1
      · exact single979_1_1_owned_block2
      · exact single979_1_1_owned_block3
      · exact single979_1_1_owned_block4
      · exact single979_1_1_owned_block5
      · exact single979_1_1_owned_block6
      · exact single979_1_1_owned_block7
      · exact single979_1_1_owned_block8
      · exact single979_1_1_owned_block9
      · exact single979_1_1_owned_block10
      · exact single979_1_1_owned_block11
      · exact single979_1_1_owned_block12
      · exact single979_1_1_owned_block13
      · exact single979_1_1_owned_block14
      · exact single979_1_1_owned_block15
      · exact single979_1_1_owned_block16
      · exact single979_1_1_owned_block17
      · exact single979_1_1_owned_block18
      · exact single979_1_1_owned_block19
      · exact single979_1_1_owned_block20
      · exact single979_1_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_1_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_1_1_metadata

theorem single979_1_1_checked : single979_1_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_1_1 case979Family 1
    single979_1_1Signatures single979_1_1_queries_exact (by decide) single979_1_1_metadata

end
end S12
