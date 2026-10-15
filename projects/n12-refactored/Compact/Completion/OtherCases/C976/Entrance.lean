import Compact.Completion.OtherCases.C976.Domains

/-! Authentic original-family compulsory points. Each blocked auxiliary
belongs strictly to a displayed distinct actual owner. Additional allowed
auxiliaries are preserved; there is no asserted 98-vector enumeration. -/
namespace N12Compact.Completion.OtherCases.C976.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

structure Compulsory (p : NormalizedPacking) : Prop where
  southwestF4 : (owners p 5).Inside 2 (87/50)
  southwestG3 : (owners p 5).Inside (87/50) 2
  southeastF8 : (owners p 6).Inside 3 (87/50)
  southeastG : (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside 3 (8/5)
  northeastF : (owners p 7).Inside 2 (113/50) ∨ (owners p 7).Inside (12/5) 3
  northeastG : (owners p 7).Inside (113/50) 2 ∨ (owners p 7).Inside (113/50) 3
  leftF1 : (owners p 8).Inside 1 (113/50)
  leftG1 : (owners p 8).Inside 1 (12/5)
  bottomF6 : (owners p 9).Inside (12/5) 1
  bottomG5 : (owners p 9).Inside (113/50) 1
  rightF9 : (owners p 10).Inside 3 (113/50)
  rightG9 : (owners p 10).Inside 3 (12/5)
  topComponent : (owners p 11).Inside (113/50) 3 ∨
    ((owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3)

theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Compulsory p := by
  have hF0 := singleton_vertical p hf (87/50) (by norm_num) le_rfl
  have hG0 := singleton_vertical p hf (8/5) (by norm_num) (by norm_num)
  have hF2 := singleton_horizontal p hf (8/5) (by norm_num) (by norm_num)
  have hG2 := singleton_horizontal p hf (87/50) (by norm_num) le_rfl
  have f4 : (owners p 5).Inside 2 (87/50) := by
    rcases southwest_f_cover p hf with wrong | wrong | own
    · exact False.elim (apart p hf 5 1 (by decide) _ _ ⟨wrong,hF0⟩)
    · exact False.elim (apart p hf 5 0 (by decide) _ _ ⟨wrong,hF2⟩)
    · exact own
  have g3 : (owners p 5).Inside (87/50) 2 := by
    rcases southwest_g_cover p hf with wrong | wrong | own
    · exact False.elim (apart p hf 5 1 (by decide) _ _ ⟨wrong,hG0⟩)
    · exact False.elim (apart p hf 5 0 (by decide) _ _ ⟨wrong,hG2⟩)
    · exact own
  have f6 : (owners p 9).Inside (12/5) 1 := by
    rcases bottom_f_cover p hf with wrong | wrong | own
    · exact False.elim (apart p hf 9 0 (by decide) _ _ ⟨wrong,hF2⟩)
    · exact False.elim (apart p hf 9 5 (by decide) _ _ ⟨wrong,f4⟩)
    · exact own
  have g5 : (owners p 9).Inside (113/50) 1 :=
    (bottom_g_cover p hf).resolve_left (foreign p hf 9 0 (by decide) _ _ hG2)
  have f8 : (owners p 6).Inside 3 (87/50) := by
    rcases southeast_f_cover p hf with wrong | wrong | own
    · exact False.elim (apart p hf 6 5 (by decide) _ _ ⟨wrong,f4⟩)
    · exact False.elim (apart p hf 6 9 (by decide) _ _ ⟨wrong,f6⟩)
    · exact own
  have right := right_pair p hf (foreign p hf 10 6 (by decide) _ _ f8)
  have left : (owners p 8).Inside 1 (12/5) := by
    rcases left_g_cover p hf with wrong | own | wrong
    · exact False.elim (apart p hf 8 1 (by decide) _ _ ⟨wrong,hG0⟩)
    · exact own
    · exact False.elim (apart p hf 8 5 (by decide) _ _ ⟨wrong,g3⟩)
  refine {
    southwestF4 := f4
    southwestG3 := g3
    southeastF8 := f8
    southeastG := ?_
    northeastF := ?_
    northeastG := ?_
    leftF1 := left_f1_of_g1 p hf left
    leftG1 := left
    bottomF6 := f6
    bottomG5 := g5
    rightF9 := right.1
    rightG9 := right.2
    topComponent := top_component p hf }
  · exact (southeast_g_cover p hf).resolve_left (foreign p hf 6 9 (by decide) _ _ g5)
  · rcases northeast_f_cover p hf with own | own | wrong
    · exact Or.inl own
    · exact Or.inr own
    · exact False.elim (apart p hf 7 10 (by decide) _ _ ⟨wrong,right.1⟩)
  · rcases northeast_g_cover p hf with own | own | wrong
    · exact Or.inl own
    · exact Or.inr own
    · exact False.elim (apart p hf 7 10 (by decide) _ _ ⟨wrong,right.2⟩)

end
#print axioms compulsory
end N12Compact.Completion.OtherCases.C976.OriginalData
