import Compact.Completion.OtherCases.C983.F5NegativeEntrance
import Compact.Completion.OtherCases.RightTripleData

/-! Original actual owners supply the entire remaining E/N/R entrance,
including the real right wall and both full-square disjointness conditions.
The local negative three-square contradiction remains a separate obligation. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f5_three_square_entrance (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    ∃ E N R : OpenSquare,RightTripleData.Input E N R ∧
      (∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2)) ∧
      (∀ x y,N.Inside x y ↔ (owners p 6).Inside (x+2) (y+2)) ∧
      (∀ x y,R.Inside x y ↔ (owners p 10).Inside (x+2) (y+2)) := by
  obtain ⟨E,N,eShape,nShape,ePhysical,nPhysical,eProfile,nProfile,nLeft,nTop⟩ :=
    f5_negative_entrance p hf f5
  have points := f5_top_only_points p hf f5
  have rOrigin : ((owners p 10).translated 2 2).Inside 1 0 := by
    norm_num [inside_translated_iff]
    exact points.2.2.2
  have rUpper : ((owners p 10).translated 2 2).Inside 1 (14/25) := by
    norm_num [inside_translated_iff]
    have final := f5_right_final p hf f5
    exact right_advance_of_omitted_lower p hf
      (by rw [final]; decide +kernel) (by rw [final]; decide +kernel)
  have wall : ∀ x y,((owners p 10).translated 2 2).Inside x y → x≤2 := by
    intro x y own
    have original := (inside_translated_iff _ _ _ _ _).mp own
    have bound := (owners_contained p 10 (x+2) (y+2) original).2.1
    linarith only [bound]
  obtain ⟨R,rShape,rPhysical,rProfile⟩ := RightTripleData.right_frame
    ((owners p 10).translated 2 2) rOrigin rUpper wall
  have physicalRight : ∀ x y,R.Inside x y ↔ (owners p 10).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff] using rPhysical x y
  have sameEN : E.side=N.side := by
    rw [eShape,nShape]
    exact owners_same_side p 5 6
  have sameER : E.side=R.side := by
    rw [eShape,rShape]
    exact owners_same_side p 5 10
  have marker : E.Inside (7/20) (-7/20) := by
    apply (ePhysical _ _).mpr
    norm_num
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : E.Inside (13/50) 0 := by
    apply (ePhysical _ _).mpr
    norm_num
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have sharp : N.Inside (21/40) (1/8) := by
    apply (nPhysical _ _).mpr
    norm_num
    exact points.1
  have apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y) := by
    intro x y own
    exact owners_apart p hf 5 10 (by decide +kernel) _ _
      ⟨(ePhysical _ _).mp own.1,(physicalRight _ _).mp own.2⟩
  have apartNR : ∀ x y,¬(N.Inside x y ∧ R.Inside x y) := by
    intro x y own
    exact owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨(nPhysical _ _).mp own.1,(physicalRight _ _).mp own.2⟩
  exact ⟨E,N,R,⟨sameEN,sameER,eProfile,nProfile,rProfile,marker,elbow,sharp,nTop,nLeft,
    apartER,apartNR⟩,ePhysical,nPhysical,physicalRight⟩

/-- The stronger original-packing context retains all three actual pairwise
disjointness statements. The older `RightTripleData.Input` API is unchanged. -/
structure F5TripleInput (E N R : OpenSquare) : Prop extends RightTripleData.Input E N R where
  apartEN : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)

theorem f5_pairwise_three_square_entrance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f5 : 5∈actual p 7) :
    ∃ E N R : OpenSquare,F5TripleInput E N R ∧
      (∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2)) ∧
      (∀ x y,N.Inside x y ↔ (owners p 6).Inside (x+2) (y+2)) ∧
      (∀ x y,R.Inside x y ↔ (owners p 10).Inside (x+2) (y+2)) := by
  obtain ⟨E,N,R,input,ePhysical,nPhysical,rPhysical⟩ :=
    f5_three_square_entrance p hf f5
  have apartEN : ∀ x y,¬(E.Inside x y ∧ N.Inside x y) := by
    intro x y own
    exact owners_apart p hf 5 6 (by decide +kernel) (x+2) (y+2)
      ⟨(ePhysical x y).mp own.1,(nPhysical x y).mp own.2⟩
  exact ⟨E,N,R,⟨input,apartEN⟩,ePhysical,nPhysical,rPhysical⟩

end
#print axioms f5_three_square_entrance
#print axioms f5_pairwise_three_square_entrance
end N12Compact.Completion.OtherCases.C983
