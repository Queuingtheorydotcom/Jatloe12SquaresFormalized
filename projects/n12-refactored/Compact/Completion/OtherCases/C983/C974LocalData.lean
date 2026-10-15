import Compact.Completion.OtherCases.C983.F4BottomMidpointOriginal
import Compact.Completion.OtherCases.C983.LeftOrigin
import Compact.Completion.OtherCases.C983.TopOnlyPoints

/-! Exact raw input of C974-THREE-SQUARE-ENDING Theorem 1 and the two
actual-owner ledgers needed by the C983 F4 proof. No orientation or
positive-frame consequence is assumed by this raw contract. -/
namespace N12Compact.Completion.OtherCases.C983.C974LocalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

structure Input (K W C : OpenSquare) : Prop where
  sideLarge : 1<K.side
  sameKW : K.side=W.side
  sameKC : K.side=C.side
  lowerWall : ∀ x y,K.Inside x y → -1≤y
  markerK : K.Inside 0 (-43/500)
  pointK : K.Inside (41/50) 0
  seedK : K.Inside (24/25) (-6/25)
  missingK : ¬K.Inside 0 0
  originW : W.Inside 1 0
  markerW : W.Inside 1 (-43/500)
  farW : W.Inside (9/5) 0
  missingMarker : ¬W.Inside (27/20) (13/20)
  missingMiddle : ¬W.Inside 1 (1/2)
  missingOuter : ¬W.Inside 2 (1/2)
  cornerWalls : ∀ x y,C.Inside x y → x≤3 ∧ -1≤y
  corner : C.Inside 2 0
  missingCorner : ¬C.Inside 2 (1/2)
  apartKW : ∀ x y,¬(K.Inside x y ∧ W.Inside x y)
  apartKC : ∀ x y,¬(K.Inside x y ∧ C.Inside x y)
  apartWC : ∀ x y,¬(W.Inside x y ∧ C.Inside x y)

/-- The surviving bottom root, with the two midpoint conclusions stated
as their exact point/exclusion premises. -/
theorem bottom_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 0).Inside 1 1)
    (seedA : (owners p 0).Inside (91/50) 1)
    (seedS : (owners p 0).Inside (49/25) (19/25))
    (origin : (owners p 9).Inside 2 1)
    (middle : ¬(owners p 9).Inside 2 (3/2))
    (outer : (owners p 5).Inside 3 (3/2)) :
    Input ((owners p 0).translated 1 1) ((owners p 9).translated 1 1)
      ((owners p 2).translated 1 1) := by
  have k : (owners p 0).Inside 1 (457/500) := by
    have h := seed_inside p hf 0 (1,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have w : (owners p 9).Inside 2 (457/500) := by
    have h := seed_inside p hf 9 (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  refine ⟨owners_side p 0,owners_same_side p 0 9,owners_same_side p 0 2,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y own
    have wall := (owners_contained p 0 _ _ ((inside_translated_iff _ _ _ _ _).mp own)).2.2.1
    linarith only [wall]
  · norm_num only [inside_translated_iff]; exact k
  · norm_num only [inside_translated_iff]; exact seedA
  · norm_num only [inside_translated_iff]; exact seedS
  · norm_num only [inside_translated_iff]; exact missing
  · norm_num only [inside_translated_iff]; exact origin
  · norm_num only [inside_translated_iff]; exact w
  · norm_num only [inside_translated_iff]; exact bottom_advance p hf
  · norm_num only [inside_translated_iff]
    exact fun own => owners_apart p hf 9 5 (by decide +kernel) _ _ ⟨own,marker⟩
  · norm_num only [inside_translated_iff]; exact middle
  · norm_num only [inside_translated_iff]
    exact fun own => owners_apart p hf 9 5 (by decide +kernel) _ _ ⟨own,outer⟩
  · intro x y own
    have wall := owners_contained p 2 _ _ ((inside_translated_iff _ _ _ _ _).mp own)
    constructor <;> linarith only [wall.2.1,wall.2.2.1]
  · norm_num only [inside_translated_iff]; exact corner
  · norm_num only [inside_translated_iff]
    exact fun own => owners_apart p hf 2 5 (by decide +kernel) _ _ ⟨own,outer⟩
  · intro x y both
    exact owners_apart p hf 0 9 (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact owners_apart p hf 0 2 (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact owners_apart p hf 9 2 (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩

/-- The opposite missing-corner root, under (x,y)↦(y-1,x-1), before
the local three-square contradiction is applied. -/
theorem left_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (missing : ¬(owners p 1).Inside 1 1)
    (seedA : (owners p 1).Inside 1 (91/50))
    (seedS : (owners p 1).Inside (19/25) (49/25)) :
    Input ((pullSwap (owners p 1)).translated 1 1)
      ((pullSwap (owners p 8)).translated 1 1)
      ((pullSwap (owners p 4)).translated 1 1) := by
  have f3 := (f4_top p hf f4).1
  have g7 := f4_northeast_g7 p hf f4
  have origin := left_origin_of_top_g7 p hf f3 g7
  have middle := merged_horizontal_point p hf
  have topAnchor : (owners p 11).Inside (8/5) 3 := by
    have h := auxiliary_inside p 11 3 (by decide +kernel) f3
    simpa [auxPoints,fPoints,gPoints] using h
  have top := CommonCases.OriginalOwners.horizontal_segment (owners p 11)
    (36/25) (8/5) 3 (3/2) (top_left_advance p hf f3 g7) topAnchor
    (by norm_num) (by norm_num) (by norm_num)
  have k : (owners p 1).Inside (457/500) 1 := by
    have h := seed_inside p hf 1 (457/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have w : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have marker : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 4).Inside 1 3 := by
    have h := seed_inside p hf 4 (1,3) (by decide +kernel)
    norm_num at h
    exact h
  refine ⟨owners_side p 1,owners_same_side p 1 8,owners_same_side p 1 4,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y own
    have original : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := (owners_contained p 1 _ _ original).1
    linarith only [wall]
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact k
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact seedA
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact seedS
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact missing
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact origin
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact w
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact left_advance p hf
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨own,marker⟩
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨own,middle⟩
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => owners_apart p hf 8 11 (by decide +kernel) _ _ ⟨own,top⟩
  · intro x y own
    have original : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := owners_contained p 4 _ _ original
    constructor <;> linarith only [wall.2.2.2,wall.1]
  · norm_num only [inside_translated_iff,inside_pullSwap]; exact corner
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => owners_apart p hf 4 11 (by decide +kernel) _ _ ⟨own,top⟩
  · intro x y both
    have first : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 8).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact owners_apart p hf 1 8 (by decide +kernel) _ _ ⟨first,last⟩
  · intro x y both
    have first : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact owners_apart p hf 1 4 (by decide +kernel) _ _ ⟨first,last⟩
  · intro x y both
    have first : (owners p 8).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact owners_apart p hf 8 4 (by decide +kernel) _ _ ⟨first,last⟩

end
#print axioms bottom_input
#print axioms left_input
end N12Compact.Completion.OtherCases.C983.C974LocalData
