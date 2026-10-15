import Compact.Completion.OtherCases.C983.C974LocalEnding
import Compact.Completion.OtherCases.C1089.WallOrigins
import Compact.Completion.CommonCases.OriginalOwners

/-! C1089-LAST-SECTOR-POINTS section 2: the actual singleton owns (1,1).
The completed local contradiction is C974-THREE-SQUARE-ENDING Theorem 1,
applied to the translated actual owners Q0, Q9, Q1. Its foreign midpoint
is obtained inside Q10, not by joining points in two different squares.

The two stronger Q0 seeds remain literal premises. Their historical
missing-corner producer imports the unavailable SingletonMissingTriangles
and MissingCornerCubic sources; neither is imported here. The ordinary
horizontal seeds (1.12,1),(1.74,1),(1.87,.76) are not substituted for
the stronger (1.82,1),(1.96,.76). This source has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.SingletonCorner
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- The local corner conclusion from the two exact stronger singleton
seeds and the retained point table. No singleton corner or bottom origin
is an input. The right-wall midpoint has its genuine separate owner. -/
theorem corner_of_seeds (q : Fin 12 → OpenSquare)
    (side : ∀ i,1<(q i).side) (same : ∀ i j,(q i).side=(q j).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (singletonMarker : (q 0).Inside 1 (457/500))
    (strongNear : (q 0).Inside (91/50) 1)
    (strongOffRow : (q 0).Inside (49/25) (19/25))
    (cornerMarker : (q 1).Inside 3 (457/500))
    (cornerPoint : (q 1).Inside 3 1)
    (southeastMarker : (q 5).Inside (47/20) (33/20))
    (southeastSouth : (q 5).Inside 2 (3/2))
    (northeastNear : (q 6).Inside 3 (113/50))
    (bottomMarker : (q 9).Inside 2 (457/500))
    (bottomInner : (q 9).Inside (12/5) 1)
    (bottomFar : (q 9).Inside (14/5) 1)
    (rightMarker : (q 10).Inside (1543/500) 2)
    (rightFar : (q 10).Inside 3 (8/5)) : (q 0).Inside 1 1 := by
  have rightLow := WallOrigins.right_low q (side 10) (contained 10) apart
    rightMarker rightFar northeastNear southeastMarker
  have rightMiddle : (q 10).Inside 3 (3/2) := by
    convert inside_segment (q 10) 3 (36/25) 3 (8/5) (3/8)
      rightLow rightFar (by norm_num) (by norm_num) using 1 <;> norm_num
  have origin := WallOrigins.bottom_origin q (side 9) (same 9 1) contained apart
    bottomMarker bottomInner cornerMarker cornerPoint rightLow rightFar
  by_contra missing
  let K := (q 0).translated 1 1
  let W := (q 9).translated 1 1
  let C := (q 1).translated 1 1
  have input : C983.C974LocalData.Input K W C := {
    sideLarge := side 0
    sameKW := same 0 9
    sameKC := same 0 1
    lowerWall := by
      intro x y own
      have actual := (inside_translated_iff (q 0) 1 1 x y).mp own
      have wall := (contained 0 _ _ actual).2.2.1
      linarith only [wall]
    markerK := by dsimp only [K]; norm_num only [inside_translated_iff]; exact singletonMarker
    pointK := by dsimp only [K]; norm_num only [inside_translated_iff]; exact strongNear
    seedK := by dsimp only [K]; norm_num only [inside_translated_iff]; exact strongOffRow
    missingK := by dsimp only [K]; norm_num only [inside_translated_iff]; exact missing
    originW := by dsimp only [W]; norm_num only [inside_translated_iff]; exact origin
    markerW := by dsimp only [W]; norm_num only [inside_translated_iff]; exact bottomMarker
    farW := by dsimp only [W]; norm_num only [inside_translated_iff]; exact bottomFar
    missingMarker := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact fun own => apart 9 5 (by decide) _ _ ⟨own,southeastMarker⟩
    missingMiddle := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact fun own => apart 9 5 (by decide) _ _ ⟨own,southeastSouth⟩
    missingOuter := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact fun own => apart 9 10 (by decide) _ _ ⟨own,rightMiddle⟩
    cornerWalls := by
      intro x y own
      have actual := (inside_translated_iff (q 1) 1 1 x y).mp own
      have wall := contained 1 _ _ actual
      exact ⟨by linarith only [wall.2.1],by linarith only [wall.2.2.1]⟩
    corner := by dsimp only [C]; norm_num only [inside_translated_iff]; exact cornerPoint
    missingCorner := by
      dsimp only [C]
      norm_num only [inside_translated_iff]
      exact fun own => apart 1 10 (by decide) _ _ ⟨own,rightMiddle⟩
    apartKW := by
      intro x y both
      exact apart 0 9 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩
    apartKC := by
      intro x y both
      exact apart 0 1 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩
    apartWC := by
      intro x y both
      exact apart 9 1 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩ }
  exact C983.C974LocalEnding.impossible K W C input

def family : Finset Nat := {1,12,48,192,256,512,1024,2048,4096,8192,16384,32768}

def masks : Fin 12 → Nat := ![1,12,48,192,256,512,1024,2048,4096,8192,16384,32768]

def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  CommonCases.OriginalOwners.owner p (masks i)

private theorem mask_member (i : Fin 12) : masks i∈family := by
  have checked : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact checked i

private theorem masks_injective : Function.Injective masks := by decide +kernel

/-- Original-marker absence is retained independently of the missing
corner contradiction. Gaining (1,1) does not acquire the absent marker. -/
theorem absent_marker (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∀ i,¬(owners p i).Inside (457/500) 1 := by
  intro i
  have checked : ∀ j : Fin 12,(1 : Marker)∉maskSupport (masks j) := by decide +kernel
  have absent := CommonCases.OriginalOwners.missing_marker family p hf (masks i)
    (mask_member i) 1 (checked i)
  simpa [owners,marker] using absent

/-- The original C1089 owners, rather than an abstract pose, supply the
three-square contradiction. Stronger singleton seeds and the remaining
post-reduction points are literal premises until their entrance is joined. -/
theorem original_corner_of_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (strongNear : (owners p 0).Inside (91/50) 1)
    (strongOffRow : (owners p 0).Inside (49/25) (19/25))
    (southeastSouth : (owners p 5).Inside 2 (3/2))
    (northeastNear : (owners p 6).Inside 3 (113/50))
    (bottomInner : (owners p 9).Inside (12/5) 1)
    (bottomFar : (owners p 9).Inside (14/5) 1)
    (rightFar : (owners p 10).Inside 3 (8/5)) :
    (owners p 0).Inside 1 1 ∧ ∀ i,¬(owners p i).Inside (457/500) 1 := by
  have seed (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
      (owners p i).Inside P.1 P.2 :=
    CommonCases.OriginalOwners.seed family p hf (masks i) (mask_member i) P checked
  have singletonMarker : (owners p 0).Inside 1 (457/500) := by
    have h := seed 0 (1,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 1).Inside 3 (457/500) := by
    have h := seed 1 (3,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 1).Inside 3 1 := by
    have h := seed 1 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have southeastMarker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have bottomMarker : (owners p 9).Inside 2 (457/500) := by
    have h := seed 9 (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have rightMarker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have side (i : Fin 12) : 1<(owners p i).side :=
    CommonCases.OriginalOwners.side p (masks i)
  have same (i j : Fin 12) : (owners p i).side=(owners p j).side := by
    change (p.square (ownerIndex p (masks i))).side=(p.square (ownerIndex p (masks j))).side
    exact (p.congruent _).trans (p.congruent _).symm
  have contained (i : Fin 12) : InsideContainer (owners p i) :=
    CommonCases.OriginalOwners.box p (masks i)
  have apart (i j : Fin 12) (different : i≠j) :
      ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
    CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
      (mask_member i) (mask_member j) (fun equal => different (masks_injective equal))
  exact ⟨corner_of_seeds (owners p) side same contained apart singletonMarker strongNear
    strongOffRow cornerMarker cornerPoint southeastMarker southeastSouth northeastNear
    bottomMarker bottomInner bottomFar rightMarker rightFar,absent_marker p hf⟩

/-- This is the precise remaining seed-production interface: only under
the missing-corner assumption must the two stronger points be supplied.
The conclusion itself is derived, and original marker absence is preserved. -/
theorem original_corner_of_missing_seed_producer (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (strongSeeds : ¬(owners p 0).Inside 1 1 →
      (owners p 0).Inside (91/50) 1 ∧ (owners p 0).Inside (49/25) (19/25))
    (southeastSouth : (owners p 5).Inside 2 (3/2))
    (northeastNear : (owners p 6).Inside 3 (113/50))
    (bottomInner : (owners p 9).Inside (12/5) 1)
    (bottomFar : (owners p 9).Inside (14/5) 1)
    (rightFar : (owners p 10).Inside 3 (8/5)) :
    (owners p 0).Inside 1 1 ∧ ∀ i,¬(owners p i).Inside (457/500) 1 := by
  refine ⟨?_,absent_marker p hf⟩
  by_contra missing
  obtain ⟨near,offRow⟩ := strongSeeds missing
  exact missing (original_corner_of_seeds p hf near offRow southeastSouth northeastNear
    bottomInner bottomFar rightFar).1

end
#print axioms corner_of_seeds
#print axioms absent_marker
#print axioms original_corner_of_seeds
#print axioms original_corner_of_missing_seed_producer
end N12Compact.Completion.OtherCases.C1089.SingletonCorner
