import Compact.Completion.FiniteCases.C972CentralSelection
import Compact.Completion.CommonCases.C974976Origins
import Compact.Completion.CommonCases.SingletonMissing
import Compact.Completion.OtherCases.C983.C974LocalEnding
import Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint.Main
import Compact.Completion.C981.WallAdvance

/-! C972's two genuine missing-corner roots. The left root is excluded
when NW omits F5. The bottom root is excluded when NE omits (2,3).
These are conditional branch exclusions, not an exclusion of C972.
There is no top-wall owner: the top marker is used only as an omission. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

private theorem cap (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side≤1001/1000 := by
  change (p.square (ownerIndex p (masks i))).side≤1001/1000
  rw [p.congruent]
  exact p.side_le

private theorem markers (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) : ExactMarkers (owners p i) (maskSupport (masks i)) := by
  have code := CommonCases.OriginalOwners.code family p hf (masks i) (member i)
  simpa only [code, owners, CommonCases.OriginalOwners.owner] using
    coded_exact p (ownerIndex p (masks i))

theorem missing_zero_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 0).Inside 1 1) :
    (owners p 0).Inside (91/50) 1 ∧ (owners p 0).Inside (49/25) (19/25) := by
  apply CommonCases.SingletonMissing.zero_missing_points _ (side p 0) (cap p 0) (box p 0) _ missing
  convert markers p hf 0 using 1
  decide +kernel

theorem missing_one_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 1).Inside 1 1) :
    (owners p 1).Inside 1 (91/50) ∧ (owners p 1).Inside (19/25) (49/25) := by
  apply CommonCases.SingletonMissing.one_missing_points _ (side p 1) (cap p 1) (box p 1) _ missing
  convert markers p hf 1 using 1
  decide +kernel

theorem left_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside 1 (14/5) := by
  have h := fixed p hf
  exact C981CompletionWallAdvance.point _ (side p 9) (box p 9) h.leftMarker h.leftG1
    (foreign p hf 9 1 (by decide) _ _ (singleton_vertical p hf _ (by norm_num) le_rfl))
    (foreign p hf 9 1 (by decide) _ _ h.singleton1Seed)
    (foreign p hf 9 8 (by decide) _ _ h.northwestMarker)

theorem left_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 113/50≤y) (high : y≤14/5) : (owners p 9).Inside 1 y :=
  CommonCases.OriginalOwners.vertical_segment _ 1 (113/50) (14/5) y
    (fixed p hf).leftF1 (left_reach p hf) (by norm_num) low high

theorem northwest_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 8).Inside 2 (113/50)) : (owners p 8).Inside (3/2) 3 := by
  have h := fixed p hf
  have pair := northwest_pair p hf
  have point := OrdinaryMarkerHalfpoint.point_original (pullSwap (owners p 8)) (43/500)
    (side p 8) (by norm_num) (by norm_num)
    (by simpa only [inside_pullSwap] using h.northwestMarker)
    (by simpa only [inside_pullSwap] using pair.2)
    (by simpa only [inside_pullSwap] using pair.1)
    (by simpa only [inside_pullSwap] using missing)
    (by norm_num [inside_pullSwap]; exact missing_top p hf 8)
    (by simpa only [inside_pullSwap] using foreign p hf 8 4 (by decide) _ _ h.northwestCorner)
    (by simpa only [inside_pullSwap] using foreign p hf 8 9 (by decide) _ _ h.leftF1)
  simpa only [inside_pullSwap] using point

theorem left_origin_of_northwest_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (half : (owners p 8).Inside (3/2) 3) :
    (owners p 9).Inside 1 2 := by
  let B := pullSwap (pullY (owners p 9))
  let K := pullSwap (pullY (owners p 4))
  have boxB := container_pullSwap _ (container_pullY _ (box p 9))
  have boxK := container_pullSwap _ (container_pullY _ (box p 4))
  have cornerMarker : (owners p 4).Inside (457/500) 3 := by
    convert seed p hf 4 (457/500,3) (by decide +kernel) using 1 <;> norm_num
  have point := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 9) (same p 9 4)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).leftMarker)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).leftG1)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).northwestCorner)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]
        exact foreign p hf 4 8 (by decide) _ _ half)
    (by
      intro x y both
      have first : (owners p 4).Inside y (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY] using both.1
      have last : (owners p 9).Inside y (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY] using both.2
      exact apart p hf 4 9 (by decide) _ _ ⟨first,last⟩)
  dsimp only [B] at point
  norm_num [inside_pullSwap,inside_pullY] at point
  exact point

theorem left_missing_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 1).Inside 1 1) (half : (owners p 8).Inside (3/2) 3) : False := by
  have h := fixed p hf
  have seeds := missing_one_points p hf missing
  have marker : (owners p 1).Inside (457/500) 1 := by
    convert seed p hf 1 (457/500,1) (by decide +kernel) using 1 <;> norm_num
  have data : C983.C974LocalData.Input ((pullSwap (owners p 1)).translated 1 1)
      ((pullSwap (owners p 9)).translated 1 1) ((pullSwap (owners p 4)).translated 1 1) := by
    refine {
      sideLarge := side p 1
      sameKW := same p 1 9
      sameKC := same p 1 4
      lowerWall := ?_, markerK := ?_, pointK := ?_, seedK := ?_, missingK := ?_
      originW := ?_, markerW := ?_, farW := ?_, missingMarker := ?_
      missingMiddle := ?_, missingOuter := ?_, cornerWalls := ?_, corner := ?_
      missingCorner := ?_, apartKW := ?_, apartKC := ?_, apartWC := ?_ }
    · intro x y own
      have original : (owners p 1).Inside (1+y) (1+x) := by
        simpa only [inside_translated_iff,inside_pullSwap] using own
      have wall := (box p 1 _ _ original).1
      linarith only [wall]
    · norm_num [inside_translated_iff,inside_pullSwap]; exact marker
    · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.1
    · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.2
    · norm_num [inside_translated_iff,inside_pullSwap]; exact missing
    · norm_num [inside_translated_iff,inside_pullSwap]
      exact left_origin_of_northwest_halfpoint p hf half
    · norm_num [inside_translated_iff,inside_pullSwap]; exact h.leftMarker
    · norm_num [inside_translated_iff,inside_pullSwap]; exact left_reach p hf
    · norm_num [inside_translated_iff,inside_pullSwap]
      exact foreign p hf 9 8 (by decide) _ _ h.northwestMarker
    · norm_num [inside_translated_iff,inside_pullSwap]
      exact foreign p hf 9 5 (by decide) _ _ (southwest_west p hf)
    · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 9 8 (by decide) _ _ half
    · intro x y own
      have original : (owners p 4).Inside (1+y) (1+x) := by
        simpa only [inside_translated_iff,inside_pullSwap] using own
      have wall := box p 4 _ _ original
      constructor <;> linarith only [wall.2.2.2,wall.1]
    · norm_num [inside_translated_iff,inside_pullSwap]; exact h.northwestCorner
    · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 4 8 (by decide) _ _ half
    · intro x y both
      exact apart p hf 1 9 (by decide) (1+y) (1+x)
        ⟨by simpa only [inside_translated_iff,inside_pullSwap] using both.1,
          by simpa only [inside_translated_iff,inside_pullSwap] using both.2⟩
    · intro x y both
      exact apart p hf 1 4 (by decide) (1+y) (1+x)
        ⟨by simpa only [inside_translated_iff,inside_pullSwap] using both.1,
          by simpa only [inside_translated_iff,inside_pullSwap] using both.2⟩
    · intro x y both
      exact apart p hf 9 4 (by decide) (1+y) (1+x)
        ⟨by simpa only [inside_translated_iff,inside_pullSwap] using both.1,
          by simpa only [inside_translated_iff,inside_pullSwap] using both.2⟩
  exact C983.C974LocalEnding.impossible _ _ _ data

theorem zero_corner_of_southeast_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (half : (owners p 6).Inside 3 (3/2)) :
    (owners p 0).Inside 1 1 := by
  by_contra missing
  have h := fixed p hf
  have seeds := missing_zero_points p hf missing
  have marker : (owners p 0).Inside 1 (457/500) := by
    convert seed p hf 0 (1,457/500) (by decide +kernel) using 1 <;> norm_num
  have cornerMarker : (owners p 2).Inside 3 (457/500) := by
    convert seed p hf 2 (3,457/500) (by decide +kernel) using 1 <;> norm_num
  have origin := CommonCases.C974976Central.bottom_origin (owners p 10) (owners p 2) (owners p 6)
    (side p 10) (same p 10 2) (box p 10) (box p 2) h.bottomMarker h.bottomF6
    cornerMarker h.southeastCorner half (apart p hf 2 6 (by decide)) (apart p hf 2 10 (by decide))
  have data : C983.C974LocalData.Input ((owners p 0).translated 1 1)
      ((owners p 10).translated 1 1) ((owners p 2).translated 1 1) := by
    refine {
      sideLarge := side p 0, sameKW := same p 0 10, sameKC := same p 0 2
      lowerWall := ?_, markerK := ?_, pointK := ?_, seedK := ?_, missingK := ?_
      originW := ?_, markerW := ?_, farW := ?_, missingMarker := ?_
      missingMiddle := ?_, missingOuter := ?_, cornerWalls := ?_, corner := ?_
      missingCorner := ?_, apartKW := ?_, apartKC := ?_, apartWC := ?_ }
    · intro x y own
      have wall := (box p 0 _ _ ((inside_translated_iff _ _ _ _ _).mp own)).2.2.1
      linarith only [wall]
    · norm_num [inside_translated_iff]; exact marker
    · norm_num [inside_translated_iff]; exact seeds.1
    · norm_num [inside_translated_iff]; exact seeds.2
    · norm_num [inside_translated_iff]; exact missing
    · norm_num [inside_translated_iff]; exact origin
    · norm_num [inside_translated_iff]; exact h.bottomMarker
    · norm_num [inside_translated_iff]; exact (bottom_reach p hf).1
    · norm_num [inside_translated_iff]; exact foreign p hf 10 6 (by decide) _ _ h.southeastMarker
    · norm_num [inside_translated_iff]; exact foreign p hf 10 5 (by decide) _ _ (southwest_south p hf)
    · norm_num [inside_translated_iff]; exact foreign p hf 10 6 (by decide) _ _ half
    · intro x y own
      have wall := box p 2 _ _ ((inside_translated_iff _ _ _ _ _).mp own)
      constructor <;> linarith only [wall.2.1,wall.2.2.1]
    · norm_num [inside_translated_iff]; exact h.southeastCorner
    · norm_num [inside_translated_iff]; exact foreign p hf 2 6 (by decide) _ _ half
    · intro x y both
      exact apart p hf 0 10 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
    · intro x y both
      exact apart p hf 0 2 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
    · intro x y both
      exact apart p hf 10 2 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  exact C983.C974LocalEnding.impossible _ _ _ data

theorem one_corner_of_northwest_missing_f5 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 8).Inside 2 (113/50)) :
    (owners p 1).Inside 1 1 := by
  by_contra corner
  exact left_missing_impossible p hf corner (northwest_halfpoint p hf missing)

theorem southeast_halfpoint_of_northeast_missing_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 7).Inside 2 3) :
    (owners p 6).Inside 3 (3/2) := by
  have h : CommonCases.C974976Central.EndingInput (owners p 6) (owners p 7) := {
    toInput := selection_input p hf
    topOrigin := missing
    northeastCorner := foreign p hf 7 3 (by decide) _ _ (fixed p hf).northeastCorner
    rightBar := fun y low high => foreign p hf 7 11 (by decide) _ _ (right_bar p hf y low high) }
  exact CommonCases.C974976Central.southeast_lower _ _ h
    (CommonCases.C974976Central.southeast_g6 _ _ h)

/-- A true-owner surviving alternative. The disjunction is necessary,
not a declaration that either listed branch has already been excluded. -/
theorem remaining_alternative (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 2 (113/50) ∨ (owners p 7).Inside 2 3 := by
  by_cases first : (owners p 8).Inside 2 (113/50)
  · exact Or.inl first
  right
  by_contra last
  have one := one_corner_of_northwest_missing_f5 p hf first
  have zero := zero_corner_of_southeast_halfpoint p hf
    (southeast_halfpoint_of_northeast_missing_origin p hf last)
  exact apart p hf 0 1 (by decide) _ _ ⟨zero,one⟩

end
#print axioms remaining_alternative
end N12Compact.FiniteCases.C972
