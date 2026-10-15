import Compact.Completion.FiniteCases.C972MissingCorner
import Compact.Geometry.FourSquareHighRight
import Compact.Completion.CommonCases.NorthwestSharpPoint

/-! Additional actual-owner reductions above C972's compulsory entrance.
The existing whole-angle four-square theorem excludes the NE inward pair;
an omitted F5 produces the corresponding real outer halfpoint. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot FourSquareAnchors
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

theorem northeast_not_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬((owners p 7).Inside 2 (113/50) ∧ (owners p 7).Inside (113/50) 2) := by
  rintro ⟨f5,g6⟩
  have h := fixed p hf
  have cornerMarker : (owners p 4).Inside 1 (1543/500) := by
    convert seed p hf 4 (1,1543/500) (by decide +kernel) using 1 <;> norm_num
  have data : FourSquareHighRight.Premises (owners p 7) (owners p 8)
      (owners p 9) (owners p 11) := {
    one_lt := side p 8
    side_cap := by
      change (p.square (ownerIndex p (masks 8))).side≤1001/1000
      rw [p.congruent]
      exact p.side_le
    sameA := same p 7 8
    sameL := same p 8 9
    sameR := same p 8 11
    boxB := box p 8
    boxL := box p 9
    boxR := box p 11
    aP := close f5
    aQ := close g6
    aT := close h.northeastMarker
    aF := foreign p hf 7 5 (by decide) _ _ h.southwestMarker
    aG := foreign p hf 7 6 (by decide) _ _ h.southeastMarker
    bBottom := close h.northwestMarker
    bTop := close (northwest_pair p hf).1
    bTopRight := close (northwest_pair p hf).2
    bMissingLeft := foreign p hf 8 4 (by decide) _ _ cornerMarker
    bMissingRight := missing_top p hf 8
    lLeft := close h.leftMarker
    lTop := close h.leftG1
    lMissingLow := foreign p hf 9 1 (by decide) _ _ h.singleton1Seed
    lMissingRight := foreign p hf 9 5 (by decide) _ _ h.southwestMarker
    rTop := close h.rightG9
    ab := apart p hf 7 8 (by decide)
    ar := apart p hf 7 11 (by decide)
    bl := apart p hf 8 9 (by decide)
    br := apart p hf 8 11 (by decide) }
  exact FourSquareHighRight.impossible _ _ _ _ data
    (right_bar p hf (5/2) (by norm_num) (by norm_num))

theorem northeast_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 7).Inside 2 (113/50)) : (owners p 7).Inside (5/2) 3 := by
  have h := fixed p hf
  have point := OrdinaryMarkerHalfpoint.point_original (pullSwap (pullX (owners p 7)))
    (43/500) (side p 7) (by norm_num) (by norm_num)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northeastMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact northeast_g7 p hf)
    (by norm_num [inside_pullSwap,inside_pullX]; exact northeast_f7 p hf)
    (by norm_num [inside_pullSwap,inside_pullX]; exact missing)
    (by norm_num [inside_pullSwap,inside_pullX]; exact missing_top p hf 7)
    (by norm_num [inside_pullSwap,inside_pullX]
        exact foreign p hf 7 3 (by decide) _ _ h.northeastCorner)
    (by norm_num [inside_pullSwap,inside_pullX]
        exact foreign p hf 7 11 (by decide) _ _ h.rightF9)
  norm_num [inside_pullSwap,inside_pullX] at point
  exact point

theorem right_origin_of_northeast_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (half : (owners p 7).Inside (5/2) 3) :
    (owners p 11).Inside 3 2 := by
  let B := pullSwap (pullY (pullX (owners p 11)))
  let K := pullSwap (pullY (pullX (owners p 3)))
  have boxB := container_pullSwap _ (container_pullY _ (container_pullX _ (box p 11)))
  have boxK := container_pullSwap _ (container_pullY _ (container_pullX _ (box p 3)))
  have cornerMarker : (owners p 3).Inside (1543/500) 3 := by
    convert seed p hf 3 (1543/500,3) (by decide +kernel) using 1 <;> norm_num
  have point := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 11) (same p 11 3)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]
        exact (fixed p hf).rightMarker)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]
        exact (fixed p hf).rightG9)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]
        exact (fixed p hf).northeastCorner)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]
        exact foreign p hf 3 7 (by decide) _ _ half)
    (by
      intro x y both
      have first : (owners p 3).Inside (4-y) (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY,inside_pullX] using both.1
      have last : (owners p 11).Inside (4-y) (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY,inside_pullX] using both.2
      exact apart p hf 3 11 (by decide) _ _ ⟨first,last⟩)
  dsimp only [B] at point
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at point
  exact point

theorem northwest_forward_right_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (forward : (owners p 8).Inside 2 (113/50)) :
    (owners p 11).Inside 3 2 :=
  right_origin_of_northeast_halfpoint p hf
    (northeast_halfpoint p hf (foreign p hf 7 8 (by decide) _ _ forward))

/-- In the complementary branch, the top origin belongs to the actual NE
central square. Its exclusion from NW, and the actual left bar, give the
sharp NW point; no boundary-square ownership is assigned to (2,3). -/
theorem northwest_missing_sharp (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 8).Inside 2 (113/50)) :
    (owners p 8).Inside (13/6) (721/300) := by
  have origin := (remaining_alternative p hf).resolve_left missing
  have h := fixed p hf
  exact CommonCases.NorthwestSharpPoint.point_original _ (side p 8) h.northwestMarker
    (northwest_pair p hf).1 (northwest_pair p hf).2 missing
    (foreign p hf 8 7 (by decide) _ _ origin)
    (foreign p hf 8 4 (by decide) _ _ h.northwestCorner) (missing_top p hf 8)
    (fun y low high => foreign p hf 8 9 (by decide) _ _ (left_bar p hf y low high))

/-- The sharp point is in the strict triangle with vertices F5, (2,3),
and the NE marker: their barycentric weights are 603, 211, 740 over 1554.
Thus the optional NE F5 is excluded by the same actual NW square. -/
theorem northeast_missing_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owners p 7).Inside 2 (113/50) := by
  intro f5
  have missing := foreign p hf 8 7 (by decide) _ _ f5
  have origin := (remaining_alternative p hf).resolve_left missing
  have marker := (fixed p hf).northeastMarker
  have sharp := northwest_missing_sharp p hf missing
  have own : (owners p 7).Inside (13/6) (721/300) := by
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [f5.1,origin.1,marker.1]
    · linarith only [f5.2.1,origin.2.1,marker.2.1]
    · linarith only [f5.2.2.1,origin.2.2.1,marker.2.2.1]
    · linarith only [f5.2.2.2,origin.2.2.2,marker.2.2.2]
  exact apart p hf 7 8 (by decide) _ _ ⟨own,sharp⟩

theorem northeast_outer_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside (5/2) 3 :=
  northeast_halfpoint p hf (northeast_missing_f5 p hf)

theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside 3 2 :=
  right_origin_of_northeast_halfpoint p hf (northeast_outer_halfpoint p hf)

end
#print axioms northeast_not_inward
#print axioms northwest_missing_sharp
#print axioms northeast_missing_f5
#print axioms right_origin
end N12Compact.FiniteCases.C972
