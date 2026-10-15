import Compact.Completion.C1092.MMMP.PointCore
import Compact.Completion.C1092.MMMMEnding
import Compact.Geometry.WallUpperMissingReach

/-! The original MMMP bottom ordinary pair. A contrary F2 supplies the
actual owners for the complete rotated three-square ending. The final F6
deduction uses the genuine single cover and the six-point theorem, so the
original three-point auxiliary budget is retained. -/
namespace N12Compact.C1092MMMPBottomPair
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092AuxiliaryCover
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
open N12Compact.Completion.OtherCases.WallProfile
set_option Elab.async false

private theorem southwest_pair_of_bottom_left (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (left : (owners p 9).Inside (8/5) 1) :
    (owners p 4).Inside 1 (87/50) ∧ (owners p 4).Inside 1 (8/5) := by
  have lower : (owners p 9).Inside (87/50) 1 := by
    have h := inside_segment (owners p 9) (8/5) 1 (113/50) 1 (7/33)
      left (wall_auxiliaries p hb).2.1 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have inward := northwest_pair p hf hb
  have g : (owners p 4).Inside 1 (8/5) := by
    rcases southwest_g_cover p hf with h|h|h
    · exact h
    · exact False.elim (owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,lower⟩)
    · exact False.elim (owners_disjoint p hf 4 7 (by decide) _ _ ⟨h,inward.2⟩)
  have cover : (owners p 4).Inside 1 (87/50) ∨
      (owners p 4).Inside (8/5) 1 ∨ (owners p 4).Inside 2 (87/50) := by
    have h := central_cover_transported ⟨true,false,false⟩ p hf
    norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
    tauto
  have f : (owners p 4).Inside 1 (87/50) := by
    by_contra absent
    rcases cover with h|h|h
    · exact absent h
    · exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,left⟩
    · apply C1092MixedSpan.impossible (pullX (owners p 4)) (side_gt p 4)
      · norm_num [inside_pullX]; exact h
      · norm_num [inside_pullX]; exact g
      · norm_num [inside_pullX]
        exact fun own => owners_disjoint p hf 4 7 (by decide) _ _ ⟨own,inward.2⟩
      · norm_num [inside_pullX]; exact absent
      · norm_num [inside_pullX]
        exact fun own => owners_disjoint p hf 4 9 (by decide) _ _ ⟨own,lower⟩
      · norm_num [inside_pullX]
        exact fun own => owners_disjoint p hf 4 9 (by decide) _ _ ⟨own,left⟩
  exact ⟨f,g⟩

private theorem top_origin_of_bottom_left (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (left : (owners p 9).Inside (8/5) 1) : (owners p 11).Inside 2 3 := by
  have sw := southwest_pair_of_bottom_left p hf hb left
  have nw := northwest_pair p hf hb
  have upper : (owners p 8).Inside 1 (12/5) := by
    rcases left_g_cover p hf with h|h|h
    · exact False.elim (owners_disjoint p hf 8 4 (by decide) _ _ ⟨h,sw.2⟩)
    · exact h
    · exact False.elim (owners_disjoint p hf 8 7 (by decide) _ _ ⟨h,nw.2⟩)
  have wallMark : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have nwMark : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have far := WallUpperMissingReach.point (owners p 8) (side_gt p 8) (p.contained _)
    wallMark upper
    (fun own => owners_disjoint p hf 8 4 (by decide) _ _ ⟨own,sw.1⟩)
    (fun own => owners_disjoint p hf 8 7 (by decide) _ _ ⟨own,nwMark⟩)
  have half : (owners p 8).Inside 1 (5/2) := by
    have h := inside_segment (owners p 8) 1 (12/5) 1 (64/25) (5/8)
      upper far (by norm_num) (by norm_num)
    norm_num at h
    exact h
  let B := pullY (owners p 11)
  let K := pullY (owners p 3)
  have boxB : InsideContainer B := container_transform ⟨false,false,true⟩ _ (p.contained _)
  have boxK : InsideContainer K := container_transform ⟨false,false,true⟩ _ (p.contained _)
  have markB : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have markK : (owners p 3).Inside 1 (1543/500) := by
    simpa [marker] using marker_point p hf 3 6 (by decide +kernel)
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  have answer := boundary_origin B K (457/500) (8/5) (side_gt p 11) (side_same p 11 3)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [B,inside_pullY]; exact markB)
    (by norm_num [B,inside_pullY]; exact (top_pair p hf hb).1)
    (by norm_num [K,inside_pullY]; exact markK)
    (by norm_num [K,inside_pullY]; exact corner)
    (by
      norm_num [K,inside_pullY]
      exact fun own => owners_disjoint p hf 3 8 (by decide) _ _ ⟨own,half⟩)
    (by
      intro x y own
      exact owners_disjoint p hf 3 11 (by decide) _ _
        ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [B,inside_pullY] at answer
  exact answer

private noncomputable def quarter (q : OpenSquare) : OpenSquare :=
  (pullSwap (pullX q)).translated 2 2

private theorem inside_quarter (q : OpenSquare) (x y : ℝ) :
    (quarter q).Inside x y ↔ q.Inside (2-y) (2+x) := by
  simp only [quarter,inside_translated_iff,inside_pullSwap,inside_pullX]
  rw [show 4-(2+y)=2-y by ring]

theorem missing_left (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : ¬(owners p 9).Inside (8/5) 1 := by
  intro left
  have sw := southwest_pair_of_bottom_left p hf hb left
  have top := top_origin_of_bottom_left p hf hb left
  have ne := northeast_pair p hf hb
  have markN : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markE : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markW : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have cornerE : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have cornerW : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  have rightTip : (owners p 10).Inside 3 (239/100) := by
    have h := local_wall_segment p mmmp hb 2 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have bottomTip : (owners p 9).Inside (161/100) 1 := by
    have h := inside_segment (owners p 9) (8/5) 1 (113/50) 1 (1/66)
      left (wall_auxiliaries p hb).2.1 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have northTip : (owners p 7).Inside 2 (239/100) := by
    have h := inside_segment (owners p 7) 2 2 2 (5/2) (39/50)
      (northwest_center p hf hb) (northwest_north p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have leftTip : (owners p 7).Inside (161/100) 2 := by
    have h := inside_segment (owners p 7) (3/2) 2 2 2 (11/50)
      (northwest_left p hf hb) (northwest_center p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  apply C1092MMMMEnding.impossible (quarter (owners p 7)) (quarter (owners p 6))
    (quarter (owners p 4))
  refine {
    side := side_gt p 7
    sameE := side_same p 7 6
    sameW := side_same p 7 4
    origin := ?_
    halfX := ?_
    halfY := ?_
    markerN := ?_
    markerE := ?_
    ordinaryE1 := ?_
    ordinaryE2 := ?_
    markerW := ?_
    ordinaryW1 := ?_
    ordinaryW2 := ?_
    eLeftBottom := ?_
    eLeftTop := ?_
    eRightBottom := ?_
    eRightTop := ?_
    wLeftBottom := ?_
    wLeftTop := ?_
    wRightBottom := ?_
    wRightTop := ?_
    apartE := ?_
    apartW := ?_ }
  · norm_num [inside_quarter]; exact northwest_center p hf hb
  · norm_num [inside_quarter]; exact northwest_north p hf hb
  · norm_num [inside_quarter]; exact northwest_left p hf hb
  · norm_num [inside_quarter]; exact markN
  · norm_num [inside_quarter]; exact markE
  · norm_num [inside_quarter]; exact ne.2
  · norm_num [inside_quarter]; exact ne.1
  · norm_num [inside_quarter]; exact markW
  · norm_num [inside_quarter]; exact sw.1
  · norm_num [inside_quarter]; exact sw.2
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 6 2 (by decide) _ _ ⟨own,cornerE⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 6 11 (by decide) _ _ ⟨own,top⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 6 10 (by decide) _ _ ⟨own,rightTip⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 6 7 (by decide) _ _ ⟨own,northTip⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 4 0 (by decide) _ _ ⟨own,cornerW⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 4 8 (by decide) _ _ ⟨own,left_origin p hf hb⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 4 9 (by decide) _ _ ⟨own,bottomTip⟩
  · norm_num [inside_quarter]
    exact fun own => owners_disjoint p hf 4 7 (by decide) _ _ ⟨own,leftTip⟩
  · intro x y own
    exact owners_disjoint p hf 7 6 (by decide) _ _
      ⟨(inside_quarter _ _ _).mp own.1,(inside_quarter _ _ _).mp own.2⟩
  · intro x y own
    exact owners_disjoint p hf 7 4 (by decide) _ _
      ⟨(inside_quarter _ _ _).mp own.1,(inside_quarter _ _ _).mp own.2⟩

theorem pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) :
    (owners p 9).Inside (12/5) 1 ∧ (owners p 9).Inside (113/50) 1 := by
  have bottom := (wall_auxiliaries p hb).2.1
  have omitted := missing_left p hf hb
  have markB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have markE : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have forward : (owners p 9).Inside (12/5) 1 := by
    have h := wall_cover_transported ⟨true,false,false⟩ p hf
    norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
    rcases h with h|h|h
    · exact False.elim (omitted h)
    · exact h
    · have six := side_six_point (pullSwap (pullX (owners p 9))) (side_gt p 9)
        (by norm_num [inside_pullSwap,inside_pullX]; exact markB)
        (by norm_num [inside_pullSwap,inside_pullX]; exact bottom)
        (by norm_num [inside_pullSwap,inside_pullX]; exact h)
      norm_num [inside_pullSwap,inside_pullX] at six
      rcases six with high|low|foreign
      · exact high
      · exact False.elim (omitted low)
      · exact False.elim (owners_disjoint p hf 9 5 (by decide) _ _ ⟨foreign,markE⟩)
  exact ⟨forward,bottom⟩

#print axioms missing_left
#print axioms pair
end N12Compact.C1092MMMPBottomPair
