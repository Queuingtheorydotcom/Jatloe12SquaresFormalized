import Compact.Completion.C1092.MMMP.CenterCorner
import Compact.Completion.C1092.MMMP.ActualProfile
import Compact.Completion.C1092.MMMP.LeftFar
import Compact.Completion.C981.TopReach

/-! Actual-owner reduction of the missing MMMP top origin to the strictly
negative canonical left-wall sign. The positive sign is excluded using
the genuine center cut; no additional face or owner premise is assumed.
The negative sign and the independent right near-point gap remain open. -/
namespace N12Compact.C1092MMMPTopOriginSign
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore C977CornerCubic
set_option Elab.async false

theorem corner_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (missing : ¬(owners p 11).Inside 2 3) : (owners p 3).Inside 1 (5/2) := by
  classical
  by_contra absent
  let B := pullY (owners p 11)
  let K := pullY (owners p 3)
  have boxB : InsideContainer B := container_pullY _ (p.contained _)
  have boxK : InsideContainer K := container_pullY _ (p.contained _)
  have markerB : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have markerK : (owners p 3).Inside 1 (1543/500) := by
    simpa [marker] using marker_point p hf 3 6 (by decide +kernel)
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  have h := Completion.OtherCases.WallProfile.boundary_origin B K (457/500) (8/5)
    (side_gt p 11) (side_same p 11 3)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [B,inside_pullY]; exact markerB)
    (by norm_num [B,inside_pullY]; exact (top_pair p hf hb).1)
    (by norm_num [K,inside_pullY]; exact markerK)
    (by norm_num [K,inside_pullY]; exact corner)
    (by norm_num [K,inside_pullY]; exact absent)
    (fun x y own => owners_disjoint p hf 3 11 (by decide) _ _
      ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [B,inside_pullY] at h
  exact missing h

theorem top_alternative (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (missing : ¬(owners p 11).Inside 2 3) : (owners p 11).Inside (6/5) 3 := by
  let T := (pullX (owners p 11)).translated 2 3
  have actual (x y : ℝ) : T.Inside x y ↔ (owners p 11).Inside (2-x) (3+y) := by
    simp only [T,inside_translated_iff,inside_pullX]
    rw [show 4-(2+x)=2-x by ring]
  have markerT : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have h := C981CompletionTopReach.origin_alternative T (side_gt p 11)
    (by
      intro x y own
      have box := p.contained _ _ _ ((actual _ _).mp own)
      linarith only [box.2.2.2])
    (by apply (actual _ _).mpr; norm_num; exact markerT)
    (by apply (actual _ _).mpr; norm_num; exact (top_pair p hf hb).1)
    (by intro own; have h := (actual _ _).mp own; norm_num at h; exact missing h)
  have h' := (actual _ _).mp h
  norm_num at h'
  exact h'

structure NegativeLeft (p : NormalizedPacking) (L : OpenSquare) : Prop where
  side : L.side=(owners p 8).side
  actual : ∀ x y, L.Inside x y ↔ (owners p 8).Inside (1+x) (2+y)
  normal : Normal L.c (-L.s)
  negative : L.s<0
  centerCut : 0≤centerY L
  centerLeft : centerX L<0
  upperV : L.loV+L.side≤L.c/2

theorem negative_left_of_missing_top (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (missing : ¬(owners p 11).Inside 2 3) : ∃ L : OpenSquare, NegativeLeft p L := by
  classical
  let W := (owners p 8).translated 1 2
  obtain ⟨L,lc,range,shape,center,inside⟩ := C1092MixedWideCrossing.centered_frame W
  have actual (x y : ℝ) : L.Inside x y ↔ (owners p 8).Inside (1+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have side : 1<L.side := by rw [shape]; exact side_gt p 8
  have cut : 0≤centerY L := by
    have original : 2≤centerY (owners p 8) := by
      simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 0).1
    have translated : centerY W=centerY (owners p 8)-2 := by
      dsimp [W,OpenSquare.translated,centerY]
      linear_combination -2*(owners p 8).unit_normal
    rw [center,translated]
    linarith only [original]
  have O : L.Inside 0 0 := by
    apply (actual _ _).mpr
    norm_num
    exact left_origin p hf hb
  have G : L.Inside 0 (2/5) := by
    apply (actual _ _).mpr
    norm_num
    exact C1092MMMPLeftFar.point p hf hb
  have T : L.Inside 0 (39/100) := by
    have h := inside_segment L 0 0 0 (2/5) (39/40) O G (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have H : ¬L.Inside 0 (1/2) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    exact missing (C1092MMMPActualProfile.top_origin_of_left_halfpoint p hf hb h)
  have X : ¬L.Inside (1/2) 0 := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 8 7 (by decide) _ _ ⟨h,northwest_left p hf hb⟩
  have sign : L.s<0 := by
    by_contra nonnegative
    have sn : 0≤L.s := le_of_not_gt nonnegative
    have dn : Normal L.c L.s :=
      ⟨sn,by simpa only [abs_of_nonneg sn] using range,L.unit_normal⟩
    have faces := C1092MMMPLeftCenterFaces.positive L dn side O T H X cut
    let K := (owners p 3).translated 1 2
    have kActual (x y : ℝ) : K.Inside x y ↔ (owners p 3).Inside (1+x) (2+y) :=
      inside_translated_iff _ _ _ _ _
    have corner : (owners p 3).Inside 1 3 := by
      simpa [cornerOwner,cornerPoint] using corner_points p hf 3
    exact C1092MMMPCenterCorner.impossible L K side
      (shape.trans (side_same p 8 3)) dn faces.1 faces.2.2.le cut G
      (by apply (kActual _ _).mpr; norm_num; exact corner_halfpoint p hf hb missing)
      (by apply (kActual _ _).mpr; norm_num; exact corner)
      (by
        intro own
        have h := (kActual _ _).mp own
        norm_num at h
        exact owners_disjoint p hf 3 11 (by decide) _ _ ⟨h,top_alternative p hf hb missing⟩)
      (fun x y own => owners_disjoint p hf 8 3 (by decide) _ _
        ⟨(actual _ _).mp own.1,(kActual _ _).mp own.2⟩)
  have dn : Normal L.c (-L.s) := ⟨by linarith only [sign],
    by simpa only [abs_of_neg sign] using range,by nlinarith only [L.unit_normal]⟩
  have faces := C1092MMMPLeftCenterFaces.negative L dn side O T H X cut
  exact ⟨L,shape,actual,dn,sign,cut,faces.2.2,faces.2.1⟩

#print axioms negative_left_of_missing_top
end N12Compact.C1092MMMPTopOriginSign
