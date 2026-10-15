import Compact.Completion.C1092.MMMP.RightFar
import Compact.Completion.C1092.MMMP.NortheastEarlyFaces

/-! The genuine northeast upper faces and strict upper point before the
top origin. The right G9 input has its actual original owner, and the
northwest small-angle consequence keeps both original central faces. -/
namespace N12Compact.C1092MMMPNortheastEarlyActual
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore C1092MMMPEndingAxes C977CornerCubic
set_option Elab.async false

structure Profile (p : NormalizedPacking) (B : OpenSquare) : Prop where
  side : B.side=(owners p 6).side
  actual : ∀ x y, B.Inside x y ↔ (owners p 6).Inside (2+y) (2-x)
  normal : Normal B.c B.s
  positive : 0<B.s
  faces : C1092MMMPNortheastEarlyFaces.Data B

theorem exists_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : ∃ B : OpenSquare, Profile p B := by
  obtain ⟨N,np⟩ := C1092MMMPNortheastActualSign.exists_positive p hf hb
  let B := clockwise N
  have actual (x y : ℝ) : B.Inside x y ↔ (owners p 6).Inside (2+y) (2-x) := by
    simpa only [B,inside_clockwise,sub_eq_add_neg] using np.actual y (-x)
  have ne := northeast_pair p hf hb
  have mark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markT : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have middle : (owners p 7).Inside 2 (12/5) := by
    have h := inside_segment (owners p 7) 2 2 2 (5/2) (4/5)
      (northwest_center p hf hb) (northwest_north p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have faces := C1092MMMPNortheastEarlyFaces.faces B
    (by dsimp [B,clockwise]; rw [np.side]; exact side_gt p 6) np.normal np.positive
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact ne.1)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,middle⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,C1092MMMPRightFar.point p hf hb⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,markT⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨h,corner⟩)
  exact ⟨B,np.side,actual,np.normal,np.positive,faces⟩

theorem upper_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 6).Inside (107/50) (5/2) := by
  obtain ⟨B,bp⟩ := exists_profile p hf hb
  have h := C1092MMMPNortheastEarlyFaces.upper_point B
    (by rw [bp.side]; exact side_gt p 6) bp.faces
  have result := (bp.actual _ _).mp h
  norm_num at result
  exact result

theorem small_northwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (C : OpenSquare) (shape : C.side=(owners p 7).side)
    (actual : ∀ x y, C.Inside x y ↔ (owners p 7).Inside (2+x) (2+y))
    (cn : Normal C.c (-C.s)) : -C.s<7/50 ∧ 99/100<C.c := by
  obtain ⟨B,bp⟩ := exists_profile p hf hb
  let A := clockwise C
  have aInside (x y : ℝ) : A.Inside x y ↔ (owners p 7).Inside (2+y) (2-x) := by
    simpa only [A,inside_clockwise,sub_eq_add_neg] using actual y (-x)
  have markA : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markB : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markSW : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  exact C1092MMMPNortheastEarlyFaces.small_central A B
    (by dsimp [A,clockwise]; rw [shape]; exact side_gt p 7)
    (shape.trans ((side_same p 7 6).trans bp.side.symm)) cn bp.normal bp.positive
    (by apply (aInside _ _).mpr; norm_num; exact northwest_center p hf hb)
    (by apply (aInside _ _).mpr; norm_num; exact northwest_left p hf hb)
    (by apply (aInside _ _).mpr; norm_num; exact markA)
    (by
      intro own
      have h := (aInside _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨h,markSW⟩)
    (by apply (bp.actual _ _).mpr; norm_num; exact markB)
    (by apply (bp.actual _ _).mpr; norm_num; exact (northeast_pair p hf hb).1)
    bp.faces
    (fun x y own => owners_disjoint p hf 7 6 (by decide) _ _
      ⟨(aInside _ _).mp own.1,(bp.actual _ _).mp own.2⟩)

#print axioms upper_point
#print axioms small_northwest
end N12Compact.C1092MMMPNortheastEarlyActual
