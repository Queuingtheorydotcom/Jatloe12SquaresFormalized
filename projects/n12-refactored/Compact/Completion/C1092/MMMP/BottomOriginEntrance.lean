import Compact.Completion.C1092.MMMP.PositiveInwardHalfangle
import Compact.Completion.C1092.MMMP.SoutheastSign

/-! Literal actual-owner entrance from DOUBLE-RIGHT-BOTTOM-ORIGIN section 4
and RIGHT-NEAR-BOTTOM-ORIGIN section 3. The strict right near point is enough;
the southeast outer-point exclusion remains an explicit separate premise.

The whole-boundary support contradiction of DOUBLE-RIGHT-BOTTOM-ORIGIN
sections 1.2--3 is not asserted here. The source conclusion is the actual
southeast half-angle point needed by that completed prose argument. -/
namespace N12Compact.C1092MMMPBottomOriginEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

/-- The genuine corner transfer forces the southeast corner's halfpoint
if the actual bottom square omits its origin. -/
theorem corner_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (missing : ¬(owners p 9).Inside 2 1) :
    (owners p 1).Inside 3 (3/2) := by
  classical
  by_contra absent
  let B := pullX (owners p 9)
  let K := pullX (owners p 1)
  have boxB : InsideContainer B := container_pullX _ (p.contained _)
  have boxK : InsideContainer K := container_pullX _ (p.contained _)
  have markerB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have markerK : (owners p 1).Inside 3 (457/500) := by
    simpa [marker] using marker_point p hf 1 2 (by decide +kernel)
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have point := Completion.OtherCases.WallProfile.boundary_origin B K
    (457/500) (8/5) (side_gt p 9) (side_same p 9 1)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [B,inside_pullX]; exact markerB)
    (by norm_num [B,inside_pullX]; exact (C1092MMMPBottomPair.pair p hf hb).1)
    (by norm_num [K,inside_pullX]; exact markerK)
    (by norm_num [K,inside_pullX]; exact corner)
    (by norm_num [K,inside_pullX]; exact absent)
    (fun x y own => owners_disjoint p hf 1 9 (by decide) _ _
      ⟨(inside_pullX _ _ _).mp own.1,(inside_pullX _ _ _).mp own.2⟩)
  norm_num [B,inside_pullX] at point
  exact missing point

/-- A missing bottom origin produces the precise strict southeast
half-angle point of the original prose, in the same actual square frame. -/
theorem southeast_halfangle (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (outerMissing : ¬(owners p 5).Inside 3 (8/5))
    (bottomMissing : ¬(owners p 9).Inside 2 1) :
    ∃ C : OpenSquare, C1092MMMPSoutheastSign.PositiveActual p C ∧
      C.Inside 1 (C1092WallProfileScalars.half C.c C.s) := by
  obtain ⟨C,actual⟩ := C1092MMMPSoutheastSign.exists_positive p hf hb near
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have markerC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  refine ⟨C,actual,?_⟩
  apply C1092MMMPPositiveInwardHalfangle.point C
    (by rw [actual.side]; exact side_gt p 5) actual.normal
  · apply (actual.actual _ _).mpr
    norm_num
    exact markerC
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.2
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.1
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact outerMissing h
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 1 (by decide) _ _
      ⟨h,corner_halfpoint p hf hb bottomMissing⟩
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom.2⟩

#print axioms corner_halfpoint
#print axioms southeast_halfangle
end N12Compact.C1092MMMPBottomOriginEntrance
