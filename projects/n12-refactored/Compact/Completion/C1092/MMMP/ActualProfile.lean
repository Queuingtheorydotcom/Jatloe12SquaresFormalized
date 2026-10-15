import Compact.Completion.C1092.MMMP.NortheastActualSign
import Compact.Completion.C1092.MMMP.StrongNortheastFaces
import Compact.Completion.C1092.MMMP.ProfileAdapter
import Compact.Completion.C1092.MMMP.RightFar
import Compact.Completion.CommonCases.OriginalOwners

/-! The remaining strong northeast profile reduces to two strict points
of named original wall owners. Every other face, the canonical sign and
the angle bound come from the existing original-family entrance. The two
wall points remain explicit premises; this is not a completed branch. -/
namespace N12Compact.C1092MMMPActualProfile
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

/-- Only these two actual wall ownership facts remain to use the existing
strong profile ending. Their strictness is essential: closed boundary
membership would not justify any disjointness contradiction below. -/
def WallPoints (p : NormalizedPacking) : Prop :=
  (owners p 11).Inside 2 3 ∧ (owners p 10).Inside 3 (64/25)

/-- The unresolved right near-point exclusion is sufficient for the
entire strong right bar. The original right-inner exclusion supplies the
other omission required by the all-angle wall-reach theorem. -/
theorem right_reach_of_missing_near (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (missing : ¬(owners p 10).Inside 3 (87/50)) :
    (owners p 10).Inside 3 (64/25) := by
  have mark : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have h := WallLowerReach.point (pullX (owners p 10)) (side_gt p 10)
    (container_pullX _ (p.contained _))
    (by norm_num [inside_pullX]; exact mark)
    (by norm_num [inside_pullX]; exact C1092MMMPRightFar.point p hf hb)
    (by norm_num [inside_pullX]; exact missing)
    (by
      norm_num [inside_pullX]
      exact C1092MMMPRightInnerActual.right_missing_inner p hf hb)
  norm_num [inside_pullX] at h
  exact h

/-- A strict halfpoint in the actual left wall excludes that point from
the actual northwest corner. The shared wall-corner theorem then gives
the top origin without introducing a separate corner profile premise. -/
theorem top_origin_of_left_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (halfpoint : (owners p 8).Inside 1 (5/2)) :
    (owners p 11).Inside 2 3 := by
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
    (by
      norm_num [K,inside_pullY]
      exact fun own => owners_disjoint p hf 3 8 (by decide) _ _ ⟨own,halfpoint⟩)
    (fun x y own => owners_disjoint p hf 3 11 (by decide) _ _
      ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [B,inside_pullY] at h
  exact h

theorem wall_points_of_entrance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (halfpoint : (owners p 8).Inside 1 (5/2))
    (missing : ¬(owners p 10).Inside 3 (87/50)) : WallPoints p :=
  ⟨top_origin_of_left_halfpoint p hf hb halfpoint,
    right_reach_of_missing_near p hf hb missing⟩

noncomputable def strong_northeast (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (wall : WallPoints p) :
    C1092MMMPProfileAdapter.StrongNortheast p := by
  classical
  let N := Classical.choose (C1092MMMPNortheastActualSign.exists_positive p hf hb)
  have np : C1092MMMPNortheastActualSign.PositiveActual p N :=
    Classical.choose_spec (C1092MMMPNortheastActualSign.exists_positive p hf hb)
  have markerN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have inner : (owners p 7).Inside 2 (12/5) := by
    have h := inside_segment (owners p 7) 2 2 2 (5/2) (4/5)
      (northwest_center p hf hb) (northwest_north p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have rightBar (y : ℝ) (low : 13/50≤y) (high : y≤14/25) :
      (owners p 10).Inside 3 (2+y) := by
    exact CommonCases.OriginalOwners.vertical_segment _ _ _ _ _
      (wall_auxiliaries p hb).2.2.1 wall.2 (by norm_num)
      (by linarith only [low]) (by linarith only [high])
  have profile := C1092MMMPStrongNortheastFaces.profile N
    (by rw [np.side]; exact side_gt p 6) np.normal
    (by apply (np.actual _ _).mpr; norm_num; exact markerN)
    (by apply (np.actual _ _).mpr; norm_num; exact (northeast_pair p hf hb).2)
    (by
      intro own
      have h := (np.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 7 (by decide) _ _
        ⟨h,(northwest_pair p hf hb).1⟩)
    (by
      intro own
      have h := (np.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,inner⟩)
    (by
      intro own
      have h := (np.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,wall.1⟩)
    (by
      intro own
      have h := (np.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨h,corner⟩)
    (by
      intro y low high own
      have h := (np.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,rightBar y low high⟩)
  exact ⟨N,np.side,(fun x y => by simpa only [add_comm] using np.actual x y),
    np.normal,profile.2,profile.1⟩

theorem impossible_of_wall_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (wall : WallPoints p) : False :=
  C1092MMMPProfileAdapter.family_impossible p hf hb (strong_northeast p hf hb wall)

/-- The unresolved geometry is the universal derivation of the two
strict wall points. All original-family and whole-packing hypotheses are
preserved by the existing branch transport. -/
theorem branch_of_wall_points
    (derive : ∀ (p : NormalizedPacking), codedMarkerFamily p=family →
      WallContext p mmmp → WallPoints p) : BranchEnding 1 :=
  C1092MMMPProfileAdapter.branch_of_profile
    (fun p hf hb => strong_northeast p hf hb (derive p hf hb))

#print axioms strong_northeast
#print axioms branch_of_wall_points
end N12Compact.C1092MMMPActualProfile
