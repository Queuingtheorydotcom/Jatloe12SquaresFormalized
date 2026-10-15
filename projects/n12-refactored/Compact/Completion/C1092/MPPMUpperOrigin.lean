import Compact.Completion.C1092.MPPMRightInner
import Compact.Completion.C1092.MMMP.MarkerHalfpoint
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! The northeast ordinary halfpoint and the original top-wall origin
in the one-omission entrance. Both actual corner walls and the foreign
wall-marker offset are retained in the shared geometric transfers. -/
namespace N12Compact.C1092MPPMUpperOrigin
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092RigidCharts
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem northeast_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 6).Inside 3 (5/2) := by
  let N := translate (pullY (owners p 6)) 2 2
  have actual (x y : ℝ) : N.Inside x y ↔ (owners p 6).Inside (2+x) (2-y) := by
    rw [N,inside_translate,inside_pullY]
    rw [show x+2=2+x by ring,show 4-(y+2)=2-y by ring]
  have pair := (omitted_bottom_neighbors p hf hb omitted).1
  have mark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have rightMark : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have mid := C1092MPPMPointCore.rectangle p hf hb omitted (113/50) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := C1092MMMPMarkerHalfpoint.point N (43/500) (by norm_num) (by norm_num)
    (side_gt p 6)
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact pair.1)
    (by apply (actual _ _).mpr; norm_num; exact pair.2)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 5 (by decide) _ _ ⟨own',mid⟩)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨own',rightMark⟩)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨own',corner⟩)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 11 (by decide) _ _
        ⟨own',(wall_auxiliaries p hb).2.2.2⟩)
  have result := (actual _ _).mp h
  norm_num at result
  exact result

theorem top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 11).Inside 2 3 := by
  let B := pullY (pullX (owners p 11))
  let K := pullY (pullX (owners p 2))
  have boxB : InsideContainer B := container_pullY _ (container_pullX _ (p.contained _))
  have boxK : InsideContainer K := container_pullY _ (container_pullX _ (p.contained _))
  have markerB : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have markerK : (owners p 2).Inside 3 (1543/500) := by
    simpa [marker] using marker_point p hf 2 4 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have actualB (x y : ℝ) : B.Inside x y ↔ (owners p 11).Inside (4-x) (4-y) := by
    rw [B,inside_pullY,inside_pullX]
  have actualK (x y : ℝ) : K.Inside x y ↔ (owners p 2).Inside (4-x) (4-y) := by
    rw [K,inside_pullY,inside_pullX]
  have h := Completion.OtherCases.WallProfile.boundary_origin B K (457/500) (8/5)
    (side_gt p 11) (side_same p 11 2)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by apply (actualB _ _).mpr; norm_num; exact markerB)
    (by apply (actualB _ _).mpr; norm_num; exact (C1092MPPMRightInner.other_ordinary p hf hb omitted).2)
    (by apply (actualK _ _).mpr; norm_num; exact markerK)
    (by apply (actualK _ _).mpr; norm_num; exact corner)
    (by
      intro own
      have own' := (actualK _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 2 6 (by decide) _ _ ⟨own',northeast_halfpoint p hf hb omitted⟩)
    (fun x y own => owners_disjoint p hf 2 11 (by decide) _ _
      ⟨(actualK _ _).mp own.1,(actualB _ _).mp own.2⟩)
  have result := (actualB _ _).mp h
  norm_num at result
  exact result

theorem top_segment (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (x : ℝ) (low : 2≤x) (high : x≤12/5) : (owners p 11).Inside x 3 :=
  CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _
    (top_origin p hf hb omitted) (C1092MPPMRightInner.other_ordinary p hf hb omitted).2
    (by norm_num) low high

#print axioms northeast_halfpoint
#print axioms top_origin
end N12Compact.C1092MPPMUpperOrigin
