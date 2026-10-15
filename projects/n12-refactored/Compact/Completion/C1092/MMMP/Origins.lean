import Compact.Completion.C1092.MMMPEntrance
import Compact.Completion.C1092.MMMP.MarkerHalfpoint
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Geometry.WallLowerReach
import Compact.Completion.C981.Crosspoint
import Compact.Completion.CommonCases.InwardPoint

/-! Actual MMMP top reach, left and right origins, and the unconditional
NW left crosspoint. Each wall-origin transfer keeps its genuine paired
corner, true container walls, and a halfpoint with a named foreign owner. -/
namespace N12Compact.C1092MMMPOrigins
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance
open N12Compact.Completion.OtherCases.WallProfile
set_option Elab.async false

theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem top_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 11).Inside (36/25) 3 := by
  let g : Transform := ⟨true,true,true⟩
  have top := top_pair p hf hb
  have ne := northeast_pair p hf hb
  have nw := northwest_pair p hf hb
  have mark : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have h := WallLowerReach.point (g.pull (owners p 11)) (side_gt p 11)
    (container_transform g _ (p.contained _))
    (by norm_num [g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact mark)
    (by norm_num [g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact top.1)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
      intro own
      exact owners_disjoint p hf 11 6 (by decide) _ _ ⟨own,ne.2⟩)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
      intro own
      exact owners_disjoint p hf 11 7 (by decide) _ _ ⟨own,nw.1⟩)
  norm_num [g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at h
  exact h

theorem top_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 11).Inside (3/2) 3 := by
  have h := inside_segment (owners p 11) (36/25) 3 (8/5) 3 (3/8)
    (top_far p hf hb) (top_pair p hf hb).1 (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 8).Inside 1 2 := by
  let g : Transform := ⟨true,false,true⟩
  let B := g.pull (owners p 8)
  let K := g.pull (owners p 3)
  have boxB : InsideContainer B := container_transform g _ (p.contained _)
  have boxK : InsideContainer K := container_transform g _ (p.contained _)
  have markB : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have markK : (owners p 3).Inside (457/500) 3 := by
    simpa [marker] using marker_point p hf 3 7 (by decide +kernel)
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  have bMark : B.Inside 2 (457/500) := by
    norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullY]
    exact markB
  have bAux : B.Inside (87/50) 1 := by
    norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullY]
    exact (wall_auxiliaries p hb).1
  have kMark : K.Inside 1 (457/500) := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullY]
    exact markK
  have kCorner : K.Inside 1 1 := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullY]
    exact corner
  have kMissing : ¬K.Inside 1 (3/2) := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullY]
    intro own
    exact owners_disjoint p hf 3 11 (by decide) _ _ ⟨own,top_halfpoint p hf hb⟩
  have apart : ∀ x y, ¬(K.Inside x y ∧ B.Inside x y) := by
    intro x y own
    have first := (inside_pull g _ _ _).mp own.1
    have last := (inside_pull g _ _ _).mp own.2
    exact owners_disjoint p hf 3 8 (by decide) _ _ ⟨first,last⟩
  have h := boundary_origin B K (457/500) (87/50) (side_gt p 8) (side_same p 8 3)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bMark bAux kMark kCorner kMissing apart
  norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullY] at h
  exact h

theorem northeast_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 6).Inside (5/2) 3 := by
  let g : Transform := ⟨true,true,false⟩
  let q := (g.pull (owners p 6)).translated 2 2
  have ne := northeast_pair p hf hb
  have nw := northwest_pair p hf hb
  have mark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have topMark : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have h := C1092MMMPMarkerHalfpoint.point q (43/500) (by norm_num) (by norm_num)
    (side_gt p 6)
    (by norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]; exact mark)
    (by norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]; exact ne.2)
    (by norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]; exact ne.1)
    (by
      norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨own,nw.1⟩)
    (by
      norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨own,topMark⟩)
    (by
      norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨own,corner⟩)
    (by
      norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨own,(wall_auxiliaries p hb).2.2.1⟩)
  norm_num [q,inside_translated_iff,g,Transform.pull,inside_pullSwap,inside_pullX] at h
  exact h

theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 10).Inside 3 2 := by
  let g : Transform := ⟨true,true,true⟩
  let B := g.pull (owners p 10)
  let K := g.pull (owners p 2)
  have boxB : InsideContainer B := container_transform g _ (p.contained _)
  have boxK : InsideContainer K := container_transform g _ (p.contained _)
  have markB : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have markK : (owners p 2).Inside (1543/500) 3 := by
    simpa [marker] using marker_point p hf 2 5 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have bMark : B.Inside 2 (457/500) := by
    norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
    exact markB
  have bAux : B.Inside (87/50) 1 := by
    norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
    exact (wall_auxiliaries p hb).2.2.1
  have kMark : K.Inside 1 (457/500) := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
    exact markK
  have kCorner : K.Inside 1 1 := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
    exact corner
  have kMissing : ¬K.Inside 1 (3/2) := by
    norm_num [K,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
    intro own
    exact owners_disjoint p hf 2 6 (by decide) _ _ ⟨own,northeast_halfpoint p hf hb⟩
  have apart : ∀ x y, ¬(K.Inside x y ∧ B.Inside x y) := by
    intro x y own
    have first := (inside_pull g _ _ _).mp own.1
    have last := (inside_pull g _ _ _).mp own.2
    exact owners_disjoint p hf 2 10 (by decide) _ _ ⟨first,last⟩
  have h := boundary_origin B K (457/500) (87/50) (side_gt p 10) (side_same p 10 2)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bMark bAux kMark kCorner kMissing apart
  norm_num [B,g,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at h
  exact h

theorem northwest_left (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside (3/2) 2 := by
  let g : Transform := ⟨true,true,false⟩
  have nw := northwest_pair p hf hb
  have mark : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have neMark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have swMark : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have h := C981CompletionCrosspoint.point (g.pull (owners p 7)) (side_gt p 7)
    (by norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]; exact nw.2)
    (by norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]; exact nw.1)
    (by norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]; exact mark)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,neMark⟩)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,swMark⟩)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,(top_pair p hf hb).1⟩)
    (by
      norm_num [g,Transform.pull,inside_pullSwap,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,top_halfpoint p hf hb⟩)
  norm_num [g,Transform.pull,inside_pullSwap,inside_pullX] at h
  exact h

#print axioms left_origin
#print axioms right_origin
#print axioms northwest_left
end N12Compact.C1092MMMPOrigins
