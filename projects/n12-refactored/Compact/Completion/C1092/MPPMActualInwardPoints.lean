import Compact.Completion.C1092.MPPMActualWallReduction
import Compact.Completion.C1092.MPPMInwardNeighbors
import Compact.Completion.C1092.MPPMPositiveSeedsActual
import Compact.Completion.C1092.MPPMInwardFinalCenteredCaps
import Compact.Completion.C1092.MPPMInwardFinalCentered
import Compact.Completion.CommonCases.InwardPoint

/-! Original-owner producers for the inward pipeline. All square
charts below are translations and face reindexings of one actual owner.
In particular the bottom and right bars each have one named owner.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic
set_option Elab.async false
noncomputable section

theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

theorem marker_owned (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

structure Frame (p : NormalizedPacking) (i : Fin 12) (C : OpenSquare) : Prop where
  side : C.side=(owners p i).side
  actual : ∀ x y,C.Inside x y ↔ (owners p i).Inside (2+x) (2+y)

noncomputable def chart (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  (owners p i).translated 2 2

theorem chart_frame (p : NormalizedPacking) (i : Fin 12) : Frame p i (chart p i) :=
  ⟨rfl,fun x y => inside_translated_iff _ _ _ _ _⟩

theorem canonical_frame (p : NormalizedPacking) (i : Fin 12) :
    ∃ C : OpenSquare,Frame p i C ∧ 0<C.c ∧ |C.s|≤C.c := by
  obtain ⟨C,cp,canonical,same,inside,closed⟩ := ClosedFrames.canonical_frame (chart p i)
  exact ⟨C,⟨same,fun x y => (inside x y).trans ((chart_frame p i).actual x y)⟩,cp,canonical⟩

theorem Frame.apart {p : NormalizedPacking} (hf : codedMarkerFamily p=family)
    {i j : Fin 12} {C D : OpenSquare} (c : Frame p i C) (d : Frame p j D) (ne : i≠j) :
    ∀ x y,¬(C.Inside x y ∧ D.Inside x y) := fun x y both =>
  owners_disjoint p hf i j ne _ _ ⟨(c.actual x y).mp both.1,(d.actual x y).mp both.2⟩

theorem successor_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4)) :
    (owners p 5).Inside (5/2) 1 := by
  have pair := C1092MPPMInwardNeighbors.southeast_pair p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) inward
  let g : Transform := ⟨true,true,false⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have P : (owners (g.pullPacking p) 4).Inside 1 (87/50) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX]
    exact pair.2
  have G : (owners (g.pullPacking p) 4).Inside 1 (8/5) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX]
    exact pair.1
  have omitted : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX]
    exact fun own => owners_disjoint p hf 5 4 (by decide) _ _ ⟨own,inward.1⟩
  have point := C1092MPPMPositiveSeedsActual.missing_halfpoint
    (g.pullPacking p) (family_transport g p hf) context P G omitted
  rw [owners_transport g p hf 4] at point
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX] at point
  exact point

theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4)) : (owners p 10).Inside 3 2 := by
  let g : Transform := ⟨true,true,false⟩
  have half : (owners (g.pullPacking p) 4).Inside 1 (3/2) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX]
    exact successor_halfpoint p hf hb inward
  have bottom : (owners (g.pullPacking p) 9).Inside (8/5) 1 := by
    rw [owners_transport g p hf 9]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX]
    exact (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2
  have origin := C1092MPPMPositiveSeedsActual.bottom_origin_of_halfpoint
    (g.pullPacking p) (family_transport g p hf) bottom half
  rw [owners_transport g p hf 9] at origin
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap,inside_pullX] at origin
  exact origin

theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4)) :
    ∀ y : ℝ,-2/5≤y → y≤0 → (chart p 10).Inside 1 y := by
  have lower := (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2
  have upper := right_origin p hf hb inward
  have bar := Completion.OtherCases.WallProfile.vertical_owned (owners p 10) 3 (8/5) 2
    (by norm_num) lower upper
  intro y low high
  rw [(chart_frame p 10).actual]
  norm_num
  exact bar _ (by linarith only [low]) (by linarith only [high])

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) :
    ∀ x : ℝ,-2/5≤x → x≤-13/50 → (chart p 9).Inside x (-1) := by
  have pair := (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1
  intro x low high
  let t := (50/7)*(x+2/5)
  have point := inside_segment (owners p 9) (8/5) 1 (87/50) 1 t pair.1 pair.2
    (by dsimp [t]; linarith only [low]) (by dsimp [t]; linarith only [high])
  rw [(chart_frame p 9).actual]
  norm_num
  convert point using 1 <;> dsimp [t] <;> ring

theorem bottom_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : BottomCorner (chart p 9) (chart p 0) := by
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_owned p hf 9 13 (by decide +kernel)
  have km : (owners p 0).Inside 1 (457/500) := by
    simpa [marker] using marker_owned p hf 0 0 (by decide +kernel)
  have kp : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  refine ⟨side_gt p 9,side_same p 9 0,?_,?_,?_,?_,?_,?_,
    Frame.apart hf (chart_frame p 0) (chart_frame p 9) (by decide)⟩
  · intro x y own
    have actual := ((chart_frame p 9).actual x y).mp own
    have wall := (p.contained _ _ _ actual).2.2.1
    linarith only [wall]
  · intro x y own
    have actual := ((chart_frame p 0).actual x y).mp own
    have wall := p.contained _ _ _ actual
    constructor <;> linarith only [wall.1,wall.2.2.1]
  · rw [(chart_frame p 9).actual]; norm_num; exact bm
  · rw [(chart_frame p 9).actual]; norm_num
    exact (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1.1
  · rw [(chart_frame p 0).actual]; norm_num; exact km
  · rw [(chart_frame p 0).actual]; norm_num; exact kp

theorem predecessor_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (W : OpenSquare) (frame : Frame p 7 W) : PredecessorPoints W := by
  have pair := C1092MPPMInwardNeighbors.northwest_pair p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) inward
  have wm : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_owned p hf 7 11 (by decide +kernel)
  have tm : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_owned p hf 11 15 (by decide +kernel)
  have km : (owners p 3).Inside 1 (1543/500) := by
    simpa [marker] using marker_owned p hf 3 6 (by decide +kernel)
  have kp : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [frame.actual]; norm_num; exact wm
  · rw [frame.actual]; norm_num; exact pair.2
  · rw [frame.actual]; norm_num; exact pair.1
  · rw [frame.actual]; norm_num
    exact fun own => owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,tm⟩
  · rw [frame.actual]; norm_num
    exact fun own => owners_disjoint p hf 7 3 (by decide) _ _ ⟨own,kp⟩
  · rw [frame.actual]; norm_num
    exact fun own => owners_disjoint p hf 7 3 (by decide) _ _ ⟨own,km⟩

theorem missing_outer_sharp (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (inward : Inward (owners p 4)) (missing : ¬(owners p 4).Inside 1 (8/5)) :
    (owners p 4).Inside (199/100) (73/50) := by
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_owned p hf 4 8 (by decide +kernel)
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_owned p hf 5 9 (by decide +kernel)
  have wm : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_owned p hf 7 11 (by decide +kernel)
  let g : Transform := ⟨true,false,true⟩
  have actual (x y : ℝ) : (g.pull (owners p 4)).Inside x y ↔ (owners p 4).Inside y (4-x) := by
    simp only [g,Transform.pull,inside_pullSwap,inside_pullY]
  have point := CommonCases.InwardPoint.strong_original (g.pull (owners p 4)) (side_gt p 4)
    (by rw [actual]; norm_num; exact cm)
    (by rw [actual]; norm_num; exact inward.2)
    (by rw [actual]; norm_num; exact inward.1)
    (by rw [actual]; norm_num
        exact fun own => owners_disjoint p hf 4 7 (by decide) _ _ ⟨own,wm⟩)
    (by rw [actual]; norm_num
        exact fun own => owners_disjoint p hf 4 5 (by decide) _ _ ⟨own,em⟩)
    (by rw [actual]; norm_num; exact missing)
  rw [actual] at point
  norm_num at point
  exact point

end
#print axioms successor_halfpoint
#print axioms right_origin
#print axioms predecessor_points
#print axioms missing_outer_sharp
end N12Compact.C1092MPPMActualInward
