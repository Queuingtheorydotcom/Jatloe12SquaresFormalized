import Compact.Completion.C1092.MPPMActualInwardPositive
import Compact.Completion.C1092.MPPMInwardPositiveSuccessor

/-! Literal actual entrance for positive missing-center inward C.
The predecessor wall origin below depends only on the opposite inward
pair, before any sign, outer-G or center classification of that owner.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem positive_missing_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (missing : ¬(owners p 4).Inside 2 2)
    (C E : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E) (cn : Normal C.c C.s) :
    C1092MPPMInwardPositive.PairInput C E := by
  have empty := C1092MPPMActualWallReduction.no_missing p hf hb
  have pair := C1092MPPMInwardNeighbors.southeast_pair p hf hb empty inward
  have anchors := central_anchors p hf C c
  have outer := nonnegative_outer_missing p hf hb inward nonordinary C c cn
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_owned p hf 5 9 (by decide +kernel)
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_owned p hf 9 13 (by decide +kernel)
  have km : (owners p 1).Inside 3 (457/500) := by
    simpa [marker] using marker_owned p hf 1 2 (by decide +kernel)
  have kp : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have source : C1092MPPMInwardPositive.Input C :=
    { side := by rw [c.side]; exact side_gt p 4
      normal := cn
      marker := anchors.1
      inner := by rw [c.actual]; norm_num; exact inward.1
      forward := by rw [c.actual]; norm_num; exact inward.2
      crosspoint := by
        rw [c.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb empty inward
      sharp := by rw [c.actual]; norm_num; exact missing_outer_sharp p hf inward outer
      origin := by rw [c.actual]; norm_num; exact missing
      outer := by rw [c.actual]; norm_num; exact outer
      bottom := by
        rw [c.actual]; norm_num
        exact fun own => owners_disjoint p hf 4 9 (by decide) _ _
          ⟨own,(C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1.1⟩
      northwest := anchors.2.2 }
  refine
    { source := source
      same := c.side.trans ((side_same p 4 5).trans e.side.symm)
      recipient := ?_
      halfpoint := by rw [e.actual]; norm_num; exact successor_halfpoint p hf hb inward
      apart := Frame.apart hf c e (by decide) }
  refine
    { side := by rw [e.side]; exact side_gt p 5
      successorMarker := by rw [e.actual]; norm_num; exact em
      near := by rw [e.actual]; norm_num; exact pair.2
      outer := by rw [e.actual]; norm_num; exact pair.1
      missingInner := ?_
      missingRight := ?_
      missingBottom := ?_
      missingCorner := ?_
      missingCornerMarker := ?_ }
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 4 (by decide) _ _ ⟨own,inward.1⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 10 (by decide) _ _
      ⟨own,(C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bm⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,kp⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,km⟩

theorem opposite_inward_left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm)
    (inward : (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2) :
    (owners p 8).Inside 1 2 := by
  let g : Transform := ⟨false,true,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have inward' : Inward (owners (g.pullPacking p) 4) := by
    rw [owners_transport g p hf 4]
    norm_num [Inward,g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY]
    exact inward
  have point := right_origin (g.pullPacking p) (family_transport g p hf) context inward'
  rw [owners_transport g p hf 10] at point
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY] at point
  exact point

theorem left_seed_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) :
    (chart p 8).Inside (-543/500) 0 ∧ (chart p 8).Inside (-1) (13/50) := by
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_owned p hf 8 12 (by decide +kernel)
  constructor
  · rw [(chart_frame p 8).actual]; norm_num; exact lm
  · rw [(chart_frame p 8).actual]; norm_num
    exact (C1092MPPMActualWallReduction.wall_pairs p hf hb).1.1

theorem left_seed_segment (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (t : ℝ) (low : 0≤t) (high : t≤1) :
    (chart p 8).Inside (-543/500+(43/500)*t) ((13/50)*t) := by
  have pair := left_seed_points p hf hb
  have point := inside_segment (chart p 8) (-543/500) 0 (-1) (13/50) t pair.1 pair.2 low high
  convert point using 1 <;> ring

end
#print axioms positive_missing_input
#print axioms opposite_inward_left_origin
#print axioms left_seed_segment
end N12Compact.C1092MPPMActualInward
