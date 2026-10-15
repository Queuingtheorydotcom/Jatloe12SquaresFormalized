import Compact.Completion.C1092.MMMMWalls
import Compact.Completion.C1092.MMMMEnding

/-! The full original MMMM entrance and the genuine BranchEnding2 contract.
All points belong to named original owners; its two short chord endpoints
come from actual wall bars, actual corners and the same strict NE triangle. -/
namespace N12Compact.C1092MMMM
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMMEntrance C1092RigidCharts
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : False := by
  have triangle := C1092MMMMStrictCore.northeast_triangle p hf hb
  have east := southeast_pair p hf hb
  have west := northwest_pair p hf hb
  have mN : (owners p 6).Inside (47/20) (47/20) := by
    have h : Owns (owners p 6) 10 := (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have mE : (owners p 5).Inside (47/20) (33/20) := by
    have h : Owns (owners p 5) 9 := (owners_markers p hf 5 9).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have mW : (owners p 7).Inside (33/20) (47/20) := by
    have h : Owns (owners p 7) 11 := (owners_markers p hf 7 11).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have bottom : (owners p 9).Inside (239/100) 1 := by
    have h := local_wall_segment p mmmm hb 1 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmm,wallOwner,pointMap,branchY] at h
    exact h
  have left : (owners p 8).Inside 1 (239/100) := by
    have h := local_wall_segment p mmmm hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmm,wallOwner,pointMap,branchY] at h
    exact h
  have innerX : (owners p 6).Inside (239/100) 2 := by
    have h := inside_segment (owners p 6) 2 2 (5/2) 2 (39/50)
      triangle.1 triangle.2.1 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have innerY : (owners p 6).Inside 2 (239/100) := by
    have h := inside_segment (owners p 6) 2 2 2 (5/2) (39/50)
      triangle.1 triangle.2.2 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have cornerE : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have cornerW : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  let N := translate (owners p 6) 2 2
  let E := translate (owners p 5) 2 2
  let W := translate (owners p 7) 2 2
  have data : C1092MMMMEnding.Data N E W where
    side := side_gt p 6
    sameE := side_same p 6 5
    sameW := side_same p 6 7
    origin := by norm_num [N,inside_translate]; exact triangle.1
    halfX := by norm_num [N,inside_translate]; exact triangle.2.1
    halfY := by norm_num [N,inside_translate]; exact triangle.2.2
    markerN := by norm_num [N,inside_translate]; exact mN
    markerE := by norm_num [E,inside_translate]; exact mE
    ordinaryE1 := by norm_num [E,inside_translate]; exact east.1
    ordinaryE2 := by norm_num [E,inside_translate]; exact east.2
    markerW := by norm_num [W,inside_translate]; exact mW
    ordinaryW1 := by norm_num [W,inside_translate]; exact west.2
    ordinaryW2 := by norm_num [W,inside_translate]; exact west.1
    eLeftBottom := by
      norm_num [E,inside_translate]
      exact fun h => owners_disjoint p hf 5 1 (by decide) _ _ ⟨h,cornerE⟩
    eLeftTop := by
      norm_num [E,inside_translate]
      exact fun h => owners_disjoint p hf 5 10 (by decide) _ _
        ⟨h,C1092MMMMWalls.right_origin p hf hb⟩
    eRightBottom := by
      norm_num [E,inside_translate]
      exact fun h => owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom⟩
    eRightTop := by
      norm_num [E,inside_translate]
      exact fun h => owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,innerX⟩
    wLeftBottom := by
      norm_num [W,inside_translate]
      exact fun h => owners_disjoint p hf 7 3 (by decide) _ _ ⟨h,cornerW⟩
    wLeftTop := by
      norm_num [W,inside_translate]
      exact fun h => owners_disjoint p hf 7 11 (by decide) _ _
        ⟨h,C1092MMMMWalls.top_origin p hf hb⟩
    wRightBottom := by
      norm_num [W,inside_translate]
      exact fun h => owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,left⟩
    wRightTop := by
      norm_num [W,inside_translate]
      exact fun h => owners_disjoint p hf 7 6 (by decide) _ _ ⟨h,innerY⟩
    apartE := fun x y h => owners_disjoint p hf 6 5 (by decide) _ _
      ⟨(inside_translate _ _ _ _ _).mp h.1,(inside_translate _ _ _ _ _).mp h.2⟩
    apartW := fun x y h => owners_disjoint p hf 6 7 (by decide) _ _
      ⟨(inside_translate _ _ _ _ _).mp h.1,(inside_translate _ _ _ _ _).mp h.2⟩
  exact C1092MMMMEnding.impossible N E W data

/-- Actual canonical Branch2 is PMPM. Reflection of the whole packing in
y=2 gives the all-high MMMM representative used by the continuous ending. -/
theorem adjacentPair : BranchEnding 2 := by
  intro p hf hb
  let g : Transform := ⟨false,false,true⟩
  have action : branchAction g (canonicalBranch 2)=mmmm := by
    funext k; fin_cases k <;> rfl
  have context := context_transport g p hf (canonicalBranch 2) hb
  rw [action] at context
  exact impossible (g.pullPacking p) (family_transport g p hf) context

#print axioms adjacentPair
end N12Compact.C1092MMMM
