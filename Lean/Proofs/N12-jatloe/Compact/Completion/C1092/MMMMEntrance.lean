import Compact.Bridge.C1092AuxiliaryCover
import Compact.Completion.C1092.ActualEntrance
import Compact.Completion.C1092.MixedSpan
import Compact.Completion.C1092.CornerTwoGaps

/-! The actual MMMM compulsory auxiliary pairs, without enumerating joint
ownership tuples. The northeast inward pair follows directly from the
physical incoming walls; component covers retain every extra ownership. -/
namespace N12Compact.C1092MMMMEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092ActualEntrance C1092AuxiliaryCover
set_option Elab.async false

def mmmm : WallBranch := ![false,false,false,false]

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem southeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 2 (87/50) ∨
      (owners p 5).Inside (12/5) 1 ∨ (owners p 5).Inside 3 (87/50) := by
  have h := central_cover_transported ⟨true,true,false⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem southwest_high_wall_points (p : NormalizedPacking) (hb : WallContext p mmmm) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 9).Inside (113/50) 1 := by
  constructor
  · have h := wall_auxiliary_point p mmmm hb 0
    norm_num [mmmm,wallOwner,pointMap,branchY] at h
    exact h
  · have h := wall_auxiliary_point p mmmm hb 1
    norm_num [mmmm,wallOwner,pointMap,branchY] at h
    exact h

theorem southeast_g (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 5).Inside 3 (8/5) := by
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have bottom := (southwest_high_wall_points p hb).2
  rcases southeast_g_cover p hf with h | h | h
  · exact False.elim (owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom⟩)
  · exact False.elim (owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,inward.2⟩)
  · exact h

theorem northwest_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 7).Inside (8/5) 3 := by
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have left := (southwest_high_wall_points p hb).1
  rcases northwest_f_cover p hf with h | h | h
  · exact False.elim (owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,left⟩)
  · exact h
  · exact False.elim (owners_disjoint p hf 7 6 (by decide) _ _ ⟨h,inward.1⟩)

theorem right_g (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 10).Inside 3 (12/5) := by
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have below := southeast_g p hf hb
  rcases right_g_cover p hf with h | h | h
  · exact False.elim (owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,inward.2⟩)
  · exact False.elim (owners_disjoint p hf 10 5 (by decide) _ _ ⟨h,below⟩)
  · exact h

theorem top_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 11).Inside (12/5) 3 := by
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have beside := northwest_f p hf hb
  rcases top_f_cover p hf with h | h | h
  · exact False.elim (owners_disjoint p hf 11 7 (by decide) _ _ ⟨h,beside⟩)
  · exact False.elim (owners_disjoint p hf 11 6 (by decide) _ _ ⟨h,inward.1⟩)
  · exact h

theorem southeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) :
    (owners p 5).Inside 3 (87/50) ∧ (owners p 5).Inside 3 (8/5) := by
  classical
  have g := southeast_g p hf hb
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have bottom := (southwest_high_wall_points p hb).2
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have bottomTip : (owners p 9).Inside (239/100) 1 := by
    have h := local_wall_segment p mmmm hb 1 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmm,wallOwner,pointMap,branchY] at h
    exact h
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h : Owns (owners p 5) 9 := (owners_markers p hf 5 9).mpr (by decide +kernel)
    simpa [Owns,marker] using h
  have f : (owners p 5).Inside 3 (87/50) := by
    by_contra absent
    have noOuter : ¬ (owners p 5).Inside (12/5) 1 := by
      intro outer
      apply C1092CornerTwoGaps.impossible (pullY (owners p 5)) (side_gt p 5)
        (39/100) (13/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · norm_num [inside_pullY]
        exact marker
      · norm_num [inside_pullY]
        exact outer
      · norm_num [inside_pullY]
        exact g
      · norm_num [inside_pullY]
        intro h
        exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottomTip⟩
      · norm_num [inside_pullY]
        exact absent
      · norm_num [inside_pullY]
        intro h
        exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨h,corner⟩
    rcases southeast_f_cover p hf with h | h | h
    · exact C1092MixedSpan.impossible (owners p 5) (side_gt p 5) h g
        (fun h => owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,inward.2⟩) absent
        (fun h => owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom⟩) noOuter
    · exact noOuter h
    · exact absent h
  exact ⟨f,g⟩

theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) :
    (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3 := by
  let g : Transform := ⟨true,false,false⟩
  have action : branchAction g mmmm=mmmm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mmmm hb
  rw [action] at context
  have h := southeast_pair (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 5] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap] at h
  exact ⟨h.2,h.1⟩

#print axioms southeast_pair
#print axioms northwest_pair
end N12Compact.C1092MMMMEntrance
