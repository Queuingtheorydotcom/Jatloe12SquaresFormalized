import Compact.Completion.C1092.MPPMUpperSign
import Compact.Completion.C1092.MMMP.RightInnerPositive

/-! The genuine top owner excludes the right inward auxiliary in the
transposed MPPM one-omission chart. The original left pair and the original
northwest covering rows supply every point of the two-square obstruction. -/
namespace N12Compact.C1092MPPMRightInner
open S12 S12Pilot C1092WallCycle C1092AuxiliaryCover C1092MPPMEntrance
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

theorem other_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 8).Inside 1 (12/5) ∧ (owners p 11).Inside (12/5) 3 := by
  classical
  have exclusion (k : Fin 4) (different : k≠1) : ¬C1092MPPMOmissions.Missing p k := by
    intro absent
    exact different (C1092MPPMOmissions.at_most_one p hf hb k 1 absent omitted)
  have first : (owners p 8).Inside 1 (12/5) := not_not.mp (exclusion 0 (by decide))
  have last : (owners p 11).Inside (12/5) 3 := not_not.mp (exclusion 3 (by decide))
  exact ⟨first,last⟩

private theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (inward : (owners p 11).Inside 2 (113/50)) :
    (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3 := by
  classical
  have leftF := (wall_auxiliaries p hb).1
  have leftG := (other_ordinary p hf hb omitted).1
  have ordinaryF : (owners p 7).Inside (8/5) 3 := by
    rcases northwest_f_cover p hf with h|h|h
    · exact False.elim (owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,leftF⟩)
    · exact h
    · exact False.elim (owners_disjoint p hf 7 11 (by decide) _ _ ⟨h,inward⟩)
  have ordinaryG : (owners p 7).Inside (87/50) 3 := by
    by_contra absent
    have inner : (owners p 7).Inside (87/50) 2 := by
      rcases northwest_g_cover p hf with h|h|h
      · exact False.elim (owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,leftG⟩)
      · exact h
      · exact False.elim (absent h)
    exact C1092MixedSpan.impossible (pullSwap (owners p 7)) (side_gt p 7)
      (by norm_num [inside_pullSwap]; exact inner)
      (by norm_num [inside_pullSwap]; exact ordinaryF)
      (by
        norm_num [inside_pullSwap]
        exact fun own => owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,inward⟩)
      (by norm_num [inside_pullSwap]; exact absent)
      (by
        norm_num [inside_pullSwap]
        exact fun own => owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,leftF⟩)
      (by
        norm_num [inside_pullSwap]
        exact fun own => owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,leftG⟩)
  exact ⟨ordinaryF,ordinaryG⟩

theorem missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    ¬(owners p 11).Inside 2 (113/50) := by
  intro inward
  obtain ⟨N,hN⟩ := C1092MPPMUpperSign.exists_positive p hf hb omitted
  let R := C1092RigidCharts.translate (pullSwap (owners p 11)) 2 2
  have actual (x y : ℝ) : R.Inside x y ↔ (owners p 11).Inside (2+y) (2+x) := by
    dsimp only [R]
    rw [C1092RigidCharts.inside_translate,inside_pullSwap]
    rw [show y+2=2+y by ring,show x+2=2+x by ring]
  have pair := northwest_pair p hf hb omitted inward
  have ne := (omitted_bottom_neighbors p hf hb omitted).1
  have mark : (owners p 6).Inside (47/20) (47/20) := by
    have own : Owns (owners p 6) 10 := (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  have wallMark : (owners p 11).Inside 2 (1543/500) := by
    have own : Owns (owners p 11) 15 := (owners_markers p hf 11 15).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  exact C1092MMMPRightInnerPositive.impossible N R
    (by rw [hN.side]; exact side_gt p 6)
    (hN.side.trans (side_same p 6 11)) hN.normal
    (by apply (hN.actual _ _).mpr; norm_num; exact mark)
    (by apply (hN.actual _ _).mpr; norm_num; exact ne.1)
    (by apply (hN.actual _ _).mpr; norm_num; exact ne.2)
    (by apply (actual _ _).mpr; norm_num; exact inward)
    (by apply (actual _ _).mpr; norm_num; exact wallMark)
    (by apply (actual _ _).mpr; norm_num; exact (other_ordinary p hf hb omitted).2)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 11 7 (by decide) _ _ ⟨own',pair.2⟩)
    (fun x y own => owners_disjoint p hf 6 11 (by decide) _ _
      ⟨(hN.actual _ _).mp own.1,(actual _ _).mp own.2⟩)

#print axioms missing
end N12Compact.C1092MPPMRightInner
