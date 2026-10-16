import Compact.Completion.OtherCases.C983.ActualBars
import Compact.Completion.OtherCases.C983.InwardOutwardPair

/-! Literal local ownership implications for the C983 F4 entrance.
Every deletion uses an actual foreign owner or the exact omitted auxiliary
of its own square; no complete ownership-vector catalogue is assumed. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem absent_of_foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (point : Nat) (different : i ≠ j) (member : point∈actual p i) :
    point∉actual p j :=
  fun h => Finset.disjoint_left.mp (actual_disjoint p hf i j different) member h

theorem point_exact (p : NormalizedPacking) (i : Fin 12) (point : Nat) (bound : point < 20) :
    (owners p i).Inside ((auxPoints 2)[point]!).1 ((auxPoints 2)[point]!).2 ↔
      point∈actual p i :=
  nat_combined_exact p (ownerIndex p (ownerCode i)) point
    (by change point∈List.range 20; exact List.mem_range.mpr bound)

private theorem merged_check : ∀ owned∈originalComponents 7,13∈owned := by decide +kernel

theorem merged_g3 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    13∈actual p 7 := merged_check _ (original_actual_mem p hf 7)

private theorem southeast_f4_check :
    ∀ owned∈originalComponents 5,4∉owned → 8∈owned := by decide +kernel

theorem f4_southeast (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 8∈actual p 5 :=
  southeast_f4_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 7 5 4 (by decide +kernel) f4)

private theorem right_from_f8_check :
    ∀ owned∈originalComponents 10,8∉owned → 9∈owned ∧ 19∈owned := by decide +kernel

theorem f4_right (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 9∈actual p 10 ∧ 19∈actual p 10 :=
  right_from_f8_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 8 (by decide +kernel) (f4_southeast p hf f4))

private theorem northeast_f4_check :
    ∀ owned∈originalComponents 6,
      4∉owned → 8∉owned → 9∉owned → 13∉owned → 19∉owned →
        (5∈owned ∨ 7∈owned) ∧ (16∈owned ∨ 17∈owned) := by decide +kernel

theorem f4_northeast (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) :
    (5∈actual p 6 ∨ 7∈actual p 6) ∧ (16∈actual p 6 ∨ 17∈actual p 6) := by
  have r := f4_right p hf f4
  exact northeast_f4_check _ (original_actual_mem p hf 6)
    (absent_of_foreign p hf 7 6 4 (by decide +kernel) f4)
    (absent_of_foreign p hf 5 6 8 (by decide +kernel) (f4_southeast p hf f4))
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) r.1)
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) r.2)

private theorem southeast_outward_check :
    ∀ owned∈originalComponents 5,
      4∉owned → 9∉owned → 5∉owned → 16∉owned → 8∈owned → owned={8,18} := by decide +kernel

theorem f4_inward_forces_outward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (f5 : 5∈actual p 6) (g6 : 16∈actual p 6) :
    actual p 5={8,18} := by
  exact southeast_outward_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 7 5 4 (by decide +kernel) f4)
    (absent_of_foreign p hf 10 5 9 (by decide +kernel) (f4_right p hf f4).1)
    (absent_of_foreign p hf 6 5 5 (by decide +kernel) f5)
    (absent_of_foreign p hf 6 5 16 (by decide +kernel) g6)
    (f4_southeast p hf f4)

/-- Complete original-owner duplicate obstruction of central reduction
Section2(5), using the already proved actual bottom bar. -/
theorem f4_inward_outward_exclusion (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (f5 : 5∈actual p 6) (g6 : 16∈actual p 6)
    (missingF7 : 7∉actual p 6) : False := by
  have outward := f4_inward_forces_outward p hf f4 f5 g6
  have nMarker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have nInward : (owners p 6).Inside 2 (113/50) := by
    have h := auxiliary_inside p 6 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have nElbow : (owners p 6).Inside (113/50) 2 := by
    have h := auxiliary_inside p 6 16 (by decide +kernel) g6
    simpa [auxPoints,fPoints,gPoints] using h
  have nMissingTop : ¬(owners p 6).Inside (12/5) 3 := by
    have pointEquiv := point_exact p 6 7 (by decide +kernel)
    simpa [auxPoints,fPoints,gPoints] using (fun h => missingF7 (pointEquiv.mp h))
  have eMarker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have eOutward : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) (by rw [outward]; decide +kernel)
    simpa [auxPoints,fPoints,gPoints] using h
  have eUpper : (owners p 5).Inside 3 (8/5) := by
    have h := auxiliary_inside p 5 18 (by decide +kernel) (by rw [outward]; decide +kernel)
    simpa [auxPoints,fPoints,gPoints] using h
  have wMarker : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have rMarker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have cCorner : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h; exact h
  have cMarker : (owners p 2).Inside (1543/500) 1 := by
    have h := seed_inside p hf 2 (1543/500,1) (by decide +kernel)
    norm_num at h; exact h
  exact inward_outward_impossible (owners p 6) (owners p 5) (owners p 9) (owners p 2)
    (owners p 10) (owners p 7) (owners_side p 6) (owners_same_side p 6 5)
    nMarker nInward nElbow nMissingTop eMarker eOutward eUpper wMarker rMarker cCorner cMarker
    (bottom_bar p hf)
    (owners_apart p hf 6 5 (by decide +kernel))
    (owners_apart p hf 6 7 (by decide +kernel))
    (owners_apart p hf 5 10 (by decide +kernel))
    (owners_apart p hf 5 2 (by decide +kernel))
    (owners_apart p hf 5 9 (by decide +kernel))

private theorem top_f7_check : ∀ owned∈originalComponents 11,7∈owned → 17∈owned := by decide +kernel

theorem f4_top_avoids_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 7∉actual p 11 := by
  intro topF7
  have topG7 := top_f7_check _ (original_actual_mem p hf 11) topF7
  have noF7 := absent_of_foreign p hf 11 6 7 (by decide +kernel) topF7
  have noG7 := absent_of_foreign p hf 11 6 17 (by decide +kernel) topG7
  have cover := f4_northeast p hf f4
  have f5 := cover.1.resolve_right noF7
  have g6 := cover.2.resolve_right noG7
  exact f4_inward_outward_exclusion p hf f4 f5 g6 noF7

private theorem top_f4_check :
    ∀ owned∈originalComponents 11,7∉owned → 3∈owned ∧ 14∈owned := by decide +kernel

theorem f4_top (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 3∈actual p 11 ∧ 14∈actual p 11 :=
  top_f4_check _ (original_actual_mem p hf 11) (f4_top_avoids_f7 p hf f4)

end
#print axioms f4_top
end N12Compact.Completion.OtherCases.C983

