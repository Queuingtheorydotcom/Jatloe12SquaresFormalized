import Compact.Completion.FiniteCases.C975SelectionSeeds
import Compact.Completion.OtherCases.C1090.NESelection

/-! The raw C1090 northeast selection applies to C975 without creating
a separate northwest square. Its foreign northwest marker and its top
marker both retain the actual merged owner34816. The exact top G set is
then reduced using the existing complete C975 top domain. Source only;
no finite domain generation, compilation, or whole-case claim occurs. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem selection_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    N12Compact.Completion.OtherCases.C1090.NESelection.Input
      (owner p 512) (owner p 1024) := by
  have h := fixed p hf
  have compulsory := C975Entrance.compulsory p hf
  exact {
    sideS := side p 512
    sideE := side p 1024
    apart := apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    markerS := h.southeastMarker
    f8 := h.southeastF8
    g8 := southeast_g8_point p hf
    corner := foreign p hf 512 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.southeastCorner
    cornerMarker := foreign p hf 512 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.southeastCornerRight
    rightMarker := foreign p hf 512 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.rightMarker
    bottom := fun x low high => foreign p hf 512 8192 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ ((bottom_reach p hf).2 x low high)
    markerE := h.northeastMarker
    northwest := foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.northwestMarker
    f9 := foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.rightF9
    g9 := foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.rightG9
    fCover := by
      rcases compulsory.northeast.1 with f5 | f7
      · left
        simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 5 (by norm_num) f5
      · right
        simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 7 (by norm_num) f7
    gCover := by
      rcases compulsory.northeast.2 with g6 | g7
      · left
        simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 16 (by norm_num) g6
      · right
        simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 17 (by norm_num) g7 }

theorem northeast_selection (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 1024).Inside (113/50) 3 ∧
      ((owner p 1024).Inside (113/50) 2 → (owner p 1024).Inside (12/5) 3) :=
  N12Compact.Completion.OtherCases.C1090.NESelection.selection
    (owner p 512) (owner p 1024) (selection_input p hf)

theorem northeast_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    17∈auxiliaries p 1024 := by
  apply (auxiliary_exact p 1024 17 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using (northeast_selection p hf).1

theorem northeast_g6_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g6 : 16∈auxiliaries p 1024) : 7∈auxiliaries p 1024 := by
  have own : (owner p 1024).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 16 (by norm_num) g6
  apply (auxiliary_exact p 1024 7 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using (northeast_selection p hf).2 own

theorem not_top_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    17∉auxiliaries p 34816 := by
  intro own
  exact Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 34816 1024
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) own (northeast_g7 p hf)

private theorem g_combined (p : NormalizedPacking) (mask j : Nat) :
    j∈natAuxOwners p 1 (ownerIndex p mask) ↔ j+10∈auxiliaries p mask := by
  unfold auxiliaries natCombinedOwners
  simpa only [Nat.add_sub_cancel] using
    (mem_combined_high _ _ (nat_aux_subset p 0 _) (j+10) (by omega)).symm

/-- This is the complete G set of the actual merged top, using the
authentic top_g_options list and the new actual foreign G7. -/
theorem top_g_exact (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    natAuxOwners p 1 (ownerIndex p 34816)={4} := by
  rcases C975IncomingCut.top_g_options p hf with single | double
  · exact single
  · exfalso
    apply not_top_g7 p hf
    apply (g_combined p 34816 7).mp
    rw [double]
    decide +kernel

/-- If this same top owned F7, its strict segment from G4 to F7 would
contain G7. The NE owner's strict G7 excludes that whole alternative. -/
theorem not_top_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    7∉auxiliaries p 34816 := by
  intro own
  have low : (owner p 34816).Inside (87/50) 3 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_point p 34816 14 (by norm_num) (C975Entrance.compulsory p hf).top
  have high : (owner p 34816).Inside (12/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 34816 7 (by norm_num) own
  have mid : (owner p 34816).Inside (113/50) 3 :=
    horizontal_segment (owner p 34816) (87/50) (12/5) 3 (113/50)
      low high (by norm_num) (by norm_num) (by norm_num)
  exact apart _ p hf 34816 1024 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨mid,(northeast_selection p hf).1⟩

#print axioms selection_input
#print axioms northeast_selection
#print axioms top_g_exact
#print axioms not_top_f7
end
end N12Compact.FiniteCases.C975Selection
