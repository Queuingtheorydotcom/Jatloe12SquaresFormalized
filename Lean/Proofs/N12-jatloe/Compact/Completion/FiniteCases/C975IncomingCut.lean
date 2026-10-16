import Compact.Completion.FiniteCases.C975Entrance
import Compact.Completion.FiniteCases.TopMergedInward
import Compact.Completion.FiniteCases.TopPairPoint
import Compact.Completion.C981.Crosspoint

/-! Genuine C975 reductions after the complete original entrance. The
merged top's F5 alternative is excluded in every orientation. Its F7
alternative forces the NE owner's actual incoming pair; F3 remains live. -/
namespace N12Compact.FiniteCases.C975IncomingCut
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

private theorem aux_inside (p : NormalizedPacking) (mask index : Nat)
    (bound : index<20) (own : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr own

private theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun h => apart _ p hf m n hm hn different x y ⟨h,own⟩

private theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed _ p hf mask member P checked

theorem not_top_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    5∉auxiliaries p 34816 := by
  intro owned
  have points := compulsory p hf
  have no5 : 5∉auxiliaries p 1024 := fun own =>
    Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 1024 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) own owned
  have outward := points.northeast.1.resolve_left no5
  have hTop : (owner p 34816).Inside 2 (1543/500) := by
    have h := seed_point p hf 34816 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have hInward : (owner p 34816).Inside 2 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 34816 5 (by norm_num) owned
  have nMarker : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have nOutward : (owner p 1024).Inside (12/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 7 (by norm_num) outward
  have nOptions : (owner p 1024).Inside (113/50) 2 ∨
      (owner p 1024).Inside (113/50) 3 := by
    rcases points.northeast.2 with inward | high
    · left
      simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 16 (by norm_num) inward
    · right
      simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 17 (by norm_num) high
  have corner : (owner p 48).Inside 3 3 := by
    have h := seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
    norm_num at h; exact h
  have rMarker : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have rHigh : (owner p 16384).Inside 3 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p 16384 19 (by norm_num) points.rightWall.2
  have seOutward : (owner p 512).Inside 3 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p 512 8 (by norm_num) points.southeast.1
  exact TopMergedInward.short_impossible (owner p 34816) (owner p 1024) (owner p 16384)
    (side p 1024) (side p 16384) (box p 16384) hTop hInward nMarker nOutward nOptions
    (foreign p hf 1024 48 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ corner) rMarker rHigh
    (foreign p hf 16384 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ seOutward)
    (apart _ p hf 34816 1024 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (apart _ p hf 1024 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem remaining_top (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    3∈auxiliaries p 34816 ∨ 7∈auxiliaries p 34816 := by
  rcases top_alternatives p hf with three | five | seven
  · exact Or.inl three
  · exact False.elim (not_top_inward p hf five)
  · exact Or.inr seven

/-- F7 spans the actual top G4-to-F7 segment, so its interior G7 belongs
to this same merged owner and is foreign to the NE owner. -/
theorem top_seven_incoming (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (seven : 7∈auxiliaries p 34816) :
    5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024 := by
  have points := compulsory p hf
  have no7 : 7∉auxiliaries p 1024 := fun own =>
    Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 1024 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) own seven
  have low : (owner p 34816).Inside (87/50) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 34816 14 (by norm_num) points.top
  have high : (owner p 34816).Inside (12/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 34816 7 (by norm_num) seven
  have mid : (owner p 34816).Inside (113/50) 3 :=
    horizontal_segment _ _ _ _ _ low high (by norm_num) (by norm_num) (by norm_num)
  have seventeen : 17∈auxiliaries p 34816 := by
    apply (auxiliary_exact p 34816 17 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using mid
  have no17 : 17∉auxiliaries p 1024 := fun own =>
    Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 1024 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) own seventeen
  exact ⟨points.northeast.1.resolve_right no7,points.northeast.2.resolve_right no17⟩

theorem right_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 16384).Inside 3 (64/25) := by
  have points := compulsory p hf
  have mark : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have high : (owner p 16384).Inside 3 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 16384 19 (by norm_num) points.rightWall.2
  have low : (owner p 512).Inside 3 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 512 8 (by norm_num) points.southeast.1
  have ne : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have h := WallHighFromMarker.point (pullX (owner p 16384)) (side p 16384)
    (container_pullX _ (box p 16384))
    (by norm_num [inside_pullX]; exact mark)
    (by norm_num [inside_pullX]; exact high)
    (by norm_num [inside_pullX]; exact (foreign p hf 16384 512 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ low))
    (by norm_num [inside_pullX]; exact (foreign p hf 16384 1024 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ ne))
  norm_num [inside_pullX] at h; exact h

theorem incoming_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (incoming : 5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024) :
    (owner p 1024).Inside 2 (5/2) := by
  have points := compulsory p hf
  have north : (owner p 1024).Inside 2 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 5 (by norm_num) incoming.1
  have east : (owner p 1024).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 16 (by norm_num) incoming.2
  have ne : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have se : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have nw : (owner p 34816).Inside (33/20) (47/20) := by
    have h := seed_point p hf 34816 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have right : (owner p 16384).Inside 3 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 16384 19 (by norm_num) points.rightWall.2
  have rightMid : (owner p 16384).Inside 3 (5/2) :=
    vertical_segment _ _ _ _ _ right (right_high p hf)
      (by norm_num) (by norm_num) (by norm_num)
  exact C981CompletionCrosspoint.point _ (side p 1024) north east ne
    (foreign p hf 1024 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ se)
    (foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ nw)
    (foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ right)
    (foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ rightMid)

/-- F7 is retained through the full budget and then forces F3 geometrically.
This is a compulsory point reduction, not an exclusion of the whole case. -/
theorem top_left (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    3∈auxiliaries p 34816 := by
  rcases remaining_top p hf with three | seven
  · exact three
  · have nw : (owner p 34816).Inside (33/20) (47/20) := by
      have h := seed_point p hf 34816 (by decide +kernel) (33/20,47/20) (by decide +kernel)
      norm_num at h; exact h
    have high : (owner p 34816).Inside (12/5) 3 := by
      simpa [auxPoints,fPoints,gPoints] using aux_inside p 34816 7 (by norm_num) seven
    have ne : (owner p 1024).Inside (47/20) (47/20) := by
      have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
      norm_num at h; exact h
    have forced := TopPairPoint.point (owner p 34816) (side p 34816) nw high
      (foreign p hf 34816 1024 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ne)
      (foreign p hf 34816 1024 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (incoming_high p hf (top_seven_incoming p hf seven)))
    apply (auxiliary_exact p 34816 3 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using forced

/-- The inward G elbow would force the already excluded F5 inside one
actual-owner triangle. No further angle or label assumption is used. -/
theorem not_top_elbow (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    16∉auxiliaries p 34816 := by
  intro owned
  have nw : (owner p 34816).Inside (33/20) (47/20) := by
    have h := seed_point p hf 34816 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have high : (owner p 34816).Inside 2 (1543/500) := by
    have h := seed_point p hf 34816 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have elbow : (owner p 34816).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 34816 16 (by norm_num) owned
  let triangle : TriangleCertificate :=
    ⟨(33/20,47/20),(2,1543/500),(113/50,2),(2,113/50),1690/7059,14455/28573⟩
  have checked : triangle.Check := by decide +kernel
  have inward := triangle_certificate_sound triangle checked (owner p 34816)
    (by norm_num [triangle]; exact nw)
    (by norm_num [triangle]; exact high)
    (by norm_num [triangle]; exact elbow)
  apply not_top_inward p hf
  apply (auxiliary_exact p 34816 5 (by norm_num)).mp
  norm_num [triangle] at inward
  simpa [auxPoints,fPoints,gPoints] using inward

private theorem g_combined (p : NormalizedPacking) (mask j : Nat) :
    j∈natAuxOwners p 1 (ownerIndex p mask) ↔ j+10∈auxiliaries p mask := by
  unfold auxiliaries natCombinedOwners
  simpa only [Nat.add_sub_cancel] using
    (mem_combined_high _ _ (nat_aux_subset p 0 _) (j+10) (by omega)).symm

private theorem top_g_checked : ∀ s∈topGAllowed,
    1∉s → 3∉s → 6∉s → s={4} ∨ s={4,7} := by decide +kernel

/-- Complete G sets of the actual merged owner. Its extra upper endpoint
remains a live original ownership alternative. -/
theorem top_g_options (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    natAuxOwners p 1 (ownerIndex p 34816)={4} ∨
      natAuxOwners p 1 (ownerIndex p 34816)={4,7} := by
  have points := compulsory p hf
  have excluded (m index : Nat) (hm : m∈family) (different : 34816≠m)
      (point : index∈auxiliaries p m) : index∉auxiliaries p 34816 :=
    fun own => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 34816 m
      (by decide +kernel) hm different) own point
  apply top_g_checked _ (C975Domains.topG.sound p _ hf
    (code _ p hf 34816 (by decide +kernel)))
  · intro own
    exact excluded 4096 11 (by decide +kernel) (by decide +kernel) points.leftWall.2
      ((g_combined p 34816 1).mp own)
  · intro own
    exact excluded 256 13 (by decide +kernel) (by decide +kernel) points.southwestCentral.2
      ((g_combined p 34816 3).mp own)
  · intro own
    exact not_top_elbow p hf ((g_combined p 34816 6).mp own)

#print axioms not_top_inward
#print axioms remaining_top
#print axioms top_seven_incoming
#print axioms top_left
#print axioms not_top_elbow
#print axioms top_g_options
end
end N12Compact.FiniteCases.C975IncomingCut
