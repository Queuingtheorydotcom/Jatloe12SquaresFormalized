import Compact.Completion.FiniteCases.C975Selection
import Compact.Completion.FiniteCases.C975IncomingPair
import Compact.Completion.OtherCases.CrossedElbow

/-! The additional C1090 elbow reduction forces NE F7 in C975. Both
markers used in the quarter-turn application retain actual top34816.
The southeast alternative is split only by its genuine G6 ownership;
the outward branch uses the whole actual bottom8192 bar. The older
incoming theorem then eliminates NE F5/G6 together. These are original
family cuts, not a whole C975 exclusion. Source only, uncompiled. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

/-- The literal outward southeast producer needs no northeast G6
ownership. Its missing G6 is the actual southeast branch assumption. -/
theorem southeast_outward_sharp (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    (owner p 512).Inside (101/40) (17/8) := by
  have h := selection_input p hf
  have point := OutwardBarPoint.point_original (pullY (owner p 512)) (side p 512)
    (by norm_num [inside_pullY]; exact h.markerS)
    (by norm_num [inside_pullY]; exact h.f8)
    (by norm_num [inside_pullY]; exact h.g8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact h.rightMarker)
    (by norm_num [inside_pullY]; exact h.corner)
    (by norm_num [inside_pullY]; exact h.cornerMarker)
    (by
      intro x low high own
      norm_num [inside_pullY] at own
      exact h.bottom x low high own)
  norm_num [inside_pullY] at point
  exact point

/-- The complete quarter-turn elbow sends its outputs to (2.5,2) and
(2.525,2.125) in NE1024. The omitted original NW marker and top marker
both belong to merged34816, which remains foreign to this NE square. -/
theorem northeast_elbow_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (f5 : (owner p 1024).Inside 2 (113/50))
    (missingF7 : ¬(owner p 1024).Inside (12/5) 3) :
    (owner p 1024).Inside (5/2) 2 ∧ (owner p 1024).Inside (101/40) (17/8) := by
  have h := fixed p hf
  have points := ElbowPoint.points_original (pullSwap (pullX (owner p 1024))) (side p 1024)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northeastMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact f5)
    (by norm_num [inside_pullSwap,inside_pullX]; exact (northeast_selection p hf).1)
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 1024 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northwestMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact missingF7)
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 1024 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.topMarker)
  norm_num [inside_pullSwap,inside_pullX] at points
  exact points

theorem northeast_f7_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 1024).Inside (12/5) 3 := by
  by_contra missing
  have h := fixed p hf
  have f5 := (selection_input p hf).fCover.resolve_right missing
  have pair := northeast_elbow_points p hf f5 missing
  by_cases g6 : (owner p 512).Inside (113/50) 2
  · exact CrossedElbow.impossible_original (owner p 512) (4/5) (side p 512)
      (by norm_num) le_rfl h.southeastMarker g6 h.southeastF8
      (foreign p hf 512 1024 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ pair.1)
      (foreign p hf 512 256 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (southwest_south p hf))
      (by
        norm_num
        exact foreign p hf 512 8192 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ (bottom_reach p hf).1)
  · exact apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨southeast_outward_sharp p hf g6,pair.2⟩

theorem northeast_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    7∈auxiliaries p 1024 := by
  apply (auxiliary_exact p 1024 7 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using northeast_f7_point p hf

/-- The former incoming alternative would force G7 into merged34816,
contradicting the strict G7 already established in actual NE1024. -/
theorem not_northeast_incoming (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) :
    ¬(5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024) := by
  intro incoming
  exact not_top_g7 p hf (C975IncomingPair.incoming_forces_top_seven p hf incoming)

structure Cuts (p : NormalizedPacking) : Prop where
  southwestSouth : (owner p 256).Inside 2 (3/2)
  southwestWest : (owner p 256).Inside (3/2) 2
  southeastG8 : 18∈auxiliaries p 512
  northeastG7 : 17∈auxiliaries p 1024
  northeastF7 : 7∈auxiliaries p 1024
  topF3 : 3∈auxiliaries p 34816
  topG4 : 14∈auxiliaries p 34816
  topGExact : natAuxOwners p 1 (ownerIndex p 34816)={4}
  missingTopF5 : 5∉auxiliaries p 34816
  missingTopF7 : 7∉auxiliaries p 34816
  missingTopG6 : 16∉auxiliaries p 34816
  missingNortheastIncoming : ¬(5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024)

/-- The strengthened original entrance, preserving every other allowed
auxiliary ownership and every square orientation. No top origin, exact
central label, or final support inequality is introduced as a premise. -/
theorem cuts (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Cuts p where
  southwestSouth := southwest_south p hf
  southwestWest := southwest_west p hf
  southeastG8 := southeast_g8 p hf
  northeastG7 := northeast_g7 p hf
  northeastF7 := northeast_f7 p hf
  topF3 := C975IncomingCut.top_left p hf
  topG4 := (C975Entrance.compulsory p hf).top
  topGExact := top_g_exact p hf
  missingTopF5 := C975IncomingCut.not_top_inward p hf
  missingTopF7 := not_top_f7 p hf
  missingTopG6 := C975IncomingCut.not_top_elbow p hf
  missingNortheastIncoming := not_northeast_incoming p hf

#print axioms southeast_outward_sharp
#print axioms northeast_f7
#print axioms not_northeast_incoming
#print axioms cuts
end
end N12Compact.FiniteCases.C975Selection
