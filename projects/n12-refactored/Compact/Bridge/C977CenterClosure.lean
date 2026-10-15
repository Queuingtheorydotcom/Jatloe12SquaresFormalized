import Compact.Bridge.C977NegativeBottomNegativeWall
import Compact.Bridge.C977NegativeBottomPositiveWall
import Compact.Bridge.C977SignedEscapeClosure

/-! The complete original C977 ending. The original missing-corner root
first forces center ownership. In that center-owned branch, every
canonical orientation of the actual bottom singleton and next wall is
excluded by their full-square support cycle and the central incoming
supports. No auxiliary-vector selector, reflected root assumption or
saved pose enclosure is added here. Source only, awaiting Lean replay. -/
namespace N12Compact.C977CenterClosure

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

/-- All actual center-owned frames are excluded. The southeast sign is
derived from the genuine paired-corner cap; the central frame is free. -/
theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  by_cases positiveO : 0≤(q 0).s
  · have on : Normal (q 0).c (q 0).s :=
      ⟨positiveO,by simpa only [abs_of_nonneg positiveO] using (canonical 0).2,
        (q 0).unit_normal⟩
    exact C977PositiveBottomWallClosure.bottom_excludes p hf q shape equivalent
      canonical on missingCorner center
  · have negativeO : (q 0).s<0 := lt_of_not_ge positiveO
    have on : Normal (q 0).c (-(q 0).s) :=
      ⟨by linarith only [negativeO],
        by simpa only [abs_of_neg negativeO] using (canonical 0).2,
        by nlinarith only [(q 0).unit_normal]⟩
    have cap := C977SignedCentralCorner.frame_cap p hf q shape equivalent canonical
      missingCorner center
    have bn : Normal (q 6).c (-(q 6).s) :=
      ⟨by linarith only [cap.1],
        by simpa only [abs_of_neg cap.1] using (canonical 6).2,
        by nlinarith only [(q 6).unit_normal]⟩
    by_cases positiveD : 0≤(q 9).s
    · have dn : Normal (q 9).c (q 9).s :=
        ⟨positiveD,by simpa only [abs_of_nonneg positiveD] using (canonical 9).2,
          (q 9).unit_normal⟩
      exact C977NegativeBottomPositiveWall.frame_excludes p hf q shape equivalent
        canonical (-(q 0).s) (-(q 6).s) (by ring) on dn (by ring) bn missingCorner center
    · have negativeD : (q 9).s<0 := lt_of_not_ge positiveD
      have dn : Normal (q 9).c (-(q 9).s) :=
        ⟨by linarith only [negativeD],
          by simpa only [abs_of_neg negativeD] using (canonical 9).2,
          by nlinarith only [(q 9).unit_normal]⟩
      exact C977NegativeBottomNegativeWall.frame_excludes p hf q shape equivalent
        canonical (-(q 0).s) (-(q 9).s) (-(q 6).s)
        (by ring) on (by ring) dn (by ring) bn missingCorner center

/-- Canonical frames are chosen for the actual squares, with their full
interiors preserved. No global geometric reflection changes the root. -/
theorem center_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  classical
  choose q positive canonical shape equivalent closed using
    (fun i : Fin 12 => ClosedFrames.canonical_frame (p.square (orderedOwner p i)))
  exact frame_excludes p hf q shape equivalent
    (fun i => ⟨positive i,canonical i⟩) missingCorner center

/-- The unchanged original case contract, including its complete
missing-corner cover and both center alternatives. -/
theorem excludes : ExcludesCase 977 := by
  apply C977SignedEscapeClosure.excludes_case_of_center_ending
  intro p hf missing bounds w walls vector center
  exact center_excludes p hf missing.entrance.corner_missing center

#print axioms frame_excludes
#print axioms center_excludes
#print axioms excludes
end N12Compact.C977CenterClosure
