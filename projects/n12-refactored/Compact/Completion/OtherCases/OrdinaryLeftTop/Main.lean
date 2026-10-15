import Compact.Completion.OtherCases.OrdinaryLeftTop.Negative
import Compact.Completion.OtherCases.OrdinaryLeftTop.Positive

/-! The all-angle conclusion of ORDINARY-LEFT-TOP-OBSTRUCTION.md Theorem 1,
and the origin corollary in C1089-LAST-SECTOR-ENDING.md section 4.
The finite source hypotheses are literal point hypotheses on one physical
square. These source proofs have not been submitted to the compiler. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop
open S12 S12Pilot
set_option Elab.async false

theorem frame (q : OpenSquare) (h : Input q) :
    ∃ r : OpenSquare, r.side=q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧ Profile r ∧
      r.Inside (7/25) 1 ∧ r.Inside (2/5) 1 := by
  obtain ⟨r,cp,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side inside
  by_cases sign : 0 ≤ r.s
  · have order : r.s ≤ r.c := by
      simpa only [abs_of_nonneg sign] using range
    have profile := positive_profile r data cp sign order
    have points := upper_points r data profile
    exact ⟨r,side,inside,profile,points.1,points.2⟩
  · have negative : r.s < 0 := lt_of_not_ge sign
    have order : -r.s ≤ r.c := by
      simpa only [abs_of_neg negative] using range
    exact False.elim (nonpositive_impossible r data (-r.s) (by ring) cp
      (by linarith only [negative]) order)

/-- In the frame supplied by the completed point theorem, both weak upper
face caps are strictly below one. The strict anchor supplies the two upper
bands at the origin, including every possible face contact. -/
theorem origin_of_profile (q : OpenSquare) (h : Input q) (p : Profile q) :
    q.Inside 0 0 := by
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s p.cosine p.sine.le
    p.canonical q.unit_normal
  have projection := ScalarMargins.originUpper q.c q.s p.cosine p.sine.le
    p.canonical q.unit_normal p.angleUpper.le
  have lowerU : q.loU < 0 := by
    linarith only [p.upperU,h.side,projection]
  have lowerV : q.loV < 0 := by
    linarith only [p.upperV,h.side,bounds.2.1]
  have upperU : 0 < q.loU+q.side := by
    linarith only [h.anchor.2.1,p.sine]
  have upperV : 0 < q.loV+q.side := by
    linarith only [h.anchor.2.2.2,p.cosine]
  simpa only [OpenSquare.Inside,InBands,mul_zero,zero_add] using
    And.intro lowerU (And.intro upperU (And.intro lowerV upperV))

theorem origin (q : OpenSquare) (h : Input q) : q.Inside 0 0 := by
  obtain ⟨r,side,inside,p,_,_⟩ := frame q h
  exact (inside _ _).mp (origin_of_profile r (h.reframe side inside) p)

theorem impossible_with_missing_origin (q : OpenSquare) (h : Input q)
    (missing : ¬ q.Inside 0 0) : False := missing (origin q h)

#print axioms frame
#print axioms origin
end N12Compact.Completion.OtherCases.OrdinaryLeftTop
