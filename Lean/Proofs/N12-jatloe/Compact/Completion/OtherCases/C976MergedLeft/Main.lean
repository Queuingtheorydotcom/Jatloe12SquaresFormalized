import Compact.Completion.OtherCases.C976MergedLeft.LowerFaces

/-! C976-MERGED-LEFT-ENDING Theorem 1. No container wall or upper side
bound is assumed. Canonical reframing preserves the original physical
square and every strict anchor / weak excluded segment. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open S12 S12Pilot
set_option Elab.async false

theorem positive_point (q : OpenSquare) (h : Input q) (p : Profile q) :
    q.Inside (27/100) (-(1/25)) := by
  have large := half_large q h p
  have span := target_span q.c q.s p.cosine p.sine.le q.unit_normal large.le
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [h.left.1,h.left.2.2.2,h.marker.2.1,p.cosine,p.sine,
      p.canonical,p.upperV,h.side,span]

theorem point (q : OpenSquare) (h : Input q) : q.Inside (27/100) (-(1/25)) := by
  obtain ⟨r,cp,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side inside
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using range
    exact (inside _ _).mp (positive_point r data (positive_profile r data cp sign order))
  · by_contra missing
    have missing' : ¬r.Inside (27/100) (-(1/25)) := fun own => missing ((inside _ _).mp own)
    exact C976LeftTop.UpperPoints.nonpositive_impossible r (data.with_missing_target missing')
      (-r.s) (by ring) cp (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

#print axioms point
end N12Compact.Completion.OtherCases.C976MergedLeft
