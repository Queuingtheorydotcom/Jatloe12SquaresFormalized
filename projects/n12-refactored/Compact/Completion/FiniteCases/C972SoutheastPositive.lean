import Compact.Completion.FiniteCases.C972SoutheastSupport
import Compact.Completion.FiniteCases.C972SoutheastNegativeHalfpoint
import Compact.Completion.FiniteCases.C972SoutheastSeparation
import Compact.Completion.OtherCases.C983.F4SoutheastSign

/-! The actual C972 missing-SE-halfpoint branch has a strictly positive
SE canonical frame.  The zero and negative frames are excluded by the
same actual right origin and the two distinct southwest points.  The
subsequent SAT reduction keeps SW and SE as their original physical
owners, with no assumed center or desired support bound. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
open ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

/-- Every canonical representation of the same SE square in the common
chart (x-2,y-2) has positive sine if the original lower halfpoint is absent. -/
theorem southeast_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 6).Inside 3 (3/2)) (E : OpenSquare)
    (shape : E.side=(owners p 6).side)
    (actual : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (cp : 0<E.c) (canonical : |E.s|≤E.c) : 0<E.s := by
  apply lt_of_not_ge
  intro sign
  have en : Normal E.c (-E.s) := ⟨by linarith only [sign],
    by simpa only [abs_of_nonpos sign] using canonical,by nlinarith only [E.unit_normal]⟩
  have point := C972Local.negative_point E (-E.s) (by ring) en
    (by rw [shape]; exact side p 6)
    (by apply (actual _ _).mpr; norm_num; exact southeast_g6_of_missing_halfpoint p hf missing)
    (by apply (actual _ _).mpr; norm_num; exact (fixed p hf).southeastF8)
    (by apply (actual _ _).mpr; norm_num; exact southeast_g8 p hf)
    (by
      intro own
      apply foreign p hf 6 11 (by decide) _ _ (right_origin p hf)
      convert (actual _ _).mp own using 1 <;> norm_num)
    (by
      intro own
      apply foreign p hf 6 5 (by decide) _ _ (fixed p hf).southwestF4
      convert (actual _ _).mp own using 1 <;> norm_num)
    (by
      intro own
      apply foreign p hf 6 5 (by decide) _ _ (southwest_south p hf)
      convert (actual _ _).mp own using 1 <;> norm_num)
  apply missing
  convert (actual _ _).mp point using 1 <;> norm_num

theorem exists_positive_southeast (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2)) :
    ∃ E : OpenSquare,E.side=(owners p 6).side ∧
      (∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y)) ∧
        Normal E.c E.s ∧ 0<E.s := by
  obtain ⟨E,cp,canonical,shape,inside,_⟩ :=
    ClosedFrames.canonical_frame ((owners p 6).translated 2 2)
  have actual (x y : ℝ) : E.Inside x y↔(owners p 6).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have shape' : E.side=(owners p 6).side := shape
  have positive := southeast_positive p hf missing E shape' actual cp canonical
  exact ⟨E,shape',actual,⟨positive.le,
    by simpa only [abs_of_pos positive] using canonical,E.unit_normal⟩,positive⟩

/-- The retained actual SE points and omissions supply the whole narrow
positive profile.  Its support comparisons are already proved in the
shared C983 source; no numerical orientation enclosure is supplied. -/
theorem southeast_support_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2))
    (E : OpenSquare) (shape : E.side=(owners p 6).side)
    (actual : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (cp : 0<E.c) (canonical : |E.s|≤E.c) :
    Completion.OtherCases.C983.F4SoutheastSignSupports.Data E := by
  have positive := southeast_positive p hf missing E shape actual cp canonical
  apply Completion.OtherCases.C983.F4SoutheastSign.entrance E
    (by rw [shape]; exact side p 6) cp positive.le
    (by simpa only [abs_of_pos positive] using canonical)
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).southeastMarker
  · apply (actual _ _).mpr; norm_num; exact southeast_g6_of_missing_halfpoint p hf missing
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).southeastF8
  · intro own
    apply foreign p hf 6 11 (by decide) _ _ (right_origin p hf)
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply foreign p hf 6 5 (by decide) _ _ (fixed p hf).southwestF4
    convert (actual _ _).mp own using 1 <;> norm_num

/-- The complete original SW/SE pair has only these three directed
support possibilities.  The exceptional transverse one is both signed
and strictly steep; it is not discarded by an unproved SW sign. -/
theorem southeast_pair_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2))
    (A E : OpenSquare) (shapeA : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (ac : 0<A.c) (canonicalA : |A.s|≤A.c)
    (shapeE : E.side=(owners p 6).side)
    (actualE : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (ec : 0<E.c) (canonicalE : |E.s|≤E.c) :
    A.loU+A.side≤lower E A.c A.s ∨
      upper A E.c E.s≤E.loU ∨
        (17*A.s< -7*A.c ∧ A.loV+A.side≤lower E (-A.s) A.c) := by
  have positive := southeast_positive p hf missing E shapeE actualE ec canonicalE
  apply C972Local.positive_southeast_alternatives A E ac canonicalA ec positive.le
    (by simpa only [abs_of_pos positive] using canonicalE)
    (shapeA.trans ((same p 5 6).trans shapeE.symm))
  · apply (actualA _ _).mpr; norm_num; exact southwest_west p hf
  · apply (actualA _ _).mpr; norm_num; exact southwest_south p hf
  · apply (actualA _ _).mpr; norm_num; exact (fixed p hf).southwestF4
  · apply (actualE _ _).mpr; norm_num; exact (fixed p hf).southeastMarker
  · apply (actualE _ _).mpr; norm_num; exact (fixed p hf).southeastF8
  · apply (actualE _ _).mpr; norm_num; exact southeast_g6_of_missing_halfpoint p hf missing
  · intro x y both
    exact apart p hf 5 6 (by decide) _ _
      ⟨(actualA x y).mp both.1,(actualE x y).mp both.2⟩

/-- At a nonnegative SW frame the strict transverse-angle requirement
is impossible, leaving exactly the two eastward longitudinal supports. -/
theorem southeast_nonnegative_pair_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2))
    (A E : OpenSquare) (shapeA : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (ac : 0<A.c) (aSign : 0≤A.s) (canonicalA : |A.s|≤A.c)
    (shapeE : E.side=(owners p 6).side)
    (actualE : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (ec : 0<E.c) (canonicalE : |E.s|≤E.c) :
    A.loU+A.side≤lower E A.c A.s ∨ upper A E.c E.s≤E.loU := by
  rcases southeast_pair_alternatives p hf missing A E shapeA actualA ac canonicalA
      shapeE actualE ec canonicalE with first | second | third
  · exact Or.inl first
  · exact Or.inr second
  · exact False.elim (by linarith only [third.1,ac,aSign])

end
#print axioms southeast_positive
#print axioms exists_positive_southeast
#print axioms southeast_support_profile
#print axioms southeast_pair_alternatives
end N12Compact.FiniteCases.C972
