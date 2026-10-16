import Compact.Completion.FiniteCases.C972SoutheastCentered
import Compact.Completion.FiniteCases.C972SouthwestCenters
import Compact.Completion.FiniteCases.C972UpperEnding
import Compact.Completion.C1092.MPPMInwardPositiveProfile

/-! C972 has a positive, missing-center inward southwest square.
The opposite canonical sign would own the center by the actual two-
singleton theorem; the actual positive-SE support join excludes that
center.  Its inward profile then follows from literal owned/omitted
points, including the sharp tip and separate genuine singleton bars. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

theorem southwest_missing_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owners p 5).Inside 2 2 :=
  southwest_center_missing p hf (southeast_missing_halfpoint p hf)

/-- The zero canonical angle is included in the negative-center
obstruction and therefore cannot survive this original family. -/
theorem southwest_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (shape : A.side=(owners p 5).side)
    (actual : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (cp : 0<A.c) (canonical : |A.s|≤A.c) : 0<A.s := by
  have _positiveCosine := cp
  apply lt_of_not_ge
  intro sign
  have normal : Normal A.c (-A.s) := ⟨by linarith only [sign],
    by simpa only [abs_of_nonpos sign] using canonical,by nlinarith only [A.unit_normal]⟩
  have center := southwest_negative_center_of_northeast_origin p hf (northeast_origin p hf)
    A normal shape actual
  apply southwest_missing_center p hf
  convert (actual _ _).mp center using 1 <;> norm_num

theorem exists_positive_southwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∃ A : OpenSquare,A.side=(owners p 5).side ∧
      (∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y)) ∧
        Normal A.c A.s ∧ 0<A.s := by
  obtain ⟨A,cp,canonical,shape,inside,_⟩ :=
    ClosedFrames.canonical_frame ((owners p 5).translated 2 2)
  have actual (x y : ℝ) : A.Inside x y↔(owners p 5).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have shape' : A.side=(owners p 5).side := shape
  have positive := southwest_positive p hf A shape' actual cp canonical
  exact ⟨A,shape',actual,⟨positive.le,
    by simpa only [abs_of_pos positive] using canonical,A.unit_normal⟩,positive⟩

/-- Every raw point in the shared positive inward theorem is supplied
by an original C972 square. The outer left point is in singleton1, the
bottom point in singleton0, and the northwest marker in actual NW2048. -/
theorem southwest_positive_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (shape : A.side=(owners p 5).side)
    (actual : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (normal : Normal A.c A.s) : C1092MPPMInwardPositive.Input A := by
  refine {
    side := by rw [shape]; exact side p 5
    normal := normal
    marker := ?_, inner := ?_, forward := ?_, crosspoint := ?_, sharp := ?_
    origin := ?_, outer := ?_, bottom := ?_, northwest := ?_ }
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).southwestMarker
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).southwestF4
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).southwestG3
  · apply (actual _ _).mpr; norm_num; exact southwest_west p hf
  · apply (actual _ _).mpr; norm_num; exact (southwest_strong_tips p hf).2
  · intro own
    apply southwest_missing_center p hf
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply foreign p hf 5 1 (by decide) _ _
      (singleton_vertical p hf (8/5) (by norm_num) (by norm_num))
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply foreign p hf 5 0 (by decide) _ _
      (singleton_horizontal p hf (8/5) (by norm_num) (by norm_num))
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply foreign p hf 5 8 (by decide) _ _ (fixed p hf).northwestMarker
    convert (actual _ _).mp own using 1 <;> norm_num

theorem southwest_positive_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (shape : A.side=(owners p 5).side)
    (actual : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (normal : Normal A.c A.s) : C1092MPPMInwardPositive.Profile A :=
  C1092MPPMInwardPositive.profile A (southwest_positive_input p hf A shape actual normal)

end
#print axioms southwest_positive
#print axioms southwest_positive_input
#print axioms southwest_positive_profile
end N12Compact.FiniteCases.C972
