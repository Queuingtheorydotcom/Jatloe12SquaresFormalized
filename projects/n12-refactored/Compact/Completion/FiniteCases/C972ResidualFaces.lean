import Compact.Completion.FiniteCases.C972SouthwestPositive

/-! Simultaneous faces in the single remaining C972 configuration.
The southeast sharp point comes from that actual square's genuine
mixed pair, actual right origin and actual bottom owner.  Together with
the northwest sharp point it bounds both upper faces of the same SW
square.  A side-width contradiction removes the other sharp-point exit. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem southeast_inner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 2 :=
  southeast_g6_of_missing_halfpoint p hf (southeast_missing_halfpoint p hf)

theorem southeast_mixed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (54/25) (79/50) := by
  have h := fixed p hf
  have point := C1090.ResidualCentralPoints.mixed_point
    ((pullSwap (pullY (owners p 6))).translated 2 2) (side p 6)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]; exact southeast_inner p hf)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]; exact h.southeastF8)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]
        exact foreign p hf 6 7 (by decide) _ _ h.northeastMarker)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]
        exact foreign p hf 6 11 (by decide) _ _ (right_origin p hf))
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]
        exact foreign p hf 6 2 (by decide) _ _ h.southeastCorner)
    (by norm_num [inside_translated_iff,inside_pullSwap,inside_pullY]
        exact foreign p hf 6 10 (by decide) _ _ h.bottomG5)
  norm_num [inside_translated_iff,inside_pullSwap,inside_pullY] at point
  exact point

/-- Both upper faces are produced simultaneously in the same actual SW
frame.  The alternate lower-v exit at the SE sharp point would give
side ≤ .58(c+s) ≤ 29/35 < 1, so it cannot survive. -/
theorem southwest_sharp_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (shape : A.side=(owners p 5).side)
    (actual : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (normal : Normal A.c A.s) :
    A.loU+A.side≤(4/25)*A.c-(21/50)*A.s ∧
      A.loV+A.side≤(4/25)*A.c+(21/50)*A.s := by
  have bounds := normal_bounds normal
  have cp : 0<A.c := by linarith only [bounds.1]
  have sideA : 1<A.side := by rw [shape]; exact side p 5
  have cap := southwest_positive_cap p hf (southeast_missing_halfpoint p hf)
    A actual cp normal.1 normal.2.1
  refine ⟨?_,by linarith only [cap]⟩
  have f : A.Inside 0 (-13/50) := by
    apply (actual _ _).mpr; norm_num; exact (fixed p hf).southwestF4
  have short : (29/50)*(A.c+A.s)<1 := by
    linarith only [bounds.2.2.2.2.2]
  have lowerV : A.loV< -(4/25)*A.s-(21/50)*A.c := by
    linarith only [cap,sideA,short]
  apply le_of_not_gt
  intro high
  have own : A.Inside (4/25) (-21/50) := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [f.1,f.2.2.2,lowerV,high,cp,normal.1,normal.2.1]
  apply apart p hf 5 6 (by decide) _ _ ⟨?_,southeast_mixed_point p hf⟩
  convert (actual _ _).mp own using 1 <;> norm_num

/-- The actual left origin gives a further simultaneous transverse cap.
The other three bands of that origin are strict: the missing-center
upper-u face and side greater than one force its lower-u band. -/
theorem southwest_left_origin_cap (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (shape : A.side=(owners p 5).side)
    (actual : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (normal : Normal A.c A.s) : A.loV+A.side≤A.s := by
  have data := southwest_positive_input p hf A shape actual normal
  have profile := C1092MPPMInwardPositive.profile A data
  have bounds := normal_bounds normal
  have cp : 0<A.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro high
  have own : A.Inside (-1) 0 := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [profile.upperU,data.side,bounds.2.1,data.inner.2.1,
        data.forward.2.2.1,high,cp,normal.1,normal.2.1]
  apply apart p hf 5 9 (by decide) _ _ ⟨?_,left_origin p hf⟩
  convert (actual _ _).mp own using 1 <;> norm_num

/-- The omitted SE lower halfpoint has only its lower-v exit in a
nonnegative canonical frame. Its other three bands follow from the
actual marker and the outer G8 point. -/
theorem southeast_lower_face (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (E : OpenSquare) (shape : E.side=(owners p 6).side)
    (actual : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (normal : Normal E.c E.s) : -E.s-E.c/2≤E.loV := by
  have cp : 0<E.c := by linarith only [(normal_bounds normal).1]
  have marker : E.Inside (7/20) (-7/20) := by
    apply (actual _ _).mpr; norm_num; exact (fixed p hf).southeastMarker
  have outer : E.Inside 1 (-2/5) := by
    apply (actual _ _).mpr; norm_num; exact southeast_g8 p hf
  apply le_of_not_gt
  intro low
  have own : E.Inside 1 (-1/2) := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [marker.1,outer.2.1,outer.2.2.2,low,cp,normal.1,normal.2.1]
  apply southeast_missing_halfpoint p hf
  convert (actual _ _).mp own using 1 <;> norm_num

theorem southeast_height_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (E : OpenSquare) (shape : E.side=(owners p 6).side)
    (actual : ∀ x y,E.Inside x y↔(owners p 6).Inside (2+x) (2+y))
    (normal : Normal E.c E.s) : 0<E.loV+E.side := by
  have cp : 0<E.c := by linarith only [(normal_bounds normal).1]
  have canonical : |E.s|≤E.c := by simpa only [abs_of_nonneg normal.1] using normal.2.1
  have data := southeast_support_profile p hf (southeast_missing_halfpoint p hf)
    E shape actual cp canonical
  have floor := southeast_lower_face p hf E shape actual normal
  have sideE : 1<E.side := by rw [shape]; exact side p 6
  linarith only [floor,sideE,data.sineUpper,data.cosineUpper]

end
#print axioms southeast_mixed_point
#print axioms southwest_sharp_faces
#print axioms southwest_left_origin_cap
#print axioms southeast_lower_face
#print axioms southeast_height_positive
end N12Compact.FiniteCases.C972
