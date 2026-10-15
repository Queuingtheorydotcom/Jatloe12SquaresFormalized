import Compact.Completion.FiniteCases.C972SoutheastReduction
import Compact.Completion.FiniteCases.C972NorthwestForward
import Compact.Completion.OtherCases.C1090.ResidualCentralPoints
import Compact.Completion.CommonCases.InwardPoint

/-! Strict points and actual southwest faces in C972's remaining SE
branch.  The northwest sharp point uses an NE-owned top origin, and the
two southwest tips use the two genuine singleton bars separately.  No
top-wall owner, southwest center, or canonical sign is assumed. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem northwest_mixed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (origin : (owners p 7).Inside 2 3) : (owners p 8).Inside (79/50) (54/25) := by
  have h := fixed p hf
  have point := C1090.ResidualCentralPoints.mixed_point
    ((pullX (owners p 8)).translated 2 2) (side p 8)
    (by norm_num [inside_translated_iff,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_translated_iff,inside_pullX]; exact northwest_forward p hf)
    (by norm_num [inside_translated_iff,inside_pullX]; exact (northwest_pair p hf).2)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 7 (by decide) _ _ h.northeastMarker)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 7 (by decide) _ _ origin)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 4 (by decide) _ _ h.northwestCorner)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 9 (by decide) _ _ h.leftF1)
  norm_num [inside_translated_iff,inside_pullX] at point
  exact point

/-- Each tip is derived from the inward square and a strict point in
the appropriate actual singleton.  In particular the two singletons
are not replaced by a single invented southwest corner square. -/
theorem southwest_strong_tips (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside (73/50) (199/100) ∧
      (owners p 5).Inside (199/100) (73/50) := by
  have h := fixed p hf
  constructor
  · have point := CommonCases.InwardPoint.strong_original (pullX (owners p 5)) (side p 5)
      (by norm_num [inside_pullX]; exact h.southwestMarker)
      (by norm_num [inside_pullX]; exact h.southwestF4)
      (by norm_num [inside_pullX]; exact h.southwestG3)
      (by norm_num [inside_pullX]
          exact foreign p hf 5 6 (by decide) _ _ h.southeastMarker)
      (by norm_num [inside_pullX]
          exact foreign p hf 5 8 (by decide) _ _ h.northwestMarker)
      (by norm_num [inside_pullX]
          exact foreign p hf 5 0 (by decide) _ _
            (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
    norm_num [inside_pullX] at point
    exact point
  · have point := CommonCases.InwardPoint.strong_original
      (pullX (pullSwap (owners p 5))) (side p 5)
      (by norm_num [inside_pullX,inside_pullSwap]; exact h.southwestMarker)
      (by norm_num [inside_pullX,inside_pullSwap]; exact h.southwestG3)
      (by norm_num [inside_pullX,inside_pullSwap]; exact h.southwestF4)
      (by norm_num [inside_pullX,inside_pullSwap]
          exact foreign p hf 5 8 (by decide) _ _ h.northwestMarker)
      (by norm_num [inside_pullX,inside_pullSwap]
          exact foreign p hf 5 6 (by decide) _ _ h.southeastMarker)
      (by norm_num [inside_pullX,inside_pullSwap]
          exact foreign p hf 5 1 (by decide) _ _
            (singleton_vertical p hf _ (by norm_num) (by norm_num)))
    norm_num [inside_pullX,inside_pullSwap] at point
    exact point

private theorem positive_cap (C : OpenSquare) (cp : 0<C.c)
    (sn : 0≤C.s) (order : C.s≤C.c)
    (west : C.Inside (-1/2) 0) (inner : C.Inside (-13/50) 0)
    (missing : ¬C.Inside (-21/50) (4/25)) :
    C.loV+C.side≤(21/50)*C.s+(4/25)*C.c := by
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [west.1,inner.2.1,inner.2.2.1,cp,sn,order,high]

private theorem negative_faces (C : OpenSquare) (cp : 0<C.c)
    (sn : C.s≤0) (order : -C.s≤C.c)
    (inner : C.Inside (-13/50) 0) (tip : C.Inside (-27/50) (-1/100))
    (missing : ¬C.Inside (-21/50) (4/25)) :
    ((-(21/50)*C.c+(4/25)*C.s≤C.loU) ∧ 12*C.c< -17*C.s) ∨
      C.loV+C.side≤(21/50)*C.s+(4/25)*C.c := by
  by_cases lower : -(21/50)*C.c+(4/25)*C.s≤C.loU
  · left
    exact ⟨lower,by linarith only [lower,tip.1]⟩
  · right
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [lower,inner.2.1,inner.2.2.1,cp,sn,order,high]

/-- The genuine NW point forces the southwest upper face for every
nonnegative canonical frame, including the axial and diagonal endpoints.
The face is expressed in the common chart (x-2,y-2). -/
theorem southwest_positive_cap (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 6).Inside 3 (3/2)) (C : OpenSquare)
    (actual : ∀ x y,C.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c) :
    C.loV+C.side≤(21/50)*C.s+(4/25)*C.c := by
  apply positive_cap C cp sn order
  · apply (actual _ _).mpr
    norm_num
    exact southwest_west p hf
  · apply (actual _ _).mpr
    norm_num
    exact (fixed p hf).southwestG3
  · intro own
    have sharp := northwest_mixed_point p hf
      (northeast_origin_of_missing_southeast_halfpoint p hf missing)
    apply apart p hf 5 8 (by decide) _ _ ⟨?_,sharp⟩
    convert (actual _ _).mp own using 1 <;> norm_num

/-- The SE-owned inward point gives the other upper face of the same
nonnegative SW frame. Both faces thus belong to one actual square. -/
theorem southwest_positive_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 6).Inside 3 (3/2)) (C : OpenSquare)
    (actual : ∀ x y,C.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c) :
    C.loU+C.side≤(13/50)*C.c ∧
      C.loV+C.side≤(21/50)*C.s+(4/25)*C.c := by
  refine ⟨?_,southwest_positive_cap p hf missing C actual cp sn order⟩
  have f : C.Inside 0 (-13/50) := by
    apply (actual _ _).mpr
    norm_num
    exact (fixed p hf).southwestF4
  have g : C.Inside (-13/50) 0 := by
    apply (actual _ _).mpr
    norm_num
    exact (fixed p hf).southwestG3
  apply le_of_not_gt
  intro high
  apply apart p hf 5 6 (by decide) _ _ ⟨?_,southeast_g6_of_missing_halfpoint p hf missing⟩
  have own : C.Inside (13/50) 0 := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [f.1,f.2.2.1,g.2.2.2,high,cp,sn,order]
  convert (actual _ _).mp own using 1 <;> norm_num

/-- For the other canonical sign the only additional possible exit is
the actual lower-u face, and the strict southwest tip makes that exit
strictly steeper than 12/17.  No whole-family sign is asserted. -/
theorem southwest_negative_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 6).Inside 3 (3/2)) (C : OpenSquare)
    (actual : ∀ x y,C.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (cp : 0<C.c) (sn : C.s≤0) (order : -C.s≤C.c) :
    ((-(21/50)*C.c+(4/25)*C.s≤C.loU) ∧ 12*C.c< -17*C.s) ∨
      C.loV+C.side≤(21/50)*C.s+(4/25)*C.c := by
  apply negative_faces C cp sn order
  · apply (actual _ _).mpr
    norm_num
    exact (fixed p hf).southwestG3
  · apply (actual _ _).mpr
    norm_num
    exact (southwest_strong_tips p hf).1
  · intro own
    have sharp := northwest_mixed_point p hf
      (northeast_origin_of_missing_southeast_halfpoint p hf missing)
    apply apart p hf 5 8 (by decide) _ _ ⟨?_,sharp⟩
    convert (actual _ _).mp own using 1 <;> norm_num

end
#print axioms northwest_mixed_point
#print axioms southwest_strong_tips
#print axioms southwest_positive_cap
#print axioms southwest_positive_faces
#print axioms southwest_negative_faces
end N12Compact.FiniteCases.C972
