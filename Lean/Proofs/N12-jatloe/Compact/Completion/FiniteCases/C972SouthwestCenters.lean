import Compact.Completion.FiniteCases.C972NorthwestHalfpoint
import Compact.Geometry.SouthwestNegativeCorner

/-! The actual singleton corner selects the complementary SW center
argument. Each literal transpose carries both different singleton owners
and the foreign wall marker with it. No singleton is replaced by a paired
corner. These are conditional actual-center producers, not case exclusions. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

private theorem negative_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A : OpenSquare)
    (normal : Normal A.c (-A.s)) (shape : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside x y)
    (missing : ¬(owners p 0).Inside 1 1) : A.Inside 2 2 := by
  have h := fixed p hf
  apply SouthwestNegativeCorner.point (owners p 0) A (owners p 1) (-A.s)
    (by ring) normal ((same p 0 5).trans shape.symm)
    (by rw [shape]; exact side p 5) (box p 0)
  · convert seed p hf 0 (1,457/500) (by decide +kernel) using 1 <;> norm_num
  · exact singleton_horizontal p hf _ le_rfl (by norm_num)
  · exact h.singleton0Seed
  · exact missing
  · exact foreign p hf 0 10 (by decide) _ _ h.bottomMarker
  · exact (actualA _ _).mpr h.southwestMarker
  · exact (actualA _ _).mpr h.southwestF4
  · exact (actualA _ _).mpr h.southwestG3
  · exact (actualA _ _).mpr (southwest_west p hf)
  · exact singleton_vertical p hf _ le_rfl (by norm_num)
  · exact singleton_vertical p hf _ (by norm_num) le_rfl
  · intro x y both
    exact apart p hf 0 5 (by decide) x y ⟨both.1,(actualA x y).mp both.2⟩
  · intro x y both
    exact apart p hf 5 1 (by decide) x y ⟨(actualA x y).mp both.1,both.2⟩

private theorem positive_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A : OpenSquare)
    (normal : Normal A.c A.s) (shape : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside x y)
    (missing : ¬(owners p 1).Inside 1 1) : A.Inside 2 2 := by
  let Q := turnFrame (turnFrame (turnFrame (pullSwap A)))
  have qc : Q.c=A.c := by dsimp only [Q,turnFrame,pullSwap]; ring
  have qs : Q.s= -A.s := by dsimp only [Q,turnFrame,pullSwap]
  have qi (x y : ℝ) : Q.Inside x y↔A.Inside y x := by
    simp only [Q,turnFrame_inside,inside_pullSwap]
  have h := fixed p hf
  have result := SouthwestNegativeCorner.point
    (pullSwap (owners p 1)) Q (pullSwap (owners p 0)) A.s qs
    (by simpa only [qc] using normal) ((same p 1 5).trans shape.symm)
    (by change 1<A.side; rw [shape]; exact side p 5)
    (container_pullSwap _ (box p 1))
    (by
      apply (inside_pullSwap _ _ _).mpr
      convert seed p hf 1 (457/500,1) (by decide +kernel) using 1 <;> norm_num)
    ((inside_pullSwap _ _ _).mpr (singleton_vertical p hf _ le_rfl (by norm_num)))
    ((inside_pullSwap _ _ _).mpr h.singleton1Seed)
    (fun own => missing ((inside_pullSwap _ _ _).mp own))
    (fun own => foreign p hf 1 9 (by decide) _ _ h.leftMarker
      ((inside_pullSwap _ _ _).mp own))
    ((qi _ _).mpr ((actualA _ _).mpr h.southwestMarker))
    ((qi _ _).mpr ((actualA _ _).mpr h.southwestG3))
    ((qi _ _).mpr ((actualA _ _).mpr h.southwestF4))
    ((qi _ _).mpr ((actualA _ _).mpr (southwest_south p hf)))
    ((inside_pullSwap _ _ _).mpr (singleton_horizontal p hf _ le_rfl (by norm_num)))
    ((inside_pullSwap _ _ _).mpr (singleton_horizontal p hf _ (by norm_num) le_rfl))
    (by
      intro x y both
      exact apart p hf 1 5 (by decide) y x
        ⟨(inside_pullSwap _ _ _).mp both.1,(actualA _ _).mp ((qi _ _).mp both.2)⟩)
    (by
      intro x y both
      exact apart p hf 5 0 (by decide) y x
        ⟨(actualA _ _).mp ((qi _ _).mp both.1),(inside_pullSwap _ _ _).mp both.2⟩)
  exact (qi 2 2).mp result

/-- An NE-owned top origin forces singleton1's corner. Its exclusion
from singleton0 supplies the entire negative-SW center theorem. The
returned point is in the given same-actual frame at the common origin. -/
theorem southwest_negative_center_of_northeast_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (origin : (owners p 7).Inside 2 3)
    (A : OpenSquare) (normal : Normal A.c (-A.s))
    (shape : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y)) : A.Inside 0 0 := by
  let G := A.translated (-2) (-2)
  have actualG (x y : ℝ) : G.Inside x y↔(owners p 5).Inside x y := by
    simp only [G,inside_translated_iff,actualA]
    ring
  have missing := foreign p hf 0 1 (by decide) _ _
    (one_corner_of_northeast_origin p hf origin)
  have center := negative_center p hf G normal shape actualG missing
  norm_num [G,inside_translated_iff] at center
  exact center

/-- A real SE lower halfpoint forces singleton0's corner. The literal
transpose of the same theorem therefore supplies the nonnegative-SW
center, including the zero-angle endpoint. -/
theorem southwest_positive_center_of_southeast_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (half : (owners p 6).Inside 3 (3/2))
    (A : OpenSquare) (normal : Normal A.c A.s)
    (shape : A.side=(owners p 5).side)
    (actualA : ∀ x y,A.Inside x y↔(owners p 5).Inside (2+x) (2+y)) : A.Inside 0 0 := by
  let G := A.translated (-2) (-2)
  have actualG (x y : ℝ) : G.Inside x y↔(owners p 5).Inside x y := by
    simp only [G,inside_translated_iff,actualA]
    ring
  have missing := foreign p hf 1 0 (by decide) _ _
    (zero_corner_of_southeast_halfpoint p hf half)
  have center := positive_center p hf G normal shape actualG missing
  norm_num [G,inside_translated_iff] at center
  exact center

end
#print axioms southwest_negative_center_of_northeast_origin
#print axioms southwest_positive_center_of_southeast_halfpoint
end N12Compact.FiniteCases.C972
