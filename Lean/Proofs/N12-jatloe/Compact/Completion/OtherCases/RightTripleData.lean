import Compact.Completion.OtherCases.NegativeTripleFaces
import Compact.Completion.OtherCases.TopOnlyQuadrantScalars
import Compact.Completion.OtherCases.DerivedWalls

/-! The exact physical three-square entrance for the remaining negative
ending. These are complete faces and genuine square incidences, not a
finite-angle or compulsory-point-only relaxation. -/
namespace N12Compact.Completion.OtherCases.RightTripleData
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

structure RightProfile (R : OpenSquare) : Prop where
  cosinePositive : 0<R.c
  sineNonpositive : R.s≤0
  origin : R.Inside 1 0
  upperPoint : R.Inside 1 (14/25)
  realWall : R.c*(R.loU+R.side)-R.s*(R.loV+R.side)≤2

theorem right_frame (q : OpenSquare) (origin : q.Inside 1 0)
    (upperPoint : q.Inside 1 (14/25)) (wall : ∀ x y,q.Inside x y → x≤2) :
    ∃ R : OpenSquare,R.side=q.side ∧ (∀ x y,R.Inside x y ↔ q.Inside x y) ∧
      RightProfile R := by
  obtain ⟨R,cp,sn,shape,physical⟩ := WallProfile.negative_frame q
  have o := (physical _ _).mpr origin
  have h := (physical _ _).mpr upperPoint
  have bound : ∀ x y,R.Inside x y → -2≤(-1)*x+0*y := by
    intro x y own
    have inequality := wall x y ((physical _ _).mp own)
    linarith only [inequality]
  have vertex := WallProfile.vertex R (R.loU+R.side) (R.loV+R.side)
    ⟨by linarith only [R.side_pos],le_rfl⟩
    ⟨by linarith only [R.side_pos],le_rfl⟩
  have closed := DerivedWalls.closed_affine_bound R (-1) 0 (-2) 1 0 bound o _ _ vertex
  have realWall : R.c*(R.loU+R.side)-R.s*(R.loV+R.side)≤2 := by
    nlinarith only [closed]
  exact ⟨R,shape,physical,cp,sn,o,h,realWall⟩

structure Input (E N R : OpenSquare) : Prop where
  sameEN : E.side=N.side
  sameER : E.side=R.side
  southeastFaces : NegativeTripleFaces.Data E (-E.s)
  northeastFaces : TopOnlyQuadrantProfile.Data N
  rightFaces : RightProfile R
  southeastMarker : E.Inside (7/20) (-7/20)
  southeastElbow : E.Inside (13/50) 0
  northeastSharp : N.Inside (21/40) (1/8)
  northeastTop : N.Inside (1/2) 1
  northeastLeft : N.Inside 0 (31/50)
  apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)
  apartNR : ∀ x y,¬(N.Inside x y ∧ R.Inside x y)

#print axioms right_frame
end N12Compact.Completion.OtherCases.RightTripleData
