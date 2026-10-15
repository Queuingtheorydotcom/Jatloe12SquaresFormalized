import Compact.Geometry.FullAuxWallEscape
import Compact.Geometry.C977CornerCubic

/-! The genuine paired upper corner closes a narrow outer-central square.
Two actual upper faces place the neighboring wall's original marker inside
the square. No frame or support assumption on that wall is needed. -/
namespace N12Compact.FullAuxWallOuterCorner

open S12 S12Pilot C977CornerCubic

/-- The original upper corner can escape only above V when the top
endpoint has already supplied the upper-U face. -/
theorem corner_cap (B : OpenSquare) (normal : Normal B.c B.s)
    (side : 1<B.side) (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (marker : B.Inside (33/20) (47/20)) (left : B.Inside 1 (12/5))
    (missing : ¬B.Inside 1 3) : B.loV+B.side≤3*B.c-B.s := by
  have bounds := normal_bounds normal
  have cp : 0<B.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro upperV
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [upperU,side,bounds.2.1,marker.2.1,
      normal.2.1,left.2.2.1,cp,upperV]

/-- On the remaining small positive arc, the two genuine upper caps force
the original left-wall marker strictly inside B. -/
theorem two_caps_marker (B : OpenSquare) (normal : Normal B.c B.s)
    (small : B.s<3/10) (side : 1<B.side)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (marker : B.Inside (33/20) (47/20))
    (left : B.Inside 1 (113/50)) : B.Inside (457/500) 2 := by
  have bounds := normal_bounds normal
  have cp : 0<B.c := by linarith only [bounds.1]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [upperU,upperV,side,small,bounds.2.1,
      normal.1,normal.2.1,marker.2.1,left.2.2.2,cp]

#print axioms corner_cap
#print axioms two_caps_marker
end N12Compact.FullAuxWallOuterCorner
