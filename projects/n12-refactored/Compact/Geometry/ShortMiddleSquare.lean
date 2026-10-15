import Compact.Geometry.ABTransverse

/-! A square of side greater than one cannot lie, on one common
separating axis, between two actual points less than one unit apart. -/
namespace N12Compact.ShortMiddleSquare
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem impossible (O D B : OpenSquare) (x y z w u v : ℝ)
    (unit : u^2+v^2=1) (side : 1<D.side)
    (first : O.Inside x y) (last : B.Inside z w)
    (short : (z-x)^2+(w-y)^2<1)
    (width : lower D u v+D.side≤upper D u v)
    (incoming : upper O u v≤lower D u v)
    (outgoing : upper D u v≤lower B u v) : False := by
  have firstBound := (strict_bounds O x y u v unit first).2
  have lastBound := (strict_bounds B z w u v unit last).1
  have identity : (u*(z-x)+v*(w-y))^2+(u*(w-y)-v*(z-x))^2=
      ((z-x)^2+(w-y)^2)*(u^2+v^2) := by ring
  rw [unit,mul_one] at identity
  have projection : u*(z-x)+v*(w-y)<1 := by
    nlinarith only [identity,short,sq_nonneg (u*(w-y)-v*(z-x)),
      sq_nonneg (u*(z-x)+v*(w-y)-1)]
  nlinarith only [firstBound,lastBound,side,width,incoming,outgoing,projection]

#print axioms impossible
end N12Compact.ShortMiddleSquare
