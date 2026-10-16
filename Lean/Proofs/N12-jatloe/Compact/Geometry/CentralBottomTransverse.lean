import Compact.Geometry.CentralRightCornerAlternatives

/-! Genuine inward exclusion and the extended bottom-wall point remove
the remaining transverse incoming axis for every central orientation. -/
namespace N12Compact.CentralBottomTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare C977CornerCubic
set_option Elab.async false

/-- After the actual southeast lower-face escape, missing the actual
right-wall midpoint can occur only on the upper U face. -/
theorem inward_cap (B : OpenSquare) (canonical : |B.s|≤B.c)
    (side : 1<B.side) (marker : B.Inside (47/20) (33/20))
    (wall : B.Inside 3 (87/50))
    (floor : B.c-3*B.s≤B.loV) (missing : ¬B.Inside 3 2) :
    B.loU+B.side≤3*B.c+2*B.s := by
  have signs := abs_le.mp canonical
  have nonneg := le_trans (abs_nonneg B.s) canonical
  have positive : 0<B.c := by
    by_contra no
    have zero : B.c=0 := by linarith only [no,nonneg]
    have sine : B.s=0 := by linarith only [zero,signs.1,signs.2]
    nlinarith only [zero,sine,B.unit_normal]
  have bound : B.c≤1 := by
    nlinarith only [B.unit_normal,sq_nonneg B.s,sq_nonneg (B.c-1)]
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,by simpa only [mul_comm] using high,?_,?_⟩ <;>
    nlinarith only [marker.1,wall.2.2.1,floor,side,positive,bound,signs.1]

/-- A transverse separator below the actual crosspoint forces the
neighbor to contain the farther point of the bottom wall. -/
theorem point (B : OpenSquare) (normal : Normal B.c B.s)
    (side : 1<B.side) (wall : B.Inside 3 (87/50))
    (cap : B.loU+B.side≤3*B.c+2*B.s)
    (transverse : B.loV+B.side<(3/2)*B.c-2*B.s) :
    B.Inside (13/5) 1 := by
  have bounds := normal_bounds normal
  have square : (B.c+B.s)^2≤2 := by
    nlinarith only [normal.2.2,sq_nonneg (B.c-B.s)]
  have firstShort : (2/5)*B.c+B.s<1 := by
    have order : (2/5)*B.c+B.s≤(7/10)*(B.c+B.s) := by
      linarith only [normal.2.1]
    nlinarith only [order,square]
  have lastShort : (1/2)*B.c+(3/5)*B.s<1 := by
    have order : (1/2)*B.c+(3/5)*B.s≤(11/20)*(B.c+B.s) := by
      linarith only [normal.2.1]
    nlinarith only [order,square]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,firstShort]
  · nlinarith only [wall.2.1,bounds.1,normal.1]
  · linarith only [transverse,side,lastShort]
  · nlinarith only [wall.2.2.2,bounds.1,normal.1,normal.2.1]

#print axioms inward_cap
#print axioms point
end N12Compact.CentralBottomTransverse
