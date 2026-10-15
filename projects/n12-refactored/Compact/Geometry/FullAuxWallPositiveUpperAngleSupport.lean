import Compact.Geometry.FullAuxWallPositiveLowerAngleSupport
import Compact.Geometry.FullAuxWallPositiveUpperAngle

/-! Both actual C/B support selectors bound B's positive sine strictly
below 23/50. All geometric inputs are original-square face inequalities. -/
namespace N12Compact.FullAuxWallPositiveUpperAngleSupport

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

theorem sine (D B : OpenSquare)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (ha : 1<D.side) (same : D.side=B.side)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (small : D.s≤11/50)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (ordered : D.s*B.c≤D.c*B.s)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV) :
    B.s<23/50 := by
  apply lt_of_not_ge
  intro steep
  have cuts := FullAuxWallPositiveLowerAngleSupport.cuts D B dn bn ha same
    bottom upperU upperV ordered modes
  rcases cuts with own | neighbor
  · have bound := FullAuxWallPositiveUpperAngle.c_axis dn bn small steep
    linarith only [own,bound]
  · have bound := FullAuxWallPositiveUpperAngle.b_axis dn bn small steep offset ordered
    linarith only [neighbor,bound]

#print axioms sine
end N12Compact.FullAuxWallPositiveUpperAngleSupport
