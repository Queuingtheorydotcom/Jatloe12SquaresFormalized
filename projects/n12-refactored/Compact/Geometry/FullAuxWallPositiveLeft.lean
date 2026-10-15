import Compact.Geometry.FullAuxWallPositiveLeftOwn
import Compact.Geometry.FullAuxWallPositiveLeftNeighbor
import Compact.Geometry.FullAuxWallPositiveLeftAboveMargin
import Compact.Geometry.FullAuxWallPositiveLeftBelowMargin
import Compact.Geometry.FullAuxWallPositiveUpperAngleSupport

/-! Complete positive-L sector of the genuine C/B/L support cycle.
Both longitudinal alternatives of L/C and L/B are retained until their
continuous scalar obstructions are applied. -/
namespace N12Compact.FullAuxWallPositiveLeft
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

theorem impossible (L D B : OpenSquare)
    (ln : Normal L.c L.s) (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (side : 1<D.side) (sameLD : L.side=D.side) (sameDB : D.side=B.side)
    (box : InsideContainer L)
    (small : D.s≤11/50) (positive : 1/20<D.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (center : D.Inside 2 2) (bottomPoint : D.Inside 2 (3/2))
    (left : D.Inside (6/5) (19/10))
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (high : B.Inside 1 (12/5))
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (lowerU : (457/500)*B.c+2*B.s≤B.loU)
    (steep : 3/10<B.s) (ordered : D.s*B.c≤D.c*B.s)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV)
    (apartLD : ∀ x y, ¬(L.Inside x y ∧ D.Inside x y))
    (apartLB : ∀ x y, ¬(L.Inside x y ∧ B.Inside x y)) : False := by
  have sideB : 1<B.side := by simpa only [sameDB] using side
  have sameLB : L.side=B.side := sameLD.trans sameDB
  have cap := FullAuxWallPositiveUpperAngleSupport.sine D B dn bn side sameDB
    bottom upperU upperV small offset ordered modes
  have width : 1<(343/500)*B.c+B.s := by
    linarith only [sideB,upperU,lowerU]
  have large := FullAuxWallSmallPositiveLeftB.sine L B ln bn sameLB sideB
    steep cap.le box marker low high upperU upperV lowerU width apartLB
  have axes := FullAuxWallLeftResidual.positive_left_axes L D ln dn sameLD
    marker low center bottomPoint left apartLD
  rcases axes with own | neighbor
  · have nonnegative : 0≤D.loU+D.side-2*(D.c+D.s) := by
      linarith only [center.2.1]
    by_cases order : 0≤L.s*D.c-L.c*D.s
    · have necessary := FullAuxWallPositiveLeftOwn.above L D ln dn side sameLD
        box marker bottomPoint order own
      have margin := FullAuxWallPositiveLeftAboveMargin.margin ln dn large.le
        positive.le small nonnegative offset order
      linarith only [necessary,margin]
    · have order : L.s*D.c-L.c*D.s≤0 := le_of_lt (lt_of_not_ge order)
      have necessary := FullAuxWallPositiveLeftOwn.below L D ln dn side sameLD
        box marker bottom order own
      have margin := FullAuxWallPositiveLeftBelowMargin.margin ln dn large.le
        small nonnegative offset order
      linarith only [necessary,margin]
  · exact FullAuxWallPositiveLeftNeighbor.impossible L D ln dn side sameLD
      box marker small large.le offset neighbor

#print axioms impossible
end N12Compact.FullAuxWallPositiveLeft
