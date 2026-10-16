import Compact.Geometry.C849NegativeLongitudinal
import Compact.Geometry.C849NegativeSupport
import Compact.Geometry.C849NegativeCorner

/-! The complete canonical negative-B sector uses the actual left wall
and upper-left corner squares. The original C point retains both possible
upper faces; the proof contains no orientation enumeration. -/
namespace N12Compact.C849Negative
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

private theorem transverse_impossible (B L : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < B.side) (same : B.side=L.side)
    (box : InsideContainer L) (left : ClosedInside L (457/500) 2)
    (low : -L.s*(19/25)+L.c*(187/100) ≤ L.loV)
    (bottom : B.Inside (33/20) (47/20))
    (corner : B.side*(B.c-B.s)+4*B.s ≤ B.loU)
    (cFace : B.loU+B.side ≤ (113/50)*B.c+3*B.s ∨
      B.loV+B.side ≤ -(113/50)*B.s+3*B.c)
    (axis : upper L (-B.s) B.c ≤ B.loV) : False := by
  let c := B.c
  let t := -B.s
  have ht : 0 ≤ t := neg_nonneg.mpr bs
  have normal : c^2+t^2=1 := by dsimp [c,t]; nlinarith only [B.unit_normal]
  have wall := FourSquareBLBridge.left_wall L lc.le box
  have support := C849NegativeSupport.support L.side c t L.c L.s L.loU L.loV
    (upper L t c) (by simpa only [same] using ha) bc ht bsc lc lsc L.unit_normal
    wall (by linarith only [low]) (by linarith only [left.1])
    (by dsimp [upper,centerX,centerY,supportRadius]; ring)
  rcases support with lowSupport | ⟨steep,highSupport⟩
  · dsimp [c,t] at lowSupport
    linarith only [lowSupport,axis,bottom.2.2.1]
  · rcases cFace with cU | cV
    · have gain := mul_pos (sub_pos.mpr ha)
        (show 0 < 1+c+t by positivity)
      have corner' : B.side*(c+t)-4*t ≤ B.loU := by
        dsimp [c,t]; nlinarith only [corner]
      have cU' : B.loU+B.side ≤ (113/50)*c-3*t := by
        dsimp [c,t]; linarith only [cU]
      have cLower : 50/63 ≤ c := by
        clear_value c t
        nlinarith only [corner',cU',gain]
      have square := mul_nonneg (sub_nonneg.mpr steep)
        (show 0 ≤ t+(4/5)*c by positivity)
      clear_value c t
      nlinarith only [normal,square,cLower,sq_nonneg (c-50/63)]
    · have sum : c+t ≤ 10/7 := by
        clear_value c t
        nlinarith only [normal,sq_nonneg (c-t),sq_nonneg (c+t-10/7)]
      have short : (63/50)*t+(13/100)*c < 1 := by
        linarith only [sum,bsc]
      have cV' : B.loV+B.side ≤ (113/50)*t+3*c := by
        dsimp [c,t]; linarith only [cV]
      change upper L t c ≤ B.loV at axis
      linarith only [highSupport,axis,cV',short,ha]

/-- Every premise refers to an original square, a compulsory original
point, or a foreign point's exact exclusion. L is only reindexed to its
canonical face frame. No extra packing restriction is introduced. -/
theorem impossible (B L E : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < B.side) (size : B.side ≤ 1001/1000)
    (sameL : B.side=L.side) (sameE : E.side=B.side)
    (boxL : InsideContainer L) (boxE : InsideContainer E)
    (bottom : B.Inside (33/20) (47/20))
    (top : ClosedInside B (8/5) 3) (high : B.Inside 2 (1543/500))
    (missingA : ¬ B.Inside 2 (5/2)) (missingC : ¬ B.Inside (113/50) 3)
    (left : ClosedInside L (457/500) 2) (lTop : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (eP : E.Inside 1 (1543/500)) (eQ : E.Inside (457/500) 3)
    (apartBL : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y))
    (apartBE : ∀ x y, ¬ (B.Inside x y ∧ E.Inside x y)) : False := by
  have corner := C849NegativeCorner.lower_face B E bc bs bsc sameE ha size boxE
    eP eQ bottom top apartBE
  have faces := C849NegativePoints.right_faces B bc bs bottom top missingC
  have cap := C849NegativePoints.upper_face B bc bs bsc bottom high missingA
  obtain ⟨low,axes⟩ := C849NegativeBL.alternatives B L bc bs bsc lc lsc ha sameL
    bottom high missingA left lTop missingLow missingRight apartBL
  rcases axes with transverse | longitudinal
  · exact transverse_impossible B L bc bs bsc lc lsc ha sameL boxL left low bottom
      corner faces transverse
  · exact C849NegativeLongitudinal.impossible B L bc bs bsc lc lsc ha sameL
      boxL left low cap bottom high corner faces longitudinal

#print axioms impossible
end N12Compact.C849Negative
