import Compact.Geometry.FullAuxWallTopEndpoint
import Compact.Geometry.FullAuxWallPositiveCNegativeBMargins
import Compact.Geometry.FullAuxWallPositiveTransverse

/-! The positive opposite square and negative upper central square.
The genuinely occupied top endpoint and paired-corner point close both
transverse separating axes. This is an actual-square support argument;
the longitudinal-axis removal is supplied separately by the proved reach
of the opposite square. -/
namespace N12Compact.FullAuxWallPositiveCNegativeB
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

/-- The top endpoint has three forced strict bands in a negative frame. -/
theorem endpoint_cap (B : OpenSquare) (t : ℝ)
    (bs : B.s=-t) (bn : Normal B.c t)
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (missing : ¬B.Inside (8/5) 3) : B.loV+B.side≤3*B.c+(8/5)*t := by
  have bounds := normal_bounds bn
  have bc : 0<B.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro top
  apply missing
  have h := high.1
  have u := marker.2.1
  have v := marker.2.2.1
  rw [bs] at h u v
  refine ⟨?_,?_,?_,?_⟩ <;> rw [bs] <;>
    nlinarith only [h,u,v,top,bc,bn.1,bn.2.1]

/-- The paired corner's genuine seed has only two possible escape faces. -/
theorem corner_faces (B : OpenSquare) (t : ℝ)
    (bs : B.s=-t) (bn : Normal B.c t)
    (marker : B.Inside (33/20) (47/20)) (missing : ¬B.Inside 1 3) :
    B.c-3*t≤B.loU ∨ B.loV+B.side≤3*B.c+t := by
  have bounds := normal_bounds bn
  have bc : 0<B.c := by linarith only [bounds.1]
  by_cases lower : B.c-3*t≤B.loU
  · exact Or.inl lower
  right
  apply le_of_not_gt
  intro top
  apply missing
  have u := marker.2.1
  have v := marker.2.2.1
  rw [bs] at u v
  refine ⟨?_,?_,?_,?_⟩ <;> rw [bs] <;>
    nlinarith only [lower,u,v,top,bc,bn.1,bn.2.1]

/-- Both transverse selectors contradict the original occupied top and
corner points. Each displayed scalar margin covers the full canonical
arc continuously. -/
theorem impossible_of_transverse (D B : OpenSquare) (t : ℝ)
    (dn : Normal D.c D.s) (bs : B.s=-t) (bn : Normal B.c t)
    (sideD : 1<D.side) (sideB : 1<B.side)
    (center : D.Inside 2 2)
    (bottomFace : D.c-(8/5)*D.s≤D.loV)
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (missingTop : ¬B.Inside (8/5) 3) (missingCorner : ¬B.Inside 1 3)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨
      upper D (-B.s) B.c≤B.loV) : False := by
  have cb := normal_bounds dn
  have bb := normal_bounds bn
  have cp : 0<D.c := by linarith only [cb.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have top := endpoint_cap B t bs bn marker high missingTop
  rcases modes with first | second
  · let k := B.c*D.s+t*D.c
    let alpha := B.c*D.c-t*D.s
    have kp : 0≤k := add_nonneg (mul_nonneg bp.le dn.1) (mul_nonneg bn.1 cp.le)
    have ap : 0≤alpha := by
      have p := mul_nonneg bp.le (sub_nonneg.mpr dn.2.1)
      have q := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
      dsimp [alpha]; nlinarith only [p,q]
    have support := lower_np B (-D.s) D.c
      (by rw [bs]; dsimp [k] at kp; nlinarith only [kp])
      (by rw [bs]; dsimp [alpha] at ap; nlinarith only [ap])
    rw [support,bs] at first
    have uk : -D.s*B.c+D.c*(-t) = -k := by dsimp [k]; ring
    have va : -(-D.s)*(-t)+D.c*B.c = alpha := by dsimp [alpha]; ring
    rw [uk,va] at first
    have own : 1+D.c-(8/5)*D.s<D.loV+D.side := by
      linarith only [bottomFace,sideD]
    rcases corner_faces B t bs bn marker missingCorner with lower | upper
    · have u := mul_nonneg kp
        (show 0≤B.loU+B.side-(1+B.c-3*t) by linarith only [lower,sideB])
      have v := mul_nonneg ap
        (show 0≤3*B.c+(8/5)*t-1-B.loV by linarith only [top,sideB])
      have margin := FullAuxWallPositiveCNegativeBMargins.lower_u dn bn
      have identity :
          -k*(1+B.c-3*t)+alpha*(3*B.c+(8/5)*t-1)-
            (1+D.c-(8/5)*D.s)=
          D.c*(2-B.c-t+(3/5)*B.c*t)+
            D.s*((3/5)-B.c+t-(3/5)*t^2)-1 := by
        dsimp [k,alpha]
        linear_combination (3*D.c-D.s)*bn.2.2
      nlinarith only [first,own,u,v,margin,identity]
    · have markerU := marker.2.1
      rw [bs] at markerU
      have u := mul_nonneg kp
        (show 0≤B.loU+B.side-((33/20)*B.c-(47/20)*t) by
          nlinarith only [markerU])
      have v := mul_nonneg ap
        (show 0≤3*B.c+t-1-B.loV by linarith only [upper,sideB])
      have margin := FullAuxWallPositiveCNegativeBMargins.upper_v dn bn
      have identity :
          -k*((33/20)*B.c-(47/20)*t)+alpha*(3*B.c+t-1)-
            (1+D.c-(8/5)*D.s)=
          D.c*(2-B.c-(13/20)*t^2-(13/20)*B.c*t)+
            D.s*(-(1/20)+(13/20)*t^2-(13/20)*B.c*t+t)-1 := by
        dsimp [k,alpha]
        linear_combination (3*D.c-(33/20)*D.s)*bn.2.2
      nlinarith only [first,own,u,v,margin,identity]
  · have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have bound := (strict_bounds D _ _ (-B.s) B.c unit center).2
    rw [bs,neg_neg] at bound second
    nlinarith only [bound,second,top,sideB,bb.2.1,bn.1]

/-- A complete signed sector from the actual A/C/B squares. Both A/C
longitudinal selectors and all C/B separating axes are discharged here;
no shifted left reach or bottom face is an additional assumption. -/
theorem impossible (A D B : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1<A.side) (sameAD : A.side=D.side) (sameDB : D.side=B.side)
    (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (p : A.Inside 2 (113/50)) (aMarker : A.Inside (47/20) (47/20))
    (aHigh : A.Inside (5/2) 3) (aTop : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2) (southwest : D.Inside (33/20) (33/20))
    (bottom : D.Inside 2 (3/2)) (missingBottom : ¬D.Inside (8/5) 1)
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (missingTop : ¬B.Inside (8/5) 3) (missingCorner : ¬B.Inside 1 3)
    (ad : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y))
    (db : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) : False := by
  have sideD : 1<D.side := by rwa [←sameAD]
  have sideB : 1<B.side := by rwa [←sameDB]
  have axes := FullAuxWallPositiveOpposite.alternatives A D side sameAD an dn sp narrow
    escape p aMarker aHigh aTop southwest center ad
  have excess := FullAuxWallPositiveOpposite.upper_u_offset A D side an dn sp narrow
    escape p aHigh aTop center axes
  have u := FullAuxWallPositiveReach.bottom_u A D side sideD an dn sp narrow
    p aHigh aTop bottom axes
  have face := FullAuxWallPositiveReach.bottom_face D dn center u missingBottom
  have reach := FullAuxWallPositiveReach.point D dn sideD center bottom excess.2 face
  have bounds := normal_bounds bn
  have bc : 0<B.c := by linarith only [bounds.1]
  have modes := FullAuxWallPositiveTransverse.alternatives D B dn bc
    (by rw [bs]; linarith only [bn.2.1])
    (by rw [bs]; linarith only [bn.1,bc]) sameDB center reach southwest marker high db
  exact impossible_of_transverse D B t dn bs bn sideD sideB center face
    marker high missingTop missingCorner modes

#print axioms endpoint_cap
#print axioms corner_faces
#print axioms impossible_of_transverse
#print axioms impossible
end N12Compact.FullAuxWallPositiveCNegativeB
