import Compact.Completion.C1092.MPPMActualNonordinaryElbow
import Compact.Completion.C1092.MPPMActualNonordinaryFarScalars
import Compact.Geometry.IncreasingSegmentAvoidance

/-! ELBOW-EXCLUSION Theorem 2. The left segment belongs to one actual
foreign square L; both strict endpoints and full-square disjointness are
retained. The far right point is only an omission from E. This local
ending does not assert an original-family successor-sign producer. -/
namespace N12Compact.C1092MPPMActualNonordinary
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support
set_option Elab.async false

theorem far_successor_faces (E : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (h : SuccessorFaces E)
    (M : E.Inside (7/20) (-7/20)) (A : E.Inside (13/50) (-1))
    (far : ¬E.Inside 1 (-14/25)) :
    E.loV+E.side≤-E.s-(14/25)*E.c ∧
      60*E.c<91*(-E.s) ∧ E.c<91/109 := by
  have eb := normal_bounds en
  have cp : 0<E.c := by linarith only [eb.1]
  have width : 1< -E.s+(343/500)*E.c := by
    linarith only [h.lowerV,h.upperV,side]
  have sine : 0< -E.s := by linarith only [width,eb.2.1]
  have uBand : E.c-(14/25)*E.s<E.loU+E.side := by
    apply lt_of_not_ge
    intro high
    have span : 1<E.c-(3/50)*E.s := by linarith only [high,h.lowerU,side]
    have product := mul_pos (show 0<E.c-(3/50)*E.s-1 by linarith only [span])
      (show 0<1+E.c by linarith only [cp])
    have cap := mul_nonneg sine.le (sub_nonneg.mpr eb.2.1)
    have small : -E.s<3/25 := by
      nlinarith only [product,cap,en.2.2,sine]
    linarith only [small,width,eb.2.1]
  have cap : E.loV+E.side≤-E.s-(14/25)*E.c := by
    apply le_of_not_gt
    intro high
    apply far
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [uBand,high,M.1,A.2.2.1,cp,en.1]
  have span : 1< -E.s+(263/500)*E.c := by linarith only [side,h.lowerV,cap]
  exact ⟨cap,far_angle E.c (-E.s) en span⟩

/-- The actual foreign segment supplies both weak possibilities. The
corner-crossing proof keeps the transverse/oblique tie. -/
theorem left_segment (C L : OpenSquare) (h : C1092ElbowProfile.Profile C)
    (P : C.Inside (-1) (-13/50)) (Q : C.Inside (-13/50) 0)
    (R : L.Inside (-543/500) 0) (H : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    C.loV+C.side≤(543/500)*C.s ∨
      -(7059/25000)≤((13/50)*C.c-(43/500)*C.s)*C.loU-
        ((13/50)*C.s+(43/500)*C.c)*(C.loV+C.side) := by
  have cp : 0<C.c := by linarith only [h.cosine]
  have cut := IncreasingSegmentAvoidance.dichotomy C L
    (-543/500) 0 (-1) (13/50) R H
    (by linarith only [cp,h.sinePositive])
    (by linarith only [cp,h.normal.2.1])
    (by linarith only [P.1,h.sinePositive])
    (by linarith only [Q.2.1,cp,h.normal.2.1])
    (by linarith only [P.2.2.1,cp,h.sinePositive]) apart
  have constant :
      (-C.s*((-1)-(-543/500))+C.c*((13/50)-0))*(C.c*(-543/500)+C.s*0)-
        (C.c*((-1)-(-543/500))+C.s*((13/50)-0))*(-C.s*(-543/500)+C.c*0)=
          -(7059/25000) := by
    linear_combination -(7059/25000)*C.unit_normal
  rcases cut with transverse|oblique
  · left; linarith only [transverse]
  · right
    rw [constant] at oblique
    nlinarith only [oblique]

theorem far_impossible (C E L : OpenSquare)
    (side : 1<C.side) (same : C.side=E.side) (h : C1092ElbowProfile.Profile C)
    (en : Normal E.c (-E.s))
    (cM : C.Inside (-7/20) (-7/20)) (cP : C.Inside (-1) (-13/50))
    (cQ : C.Inside (-13/50) 0)
    (M : E.Inside (7/20) (-7/20))
    (A : E.Inside (13/50) (-1)) (B : E.Inside (2/5) (-1))
    (G : ¬E.Inside 1 (-2/5)) (K : ¬E.Inside 1 (-1))
    (R : ¬E.Inside 0 (-543/500)) (far : ¬E.Inside 1 (-14/25))
    (leftMarker : L.Inside (-543/500) 0) (leftAnchor : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y))
    (apartLeft : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) : False := by
  have cp : 0<C.c := by linarith only [h.cosine]
  have dp : 0<E.c := by linarith only [(normal_bounds en).1]
  have length : 1<E.side := by simpa only [←same] using side
  have e := successor_faces E length en M A B G K R
    (fun own => apart 0 (-1/2) ⟨h.crosspoint,own⟩)
  have farFaces := far_successor_faces E length en e M A far
  let k := C.c*E.c+C.s*E.s
  let l := -C.c*E.s+C.s*E.c
  have rel := relative_bounds C.c C.s E.c (-E.s) h.normal en h.cosine h.sinePositive h.sine
  have kp : 0<k := by dsimp [k]; nlinarith only [rel.1]
  have lp : 0<l := by dsimp [l]; nlinarith only [rel.2.1]
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<1+k+l by linarith only [kp,lp])
  have extra := mul_nonneg lp.le dp.le
  have choices := successor_axes C E same cp h.sinePositive dp
    (by linarith only [en.1]) cM M apart
  rcases choices with own|transverse|neighbor|neighborV
  · have formula := lower_nn E C.c C.s k l
      (by dsimp [k]) (by dsimp [l]) kp.le lp.le
    have first := mul_nonneg kp.le
      (show 0≤E.c-E.s-C.side-E.loU by linarith only [e.upperU,same])
    have last := mul_nonneg lp.le
      (show 0≤-E.s-(14/25)*E.c-C.side-E.loV by linarith only [farFaces.1,same])
    have margin := source_longitudinal C.c C.s E.c (-E.s) h.normal en cp h.sinePositive
    dsimp [k,l] at formula first last strict extra
    nlinarith only [own,formula,first,last,strict,h.lowerU,margin,extra]
  · have formula := lower_pn E C.s (-C.c) l (-k)
      (by dsimp [l]; ring) (by dsimp [k]; ring) lp.le (by linarith only [kp])
    rw [←same] at formula
    have ownV : upper C C.s (-C.c)= -C.loV := by
      simpa only [neg_neg,(ABTransverse.ownV C).1] using upper_neg C (-C.s) C.c
    have first := mul_nonneg lp.le
      (show 0≤E.c-E.s-C.side-E.loU by linarith only [e.upperU,same])
    have last := mul_nonneg kp.le
      (show 0≤E.loV+(543/500)*E.c by linarith only [e.lowerV])
    have margin := far_source_transverse C.c C.s E.c (-E.s)
      h.normal en h.cosine h.sinePositive h.sine h.sum farFaces.2.2.le
    dsimp [k,l] at formula first last strict
    nlinarith only [transverse,formula,ownV,first,last,strict,h.upperV,margin,same]
  · have formula := upper_pos_neg C E.c E.s k (-l)
      (by dsimp [k]; ring) (by dsimp [l]; ring) kp.le (by linarith only [lp])
    rcases left_segment C L h cP cQ leftMarker leftAnchor apartLeft with cap|oblique
    · have first := mul_nonneg kp.le
        (show 0≤C.loU+C.c+(2/5)*C.s by linarith only [h.lowerU])
      have last := mul_nonneg lp.le
        (show 0≤(543/500)*C.s-C.side-C.loV by linarith only [cap])
      have margin := far_transverse_segment C.c C.s E.c (-E.s)
        h.normal en h.cosine h.sinePositive h.sine h.sum h.halfSmall farFaces.2.1.le
      dsimp [k,l] at formula first last strict
      nlinarith only [neighbor,formula,first,last,strict,e.upperU,margin,same]
    · let alpha := (13/50)*C.c-(43/500)*C.s
      let gamma := (13/50)*C.s+(43/500)*C.c
      have ap : 0<alpha := by dsimp [alpha]; linarith only [cp,h.normal.2.1]
      have gp : 0<gamma := by dsimp [gamma]; linarith only [cp,h.sinePositive]
      have coefficient : k*gamma-l*alpha=(43/500)*E.c+(13/50)*E.s := by
        dsimp [k,l,alpha,gamma]
        linear_combination ((43/500)*E.c+(13/50)*E.s)*C.unit_normal
      have negative : k*gamma-l*alpha<0 := by
        rw [coefficient]
        linarith only [farFaces.2.1,dp]
      have sep := mul_le_mul_of_nonneg_left neighbor gp.le
      have rightFace := mul_nonneg gp.le
        (show 0≤E.c-E.s-C.side-E.loU by linarith only [e.upperU,same])
      have segment := mul_nonneg lp.le
        (show 0≤alpha*C.loU-gamma*(C.loV+C.side)+7059/25000 by
          dsimp [alpha,gamma]; linarith only [oblique])
      have sourceFace := mul_nonneg
        (show 0≤l*alpha-k*gamma by linarith only [negative])
        (show 0≤-(13/50)*C.s-C.side-C.loU by linarith only [h.upperU])
      have weightedStrict := mul_pos (sub_pos.mpr side)
        (show 0<gamma+l*(gamma+alpha) by
          have prod := mul_pos lp (add_pos gp ap)
          linarith only [gp,prod])
      have margin : 0<gamma*(1-E.c+E.s-(13/50)*C.s*k)+
          l*(gamma+alpha+(13/50)*C.s*alpha-7059/25000) := by
        convert far_oblique_segment C.c C.s E.c (-E.s)
          h.normal en h.cosine h.sinePositive h.sine h.halfSmall farFaces.2.1.le using 1;
          dsimp [gamma,alpha,k,l]; ring
      have weightedFormula := congrArg (fun value : ℝ => gamma*value) formula
      nlinarith only [sep,rightFace,segment,sourceFace,weightedStrict,margin,weightedFormula]
  · have formula := upper_pos_pos C (-E.s) E.c l k
      (by dsimp [l]; ring) (by dsimp [k]; ring) lp.le kp.le
    have first := mul_nonneg lp.le
      (show 0≤C.loU+C.c+(2/5)*C.s by linarith only [h.lowerU])
    have last := mul_nonneg kp.le
      (show 0≤C.loV+C.c-(2/5)*C.s by linarith only [h.lowerV])
    have margin := successor_transverse C.c C.s E.c (-E.s)
      h.normal en h.cosine h.sinePositive h.sine
    dsimp [k,l] at formula first last strict
    nlinarith only [neighborV,formula,first,last,strict,farFaces.1,margin,same,dp]

#print axioms far_successor_faces
#print axioms left_segment
#print axioms far_impossible
end N12Compact.C1092MPPMActualNonordinary
