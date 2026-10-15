import Compact.Geometry.C696BottomChainSelectors
import Compact.Geometry.C977NegativeCorner

/-! A shallow negative bottom singleton forces the next actual bottom
wall to have a negative canonical frame as well. The next paired corner's
genuine marker supplies the wall's upper escape. The small bottom angle
must be supplied by actual central geometry; it is not inferred from the
singleton alone. Source only, uncompiled. -/
namespace N12Compact.NegativeBottomNextWall

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem entry {d s : ℝ} (normal : Normal d s) :
    0≤(1-d)*(1-d/2)+s*(d-457/500) := by
  have b := normal_bounds normal
  by_cases sign : 457/500≤d
  · have first := mul_nonneg (sub_nonneg.mpr b.2.1)
      (show 0≤1-d/2 by linarith only [b.2.1])
    have second := mul_nonneg normal.1 (sub_nonneg.mpr sign)
    linarith only [first,second]
  · have replace := mul_nonneg (sub_nonneg.mpr normal.2.1)
      (show 0≤457/500-d by linarith only [sign])
    have certificate : 1-(1207/500)*d+(3/2)*d^2=
        (3/2)*(d-1207/1500)^2+43151/1500000 := by ring
    nlinarith only [replace,certificate,sq_nonneg (d-1207/1500)]

private theorem shallow_cosine {c t : ℝ} (normal : Normal c t)
    (small : t≤1/5) : 19/20<c := by
  have b := normal_bounds normal
  have bounded := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/5+t by linarith only [normal.1])
  by_contra failure
  have square := mul_nonneg (show 0≤19/20-c by linarith only [failure])
    (show 0≤19/20+c by linarith only [b.1])
  nlinarith only [bounded,square,normal.2.2]

/-- Both actual longitudinal separators are impossible when the next
wall is positive. The directed SAT theorem retains every transverse
alternative, which the signed angle bounds eliminate here. -/
theorem impossible (O D : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (dn : Normal D.c D.s) (small : t≤1/5)
    (same : O.side=D.side) (side : 1<O.side)
    (oBox : InsideContainer O) (dBox : InsideContainer D)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oMiddle : O.Inside (87/50) 1) (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1)
    (marker : D.Inside 2 (457/500)) (missingNext : ¬D.Inside 3 (457/500))
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) : False := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have wide := shallow_cosine on small
  have faces := corner_face O t os on side oBox oMarker oNear oFar missingCorner
  let K : ℝ := O.c*D.c-t*D.s
  let H : ℝ := O.c*D.s+t*D.c
  have kp : 0≤K := by
    have first := mul_nonneg dc.le (sub_nonneg.mpr on.2.1)
    have second := mul_nonneg on.1 (sub_nonneg.mpr dn.2.1)
    dsimp [K]; nlinarith only [first,second]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg oc.le dn.1) (mul_nonneg on.1 dc.le)
  have lowerForm : lower D O.c (-t)=K*D.loU-H*(D.loV+O.side) := by
    rw [lower_in_bands,←same]
    have first : O.c*D.c+(-t)*D.s=K := by dsimp [K]; ring
    have second : -O.c*D.s+(-t)*D.c=-H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  have upperForm : upper O D.c D.s=K*(O.loU+O.side)+H*(O.loV+O.side) := by
    rw [upper_negative_pos O t D.c D.s os]
    · dsimp [K,H]; ring
    · simpa [K,mul_comm] using kp
    · simpa [H,mul_comm,add_comm] using hp
  have dBottom := ThreeSquare.bottom_wall D dc.le dBox
  rw [abs_of_nonneg dn.1] at dBottom
  have dWall : 0≤D.s*D.loU+D.c*D.loV := by
    dsimp [centerY] at dBottom
    nlinarith only [dBottom]
  have markerU : D.loU<2*D.c+(457/500)*D.s := by
    nlinarith only [marker.1]
  have escapes : D.loU+O.side≤3*D.c+(457/500)*D.s ∨
      (457/500)*D.c-3*D.s≤D.loV := by
    by_cases cap : D.loU+O.side≤3*D.c+(457/500)*D.s
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro low
      apply missingNext
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [marker.1,marker.2.2.2,dc,dn.1,cap,low,same]
  have noD : ¬upper O D.c D.s≤D.loU := by
    have cornerWeight := mul_nonneg dc.le (sub_nonneg.mpr faces.1)
    have floorWeight := mul_nonneg hp (sub_nonneg.mpr faces.2.1)
    have width := mul_pos (sub_pos.mpr side)
      (show 0<D.c+O.c*H by nlinarith only [dc,mul_nonneg oc.le hp])
    have defect := mul_nonneg
      (mul_nonneg dc.le (sub_nonneg.mpr ob.2.1))
      (show 0≤1-t by linarith only [small])
    have tilt := mul_nonneg (mul_nonneg oc.le dn.1)
      (show 0≤O.c-457/500 by linarith only [wide])
    have identity : O.c*(upper O D.c D.s-(2*D.c+(457/500)*D.s))=
        D.c*(O.loU-(O.c-t))+H*(O.c*O.loV-t*(O.loU+O.side))+
        (O.side-1)*(D.c+O.c*H)+D.c*(1-O.c)*(1-t)+
        O.c*D.s*(O.c-457/500) := by
      rw [upperForm]
      dsimp [K,H]
      linear_combination (D.c*(O.loU+O.side))*on.2.2
    have strict : 0<O.c*(upper O D.c D.s-(2*D.c+(457/500)*D.s)) := by
      linarith only [identity,cornerWeight,floorWeight,width,defect,tilt]
    have gap := pos_of_mul_pos_right strict oc.le
    intro sep
    linarith only [gap,markerU,sep]
  have noO : ¬O.loU+O.side≤lower D O.c (-t) := by
    intro sep
    rcases escapes with cap | low
    · let M : ℝ := D.c+O.c+D.c*H-2*O.c*D.c-D.c*t-(457/500)*O.c*D.s
      have margin : 0≤M := by
        have term₀ := mul_nonneg oc.le (entry dn)
        have term₁ := mul_nonneg dc.le (sub_nonneg.mpr ob.2.1)
        have term₂ := mul_nonneg
          (mul_nonneg (show 0≤O.c/2-t by linarith only [wide,small]) dc.le)
          (sub_nonneg.mpr db.2.1)
        have decomposition : M=
            O.c*((1-D.c)*(1-D.c/2)+D.s*(D.c-457/500))+
            D.c*(1-O.c)+(O.c/2-t)*D.c*(1-D.c) := by
          dsimp [M,H]; ring
        linarith only [decomposition,term₀,term₁,term₂]
      have cornerWeight := mul_nonneg dc.le (sub_nonneg.mpr faces.1)
      have capWeight := mul_nonneg oc.le (sub_nonneg.mpr cap)
      have wallWeight := mul_nonneg hp dWall
      have width := mul_pos (sub_pos.mpr side)
        (show 0<D.c+O.c+D.c*H by nlinarith only [dc,oc,mul_nonneg dc.le hp])
      have identity : D.c*(O.loU+O.side-lower D O.c (-t))=
          D.c*(O.loU-(O.c-t))+O.c*(3*D.c+(457/500)*D.s-(D.loU+O.side))+
          H*(D.s*D.loU+D.c*D.loV)+(O.side-1)*(D.c+O.c+D.c*H)+M := by
        rw [lowerForm]
        dsimp [K,H,M]
        linear_combination (-O.c*D.loU)*dn.2.2
      have strict : 0<D.c*(O.loU+O.side-lower D O.c (-t)) := by
        linarith only [identity,cornerWeight,capWeight,wallWeight,width,margin]
      have gap := pos_of_mul_pos_right strict dc.le
      linarith only [gap,sep]
    · let M : ℝ := 1-O.c*(1+D.s^2-D.s)-t*(D.c*D.s-D.c+43/500)
      have margin : 0≤M := by
        have sine := mul_nonneg dn.1 (sub_nonneg.mpr db.2.2.2.1)
        have smax : D.s≤3/4 := by linarith only [dn.2.1,db.2.2.2.2.2]
        have product := mul_nonneg dc.le (sub_nonneg.mpr smax)
        have coefficient : D.c*D.s-D.c+43/500≤0 := by
          nlinarith only [product,db.1]
        have first := mul_nonneg oc.le sine
        have second := mul_nonneg on.1 (neg_nonneg.mpr coefficient)
        dsimp [M]
        nlinarith only [first,second,ob.2.1]
      have cornerWeight := sub_nonneg.mpr faces.1
      have markerWeight := mul_nonneg kp (sub_nonneg.mpr markerU.le)
      have lowWeight := mul_nonneg hp (sub_nonneg.mpr low)
      have width := mul_pos (sub_pos.mpr side) (show 0<1+H by linarith only [hp])
      have identity : O.loU+O.side-lower D O.c (-t)=
          (O.loU-(O.c-t))+K*(2*D.c+(457/500)*D.s-D.loU)+
          H*(D.loV-((457/500)*D.c-3*D.s))+(O.side-1)*(1+H)+M := by
        rw [lowerForm]
        dsimp [K,H,M]
        linear_combination (-2*O.c+(457/500)*t)*dn.2.2
      linarith only [identity,cornerWeight,markerWeight,lowWeight,width,margin,sep]
  have directed := C696BottomChainSelectors.singleton_wall O D oc dc
    (by rw [os]; linarith only [on.1,oc]) dn.2.1 same
    oMarker oMiddle oFar marker apart
  rcases directed with own | next
  · rcases own with forward | transverse
    · exact noO (by simpa only [(ownU O).2,os] using forward)
    · rw [os,neg_neg] at transverse
      nlinarith only [transverse.1,small,ob.1]
  · rcases next with forward | transverse
    · exact noD (by simpa only [(ownU D).1] using forward)
    · nlinarith only [transverse.1,dn.1,dc]

#print axioms impossible
end N12Compact.NegativeBottomNextWall
