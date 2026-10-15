import Compact.Completion.C1092.MPPMInwardSmallThreeBoundaryScalars
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry

/-! SMALL-INWARD-THREE-SQUARE-ENDING §§4--6. The B--E separation
uses the very B whose C--B separator and signed tilt have been derived.
The final frame change only reindexes that physical square, preserving
its center, side, real wall, and every strict point. Source only. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
open C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

theorem canonical_impossible (C B E : OpenSquare) (input : Input C B E)
    (canonical : |B.s|≤B.c) : False := by
  let d := E.c
  let t := -E.s
  let h := B.c
  let k := B.s
  let n := nu d t h k
  let e := eta d t h k
  let lam := C.c*B.c+C.s*B.s
  let gam := C.c*B.s-C.s*B.c
  have profile := bottom_profile C B input.bottom canonical
  have eb := normal_bounds input.successor.normal
  have bounds := successor_bounds C B E input
  have q : BoundaryRange d t h k :=
    ⟨input.successor.normal,bounds.1,successor_low C B E input,bounds.2,
      profile.cosine,B.unit_normal,profile.low,profile.high⟩
  have coeff := boundary_coefficients q
  have np : 0<n := coeff.1
  have ep : 0<e := by linarith only [coeff.2.2.1]
  have width : 1<t+(343/500)*d := by
    dsimp [d,t]
    linarith only [input.bottom.side,input.sameE,input.successor.lowerV,input.successor.upperV]
  have margins := boundary_margins q width
  have center := BottomAngle.central_faces C B input.bottom
  have same : B.side=E.side := input.bottom.same.symm.trans input.sameE
  have marker : -(543/500)*k<B.loU+B.side := by
    dsimp [k]; linarith only [input.bottom.bottomMarker.2.1]
  have Apositive : 0<C.loU+C.side := by
    have cb := normal_bounds input.bottom.normal
    linarith only [center.lowerU,input.bottom.side,cb.2.1,input.bottom.normal.1]
  have Dcap : B.loV+B.side< -lam*C.side := by
    have first := mul_pos profile.gamma Apositive
    have last := mul_nonneg (show 0≤lam by dsimp [lam]; linarith only [profile.lambda])
      (show 0≤-C.side-C.loV by linarith only [center.upperV])
    dsimp [gam,lam] at *
    nlinarith only [profile.separator,first,last]
  have first_source (sep : B.loU+B.side≤lower E B.c B.s) : False := by
    have formula := lower_nn E B.c B.s n e
      (by dsimp [n,nu,d,t,h,k]; ring) (by dsimp [e,eta,d,t,h,k]; ring) np.le ep.le
    have first := mul_le_mul_of_nonneg_left input.successor.upperU np.le
    have last := mul_le_mul_of_nonneg_left input.successor.upperV ep.le
    have side : 1<E.side := by rw [←input.sameE]; exact input.bottom.side
    have reserve := mul_pos (sub_pos.mpr side) (add_pos np ep)
    have identity : n*(d+t-1)+e*(t-(2/5)*d-1)=h*X0 d t+k*Y0 d t := by
      dsimp [n,e,nu,eta,X0,Y0]
      linear_combination (h-k)*input.successor.normal.2.2
    have margin := first_source_margin q width
    dsimp [d,t,h,k] at first last identity margin
    nlinarith only [sep,formula,first,last,reserve,identity,margin,marker]
  have longitudinal (sep : upper B E.c E.s≤E.loU) : False := by
    have formula := upper_pos_neg B E.c E.s n (-e)
      (by dsimp [n,nu,d,t,h,k]; ring) (by dsimp [e,eta,d,t,h,k]; ring)
      np.le (neg_nonpos.mpr ep.le)
    have first := mul_lt_mul_of_pos_left marker np
    have lowV : B.loV< -C.side*(1+lam) := by linarith only [Dcap,input.bottom.same]
    have last := mul_lt_mul_of_neg_left lowV (neg_neg_of_pos ep)
    have reserve := mul_pos (sub_pos.mpr input.bottom.side)
      (mul_pos ep (show 0<1+lam by dsimp [lam]; linarith only [profile.lambda]))
    have product := mul_nonneg np.le (show 0≤21/1000-k by exact sub_nonneg.mpr profile.high.le)
    have cap : n*k≤21/1000 := by nlinarith only [product,coeff.2.1]
    have second := mul_pos (show 0<e-7/25 by exact sub_pos.mpr coeff.2.2.1)
      (show 0<1+lam by dsimp [lam]; linarith only [profile.lambda])
    have height : 1/2<upper B E.c E.s := by
      nlinarith only [formula,first,last,reserve,cap,second,profile.lambda]
    have low : E.loU<1/2 := by
      dsimp [d,t] at bounds
      linarith only [input.successor.upperU,input.sameE,input.bottom.side,eb.2.1,bounds.2]
    linarith only [height,low,sep]
  have transverse (sep : upper B (-E.s) E.c≤E.loV) : False := by
    have formula := upper_pos_pos B (-E.s) E.c e n
      (by dsimp [e,eta,d,t,h,k]; ring) (by dsimp [n,nu,d,t,h,k]; ring) ep.le np.le
    have first := mul_lt_mul_of_pos_left marker ep
    have Wcap : E.loV<t-(2/5)*d-1 := by
      dsimp [d,t]
      linarith only [input.successor.upperV,input.sameE,input.bottom.side]
    by_cases positive : 0≤k
    · have bn : Normal h k := ⟨positive,
        by simpa only [h,k,abs_of_nonneg positive] using canonical,B.unit_normal⟩
      have wall := BottomAngle.positive_wall C B input.bottom bn
      have product := mul_nonneg (show 0≤1-h by linarith only [coeff.2.2.2])
        (show 0≤3-h by linarith only [coeff.2.2.2])
      have width : 0<1+h*(h+k) := by
        have p := mul_nonneg (show 0≤h by linarith only [profile.cosine])
          (show 0≤h+k by linarith only [profile.cosine,positive])
        nlinarith only [p]
      have reserve := mul_pos (sub_pos.mpr input.bottom.side) width
      have extra := mul_nonneg positive
        (show 0≤h/2-49/100 by linarith only [profile.cosine])
      have Dlow : -1+(49/100)*k<B.loV+B.side := by
        dsimp [h,k] at product reserve extra
        nlinarith only [wall,product,reserve,extra]
      have last := mul_lt_mul_of_pos_left Dlow np
      have coef := positive_transverse_coefficient q positive
      have tail := mul_nonneg positive (show 0≤Z0 d t h k by linarith only [coef])
      have gap := mul_nonneg (show 0≤d by linarith only [q.cosine])
        (show 0≤1-h by linarith only [coeff.2.2.2])
      have identity : -(543/500)*e*k+n*(-1+(49/100)*k)-(t-(2/5)*d-1)=
          Delta0 d t+d*(1-h)+k*Z0 d t h k := by
        dsimp [n,e,nu,eta,Delta0,Z0]; ring
      nlinarith only [formula,first,last,Wcap,identity,margins.2.2.2,tail,gap,sep]
    · have negative : k<0 := lt_of_not_ge positive
      have bn : Normal h (-k) := ⟨by linarith only [negative],
        by simpa only [h,k,abs_of_neg negative] using canonical,by nlinarith only [B.unit_normal]⟩
      have Dlow := BottomAngle.negative_wall_height C B input.bottom bn
      have last := mul_lt_mul_of_pos_left Dlow np
      have margin := negative_transverse_margin q negative
      have identity : -(543/500)*e*k-n-(t-(2/5)*d-1)=
          Delta0 d t+d*(1-h)-(543/500)*d*k^2+(-k)*t*((543/500)*h-1) := by
        dsimp [n,e,nu,eta,Delta0]; ring
      nlinarith only [formula,first,last,Wcap,identity,margins.2.2.2,margin,sep]
  have bottom_transverse (negative : k<0)
      (sep : B.loV+B.side≤lower E (-B.s) B.c) : False := by
    have formula := lower_np E (-B.s) B.c (-e) n
      (by dsimp [e,eta,d,t,h,k]; ring) (by dsimp [n,nu,d,t,h,k]; ring)
      (neg_nonpos.mpr ep.le) np.le
    have first := mul_le_mul_of_nonpos_left input.successor.lowerU (neg_nonpos.mpr ep.le)
    have last := mul_le_mul_of_nonneg_left input.successor.upperV np.le
    have side : 1<E.side := by rw [←input.sameE]; exact input.bottom.side
    have reserve := mul_pos (sub_pos.mpr side) (add_pos np ep)
    have numerator := mul_nonneg ep.le q.normal.1
    have relative := negative_relative_cosine q negative
    have factor : 15/17<1-t+(2/5)*d := by linarith only [q.sineHigh,q.cosine]
    have product := mul_pos (show 0<n-15/17 by linarith only [relative,q.cosine])
      (show 0<1-t+(2/5)*d by linarith only [factor])
    have bound : 1<e+n*(1-t+(2/5)*d) := by
      nlinarith only [product,factor,coeff.2.2.1]
    have bn : Normal h (-k) := ⟨by linarith only [negative],
      by simpa only [h,k,abs_of_neg negative] using canonical,by nlinarith only [B.unit_normal]⟩
    have height := BottomAngle.negative_wall_height C B input.bottom bn
    dsimp [d,t] at first last numerator bound
    nlinarith only [formula,first,last,reserve,numerator,bound,height,sep]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower E nx ny) : 0<nx ∧ 0<(7/20)*nx+(92/125)*ny := by
    have a := (strict_bounds B _ _ nx ny unit input.bottom.bottomNear).2
    have b := (strict_bounds E _ _ nx ny unit input.successor.outer).1
    have c := (strict_bounds B _ _ nx ny unit input.bottom.bottomMarker).2
    have f := (strict_bounds E _ _ nx ny unit input.successor.marker).1
    constructor <;> linarith only [a,b,c,f,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B E same input.apartBE
      with bu|bu'|bv|bv'|eu|eu'|ev|ev'
  · exact first_source (by simpa only [(ownU B).2] using bu)
  · have bad := (cone _ _ (by nlinarith only [B.unit_normal]) bu').1
    linarith only [bad,profile.cosine]
  · have bad := (cone _ _ (by nlinarith only [B.unit_normal]) bv).1
    exact bottom_transverse (by dsimp [k]; linarith only [bad])
      (by simpa only [(ownV B).2] using bv)
  · have bad := (cone _ _ (by nlinarith only [B.unit_normal]) bv').2
    linarith only [bad,profile.high,profile.cosine]
  · exact longitudinal (by simpa only [(ownU E).1] using eu)
  · have bad := (cone _ _ (by nlinarith only [E.unit_normal]) eu').1
    linarith only [bad,bounds.1]
  · exact transverse (by simpa only [(ownV E).1] using ev)
  · have bad := (cone _ _ (by nlinarith only [E.unit_normal]) ev').1
    have low := successor_low C B E input
    linarith only [bad,low]

theorem impossible (C B E : OpenSquare) (input : Input C B E) : False := by
  obtain ⟨D,dc,ds,same,cx,cy,inside⟩ := exists_positive_frame B
  have canonicalFrame : ∃ Q : OpenSquare,|Q.s|≤Q.c ∧ Q.side=B.side ∧
      centerX Q=centerX B ∧ (∀ x y,Q.Inside x y↔B.Inside x y) := by
    by_cases order : D.s≤D.c
    · exact ⟨D,by simpa only [abs_of_nonneg ds] using order,same,cx,inside⟩
    · refine ⟨turnFrame (turnFrame (turnFrame D)),?_,by simpa using same,
        by simpa using cx,?_⟩
      · simpa [turnFrame,abs_of_nonneg dc] using (lt_of_not_ge order).le
      · intro x y; simpa using inside x y
  obtain ⟨Q,canonical,same,center,inside⟩ := canonicalFrame
  have changed : Input C Q E :=
    { bottom :=
        { side := input.bottom.side
          same := input.bottom.same.trans same.symm
          normal := input.bottom.normal
          marker := input.bottom.marker
          inner := input.bottom.inner
          forward := input.bottom.forward
          crosspoint := input.bottom.crosspoint
          sharp := input.bottom.sharp
          origin := input.bottom.origin
          outer := input.bottom.outer
          bottomMarker := (inside _ _).mpr input.bottom.bottomMarker
          bottomNear := (inside _ _).mpr input.bottom.bottomNear
          bottomFar := (inside _ _).mpr input.bottom.bottomFar
          wall := fun x y own => input.bottom.wall x y ((inside x y).mp own)
          center := by rw [center]; exact input.bottom.center
          apart := fun x y own => input.bottom.apart x y ⟨own.1,(inside x y).mp own.2⟩ }
      sameE := input.sameE
      successor := input.successor
      apartCE := input.apartCE
      apartBE := fun x y own => input.apartBE x y ⟨(inside x y).mp own.1,own.2⟩ }
  exact canonical_impossible C Q E changed canonical

end
#print axioms impossible
end N12Compact.C1092MPPMInwardSmallThree
