import Compact.Completion.C1092.MixedWideWall
import Compact.Completion.C1092.MixedWideCrossingScalars

/-! A genuine mixed wall forces the missing half-angle crossing in its
actual inward neighbor. Both complete squares and the original wall-center
cut enter the argument; weak support contacts are retained. -/
namespace N12Compact.C1092MixedWideCrossing
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem centered_frame (W : OpenSquare) :
    ∃ R : OpenSquare, 0 < R.c ∧ |R.s| ≤ R.c ∧ R.side=W.side ∧
      centerY R=centerY W ∧ (∀ x y, R.Inside x y ↔ W.Inside x y) := by
  obtain ⟨R,rc,rs,side,_,cy,inside⟩ := exists_positive_frame W
  by_cases order : R.s ≤ R.c
  · have cp : 0 < R.c := by nlinarith only [R.unit_normal,rc,rs,order]
    exact ⟨R,cp,by simpa only [abs_of_nonneg rs] using order,side,cy,inside⟩
  · refine ⟨turnFrame (turnFrame (turnFrame R)),?_,?_,by simpa using side,
      by simpa using cy,?_⟩
    · simpa [turnFrame] using (show 0 < R.s by linarith only [rc,order])
    · simpa [turnFrame,abs_of_nonneg rc] using (lt_of_not_ge order).le
    · intro x y
      simpa using inside x y

theorem negative_axes (C W : OpenSquare) (same : C.side=W.side)
    (cp : 0 < C.c) (cs : C.s < 0) (wp : 0 < W.c) (ws : W.s < 0)
    (Q : C.Inside (13/50) 0) (rho : ℝ) (rhoLarge : 2/5 < rho)
    (R : C.Inside 1 rho) (S : W.Inside (543/500) 0)
    (B : W.Inside 1 (2/5))
    (apart : ∀ x y, ¬ (C.Inside x y ∧ W.Inside x y)) :
    C.loU+C.side ≤ lower W C.c C.s ∨ upper C W.c W.s ≤ W.loU := by
  have all := CongruentSAT.faceSeparation_of_disjoint C W same apart
  change pairRadius C W ≤ |C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W ≤ |-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C ≤ |W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C ≤ |-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius ≤ |nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [identity])
  rcases all with cu | cv | wu | wv
  · have sep := split C.c C.s _ (parallel_radius C W) cu
    rw [(ownU C).1,(ownU C).2] at sep
    rcases sep with forward | reverse
    · exact Or.inl forward
    · have bound := (strict_bounds W _ _ C.c C.s C.unit_normal S).2
      exfalso
      linarith only [reverse,bound,Q.1,cp]
  · have sep := split (-C.s) C.c _ (transverse_radius C W) cv
    rw [(ownV C).1,(ownV C).2] at sep
    rcases sep with forward | reverse
    · have bound := (strict_bounds W _ _ (-C.s) C.c
        (by nlinarith only [C.unit_normal]) B).1
      have weight := mul_pos cp (sub_pos.mpr rhoLarge)
      exfalso
      nlinarith only [forward,bound,R.2.2.2,weight]
    · have bound := (strict_bounds W _ _ (-C.s) C.c
        (by nlinarith only [C.unit_normal]) S).2
      exfalso
      linarith only [reverse,bound,Q.2.2.1,cs]
  · have identity : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]
      exact parallel_radius W C
    have sep := split W.c W.s _ identity wu
    rw [(ownU W).1,(ownU W).2] at sep
    rcases sep with forward | reverse
    · exact Or.inr forward
    · have bound := (strict_bounds C _ _ W.c W.s W.unit_normal Q).1
      exfalso
      linarith only [reverse,bound,S.2.1,wp]
  · have identity : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]
      exact transverse_radius W C
    have sep := split (-W.s) W.c _ identity wv
    rw [(ownV W).1,(ownV W).2] at sep
    rcases sep with forward | reverse
    · have bound := (strict_bounds C _ _ (-W.s) W.c
        (by nlinarith only [W.unit_normal]) R).2
      have weight := mul_pos wp (sub_pos.mpr rhoLarge)
      exfalso
      nlinarith only [forward,bound,B.2.2.1,weight]
    · have bound := (strict_bounds C _ _ (-W.s) W.c
        (by nlinarith only [W.unit_normal]) Q).1
      exfalso
      linarith only [reverse,bound,S.2.2.2,ws]

/-- Once a hypothetical escape supplies a strict point above the wide
wall bar, these two full actual squares cannot separate. The same theorem
serves both missing-center and missing-crosspoint arguments. -/
theorem support_impossible (C W : OpenSquare) (c s z rho : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s)
    (side : 1<C.side) (cap : C.side≤1001/1000) (same : C.side=W.side)
    (cp : 0<c) (sp : 0<s) (angle : z*(1+c)=s) (unitAngle : s*z=1-c)
    (Q : C.Inside (13/50) 0) (M : C.Inside (7/20) (7/20))
    (escape : -z≤C.loU) (R : C.Inside 1 rho) (rhoLarge : 2/5<rho)
    (zp : 0≤z) (zSmall : z<53/500) (cosine : 97/100<c)
    (sine : s<21/100) (halfBound : z≤(51/100)*s)
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (-39/100))
    (B : W.Inside 1 (2/5)) (E : ¬W.Inside 1 (-2/5))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : centerY W≤0)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have sn := sp.le
  have unit : c^2+s^2=1 := by simpa only [cframe,sframe,neg_sq] using C.unit_normal
  have failure := escape
  have owned := R
  obtain ⟨V,vc,vrange,vside,vcenter,vinside⟩ := centered_frame W
  have sameV : C.side=V.side := same.trans vside.symm
  have VS := (vinside _ _).mpr S
  have VT := (vinside _ _).mpr T
  have VB := (vinside _ _).mpr B
  have wallV : ∀ x y, V.Inside x y → x ≤ 2 :=
    fun x y h => wall x y ((vinside x y).mp h)
  have cutV : centerY V ≤ 0 := by simpa only [vcenter] using cut
  have profile := C1092MixedWideWall.canonical_profile V
    (by simpa only [←sameV] using side) (by simpa only [←sameV] using cap)
    vc vrange wallV cutV VS VT VB
    (fun h => E ((vinside _ _).mp h))
    (fun h => apart _ _ ⟨M,(vinside _ _).mp h⟩)
  let d := V.c
  let t := -V.s
  let k := c*t-s*d
  let alpha := c*d+s*t
  have dtunit : d^2+t^2=1 := by dsimp [d,t]; nlinarith only [V.unit_normal]
  have tn : 0 ≤ t := by dsimp [t]; linarith only [profile.1]
  have wide : 5/4 < d+t := by simpa only [d,t,sub_eq_add_neg] using profile.2.2.1
  have margin := C1092MixedWideCrossingScalars.margins c s d t z cp sp unit vc tn dtunit
    wide zp zSmall cosine sine halfBound angle
  have tp : 0 < t := by linarith only [margin.1]
  have kp : 0 < k := margin.2.1
  have ap : 0 < alpha := add_pos_of_pos_of_nonneg (mul_pos cp vc) (mul_nonneg sn tn)
  have disjoint : ∀ x y, ¬ (C.Inside x y ∧ V.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(vinside x y).mp h.2⟩
  have possibilities := negative_axes C V sameV (by rwa [cframe])
    (by rw [sframe]; linarith only [sp]) vc profile.1 Q rho
    rhoLarge owned VS VB disjoint
  have lowerFormula : lower V c (-s)=alpha*V.loU+k*V.loV := by
    dsimp [lower,supportRadius,centerX,centerY,alpha,k,d,t]
    rw [abs_of_nonneg (by dsimp [alpha,d,t] at ap; nlinarith only [ap]),
      abs_of_nonneg (by dsimp [k,d,t] at kp; nlinarith only [kp])]
    ring
  have upperFormula : upper C d (-t)=alpha*(C.loU+C.side)-k*C.loV := by
    dsimp [upper,supportRadius,centerX,centerY]
    rw [cframe,sframe]
    rw [abs_of_nonneg (by dsimp [alpha] at ap; nlinarith only [ap]),
      abs_of_nonpos (by dsimp [k] at kp; nlinarith only [kp])]
    dsimp [alpha,k]
    ring
  have wallBound := square_support_bound V 1 0 2
    (by intro x y h; simpa only [one_mul,zero_mul,add_zero] using wallV x y h)
  have wallCenter : centerX V+V.side*(V.c-V.s)/2 ≤ 2 := by
    simpa [squareRadius,abs_of_pos vc,abs_of_neg profile.1,mul_comm] using wallBound
  have vertex : d*(V.loU+V.side)+t*(V.loV+V.side) ≤ 2 := by
    dsimp [centerX] at wallCenter
    dsimp [d,t]
    nlinarith only [wallCenter]
  have ownV : C.loV < (13/50)*s := by
    have h := Q.2.2.1
    rw [sframe] at h
    nlinarith only [h]
  rcases possibilities with central | wallAxis
  · rw [cframe,sframe] at central
    have lowerScaled : t*lower V c (-s) <
        s*(d-(2/5)*t)+k*(2-C.side*(d+t)) := by
      have first := mul_pos sp (sub_pos.mpr VB.1)
      have second := mul_nonneg kp.le (sub_nonneg.mpr vertex)
      rw [←sameV] at second
      rw [lowerFormula]
      have identity : t*alpha-k*d=s := by
        dsimp [alpha,k]
        linear_combination s*dtunit
      have cancel := congrArg (fun a : ℝ => a*V.loU) identity
      dsimp [d,t] at first
      nlinarith only [first,second,cancel]
    have required := mul_le_mul_of_nonneg_left
      ((add_le_add_right failure C.side).trans central) tp.le
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < t+k*(d+t) by
        have product := mul_nonneg kp.le (by linarith only [vc,tn] : 0 ≤ d+t)
        linarith only [tp,product])
    have identity : t*(1-z)-(s*(d-(2/5)*t)+k*(2-(d+t)))=
        t*(1-z-c+(2/5)*s)+k*(d+t-1) := by dsimp [k]; ring
    nlinarith only [lowerScaled,required,strict,identity,margin.2.2.1]
  · change upper C d (-t) ≤ V.loU at wallAxis
    have uWeight := mul_nonneg ap.le (sub_nonneg.mpr failure)
    have vWeight := mul_pos kp (sub_pos.mpr ownV)
    have sideWeight := mul_pos ap (sub_pos.mpr side)
    have difference : d*(-z*(c+s)+(13/50)*s^2)+
        t*((1-z)*s-(13/50)*s*c+2/5) < 0 := by
      have lowerU := VB.1
      dsimp [d,t] at lowerU
      have identity : alpha*(1-z)-(13/50)*s*k-(d-(2/5)*t)=
          d*(-z*(c+s)+(13/50)*s^2)+
            t*((1-z)*s-(13/50)*s*c+2/5) := by
        dsimp [alpha,k]
        nlinarith only [congrArg (fun a : ℝ => d*a) unitAngle]
      nlinarith only [upperFormula,wallAxis,uWeight,vWeight,sideWeight,lowerU,identity]
    linarith only [difference,margin.2.2.2]

/-- The central frame is explicitly negative; the wall frame and both
actual square positions are unrestricted. -/
theorem point (C W : OpenSquare) (c s z : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s)
    (side : 1 < C.side) (cap : C.side ≤ 1001/1000) (same : C.side=W.side)
    (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (angle : z*(1+c)=s) (unitAngle : s*z=1-c)
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0)
    (M : C.Inside (7/20) (7/20)) (lowerV : 0 ≤ C.loV)
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (-39/100))
    (B : W.Inside 1 (2/5)) (E : ¬ W.Inside 1 (-2/5))
    (wall : ∀ x y, W.Inside x y → x ≤ 2) (cut : centerY W ≤ 0)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ W.Inside x y)) :
    C.loU < -z ∧ C.Inside z 1 := by
  classical
  have unit : c^2+s^2=1 := by simpa only [cframe,sframe,neg_sq] using C.unit_normal
  have sp : 0 < s := by
    have bound := Q.2.2.1
    rw [sframe] at bound
    nlinarith only [bound,lowerV]
  have cu : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,cp]
  have zp : 0 < z := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonpos_of_nonpos_of_nonneg bad
      (show 0 ≤ 1+c by linarith only [cp])
    linarith only [angle,product,sp]
  have zu : z < 1/2 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (sub_nonneg.mpr bad)
      (show 0 ≤ 1+c by linarith only [cp])
    nlinarith only [angle,product,order,unit,cp,sp,cu]
  have cform : (1+z^2)*c=1-z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    dsimp at times
    nlinarith only [times,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have times := congrArg (fun a : ℝ => a*z) unitAngle
    dsimp at times
    nlinarith only [times,angle]
  have crossingFace : C.loU < -z := by
    apply lt_of_not_ge
    intro failure
    let r0 := (1-z)^2/2
    let rho := max (2/5) r0
    have rhoLow : 2/5 ≤ rho := le_max_left _ _
    have rhoHigh : rho < 1/2 := by
      apply max_lt_iff.mpr
      refine ⟨by norm_num,?_⟩
      have product := mul_pos zp (show 0 < 2-z by linarith only [zu])
      dsimp [r0]
      nlinarith only [product]
    have fixedU : c-s*r0=1-z := by dsimp [r0]; nlinarith only [unitAngle,sform]
    have fixedV : s+c*r0=1-r0 := by dsimp [r0]; nlinarith only [cform,angle]
    have owned : C.Inside 1 rho := by
      have lower0 := P.1
      have lower1 := Q.2.2.1
      rw [cframe,sframe] at lower0 lower1
      have product := mul_nonneg sn (show 0 ≤ 1/2-rho by linarith only [rhoHigh])
      have cProduct := mul_nonneg cp.le (show 0 ≤ rho by linarith only [rhoLow])
      have upperU : c-s*rho < C.loU+C.side := by
        have rbound : r0 ≤ rho := le_max_right _ _
        have weight := mul_nonneg sn (sub_nonneg.mpr rbound)
        nlinarith only [fixedU,weight,failure,side]
      have upperV : s+c*rho < C.loV+C.side := by
        by_cases selected : 2/5 ≤ r0
        · have equality : rho=r0 := max_eq_right selected
          rw [equality,fixedV]
          have square : 0 ≤ r0 := by dsimp [r0]; positivity
          linarith only [square,side,lowerV]
        · have equality : rho=2/5 := max_eq_left (lt_of_not_ge selected).le
          rw [equality]
          have bound : s+(2/5)*c ≤ 1 := by
            have sumsq : (s+(2/5)*c)^2 ≤ 49/50 := by
              have gap := mul_nonneg (sub_nonneg.mpr order)
                (show 0 ≤ (41/50)*c+(1/50)*s by linarith only [cp,sn])
              nlinarith only [unit,gap]
            nlinarith only [sumsq,sq_nonneg (s+(2/5)*c-1)]
          linarith only [bound,side,lowerV]
      refine ⟨?_,?_,?_,?_⟩
      · rw [cframe,sframe]
        nlinarith only [lower0,product,cp,order,sn]
      · rw [cframe,sframe]
        nlinarith only [upperU]
      · rw [cframe,sframe]
        nlinarith only [lower1,cProduct,sp]
      · rw [cframe,sframe]
        nlinarith only [upperV]
    have rLarge : 2/5 < r0 := by
      apply lt_of_not_ge
      intro bad
      have equality : rho=2/5 := max_eq_left bad
      rw [equality] at owned
      exact apart _ _ ⟨owned,B⟩
    have selected : rho=r0 := max_eq_right rLarge.le
    have small := C1092MixedWideCrossingScalars.small c s z cp sp order unit zp zu
      angle sform rLarge
    exact support_impossible C W c s z rho cframe sframe side cap same cp sp angle unitAngle
      Q M failure owned (by rw [selected]; exact rLarge) zp.le
      small.1 small.2.1 small.2.2.1 small.2.2.2 S T B E wall cut apart
  have Pupper := P.2.1
  have Qlower := Q.2.2.1
  rw [cframe,sframe] at Pupper Qlower
  have unitU : c*z-s=-z := by nlinarith only [angle]
  have unitV : s*z+c=1 := by linarith only [unitAngle]
  refine ⟨crossingFace,?_,?_,?_,?_⟩
  · rw [cframe,sframe]
    nlinarith only [unitU,crossingFace]
  · rw [cframe,sframe]
    have zLower : s/2 ≤ z := by
      have weight := mul_nonneg zp.le (sub_nonneg.mpr cu)
      nlinarith only [weight,angle]
    nlinarith only [unitU,Pupper,zLower,sp]
  · rw [cframe,sframe]
    nlinarith only [unitV,Qlower,sn,cu,order]
  · rw [cframe,sframe]
    nlinarith only [unitV,lowerV,side]

#print axioms point
end N12Compact.C1092MixedWideCrossing
