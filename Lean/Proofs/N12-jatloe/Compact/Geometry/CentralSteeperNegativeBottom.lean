import Compact.Geometry.CentralSteeperIncoming
import Compact.Geometry.OwnedWestBottomAngle

/-! The small upper-U excess forced by the actual steeper southeast
neighbor still excludes a steep negative bottom singleton. All four
O/A axes and both genuine missing-bottom-marker faces are retained. -/
namespace N12Compact.CentralSteeperNegativeBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem transverse (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (small : A.s≤2/5)
    (near : O.Inside (28/25) 1) (far : O.Inside (187/100) (19/25))
    (marker : A.Inside (33/20) (33/20)) (right : A.Inside 2 (87/50))
    (cap : A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c)
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) :
    O.loV+O.side≤lower A t O.c ∨ upper O (-A.s) A.c≤A.loV := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  have noOwn : ¬(upper O O.c O.s≤lower A O.c O.s ∨
      upper A O.c O.s≤lower O O.c O.s) := by
    have ofar := strict_bounds O _ _ O.c O.s O.unit_normal far
    have anear := strict_bounds A _ _ O.c O.s O.unit_normal marker
    have one := strict_bounds O _ _ O.c O.s O.unit_normal near
    have aright := strict_bounds A _ _ O.c O.s O.unit_normal right
    rw [os] at ofar anear one aright ⊢
    rintro (sep | sep) <;>
      nlinarith only [sep,ofar.2,anear.1,one.1,aright.2,oc,on.1,on.2.1]
  have noCentral : ¬(upper O A.c A.s≤lower A A.c A.s ∨
      upper A A.c A.s≤lower O A.c A.s) := by
    have ofar := strict_bounds O _ _ A.c A.s A.unit_normal far
    have one := strict_bounds O _ _ A.c A.s A.unit_normal near
    have aright := strict_bounds A _ _ A.c A.s A.unit_normal right
    rintro (sep | sep)
    · rw [(ownU A).1] at sep
      nlinarith only [sep,ofar.2,cap,side,ab.2.1,small]
    · nlinarith only [sep,one.1,aright.2,ac,an.1]
  have reverse (c s : ℝ) (hc : 0<c) (hs : s≤c) (unit : c^2+s^2=1) :
      ¬upper A (-s) c≤lower O (-s) c := by
    have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
    have ap := strict_bounds A _ _ (-s) c normal marker
    have op := strict_bounds O _ _ (-s) c normal near
    intro sep
    nlinarith only [sep,ap.2,op.1,hc,hs]
  have axes := CongruentSAT.faceSeparation_of_disjoint O A same apart
  change C977ChainBridge.pairRadius O A≤|O.c*(centerX A-centerX O)+O.s*(centerY A-centerY O)| ∨
    C977ChainBridge.pairRadius O A≤|-O.s*(centerX A-centerX O)+O.c*(centerY A-centerY O)| ∨
    C977ChainBridge.pairRadius A O≤|A.c*(centerX A-centerX O)+A.s*(centerY A-centerY O)| ∨
    C977ChainBridge.pairRadius A O≤|-A.s*(centerX A-centerX O)+A.c*(centerY A-centerY O)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius O x y+supportRadius A x y=R)
      (sep : R≤|x*(centerX A-centerX O)+y*(centerY A-centerY O)|) :=
    separated O A x y (by rwa [identity])
  rcases axes with ou | ov | au | av
  · exact False.elim (noOwn (separateAxis _ _ _ (parallel_radius O A) ou))
  · rcases separateAxis _ _ _ (transverse_radius O A) ov with forward | backward
    · left
      rw [(ownV O).2] at forward
      simpa only [os,neg_neg] using forward
    · exact False.elim (reverse O.c O.s oc (by rw [os]; linarith only [oc,on.1])
        O.unit_normal backward)
  · have identity : supportRadius O A.c A.s+supportRadius A A.c A.s=C977ChainBridge.pairRadius A O := by
      rw [add_comm]; exact parallel_radius A O
    exact False.elim (noCentral (separateAxis _ _ _ identity au))
  · have identity : supportRadius O (-A.s) A.c+supportRadius A (-A.s) A.c=C977ChainBridge.pairRadius A O := by
      rw [add_comm]; exact transverse_radius A O
    rcases separateAxis _ _ _ identity av with forward | backward
    · exact Or.inr (by simpa only [(ownV A).1] using forward)
    · exact False.elim (reverse A.c A.s ac an.2.1 A.unit_normal backward)

private theorem remainder {c t C S : ℝ} (on : Normal c t) (an : Normal C S)
    (small : S≤2/5) :
    (c+t)*((1-C)-(7/20)*S^2)-(c-t)*S*(1-(7/20)*C)+
      (9/100)*C*(t*C+c*S)≤(9/100)*t ∨
    (c+t)*((1-C)-(7/20)*S^2)-(c-t)*S*(1-(7/20)*C)+
      (9/100)*C*(t*C+c*S)≤(3593/9500)*t-(93/475)*c := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0≤c := by linarith only [ob.1]
  have ap : 0≤C := by linarith only [ab.1]
  have wide : 9/10≤C := by
    have square := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤S+2/5 by linarith only [an.1])
    by_contra no
    have csquare := mul_nonneg (show 0≤9/10-C by linarith only [no])
      (show 0≤9/10+C by linarith only [ap])
    nlinarith only [square,csquare,an.2.2]
  have defect : 1-C≤(10/19)*S^2 := by
    have product := mul_nonneg (sub_nonneg.mpr ab.2.1)
      (show 0≤(10/19)*(1+C)-1 by linarith only [wide])
    nlinarith only [product,an.2.2]
  have first := mul_nonneg (add_nonneg cp on.1) (sub_nonneg.mpr defect)
  have second := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr on.2.1) an.1)
    (show 0≤1-(7/20)*C-13/20 by linarith only [ab.2.1])
  have shortSquare := mul_nonneg an.1 (sub_nonneg.mpr small)
  have third := mul_nonneg (add_nonneg cp on.1) shortSquare
  have fourth := mul_nonneg on.1 (sq_nonneg S)
  have fifth := mul_nonneg (mul_nonneg cp an.1) (sub_nonneg.mpr ab.2.1)
  have normalT : t*C^2+t*S^2=t := by linear_combination t*an.2.2
  let Q : ℝ := -(93/190)*c+(1369/1900)*t
  have bound : (c+t)*((1-C)-(7/20)*S^2)-(c-t)*S*(1-(7/20)*C)+
      (9/100)*C*(t*C+c*S)≤(9/100)*t+S*Q := by
    dsimp [Q]
    nlinarith only [first,second,third,fourth,fifth,normalT]
  by_cases sign : Q≤0
  · have product := mul_nonneg an.1 (neg_nonneg.mpr sign)
    exact Or.inl (by linear_combination bound + product)
  · have product := mul_nonneg (show 0≤Q by linarith only [sign]) (sub_nonneg.mpr small)
    right
    dsimp [Q] at bound product
    nlinarith only [bound,product]

private theorem own_axis_impossible (O A : OpenSquare) (t : ℝ)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (side : 1≤A.side) (small : A.s≤2/5)
    (steep : 47/100<t) (spread : 27/20<O.c+t)
    (cap : A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c)
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (face : boundary O.c t<O.loV+O.side)
    (sep : O.loV+O.side≤lower A t O.c) : False := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<O.c := by linarith only [ob.1]
  have ap : 0≤A.c := by linarith only [ab.1]
  let H := t*A.c+O.c*A.s
  let K := O.c*A.c-t*A.s
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg on.1 ap) (mul_nonneg cp.le an.1)
  have kp : 0≤K := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,second]
  have form : lower A t O.c=H*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have u : t*A.c+O.c*A.s=H := rfl
    have v : -t*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg hp,abs_of_nonneg kp]
    ring
  have first := mul_nonneg hp (sub_nonneg.mpr cap)
  have second := mul_nonneg kp (sub_nonneg.mpr northwest)
  have width := mul_nonneg (sub_nonneg.mpr side) (add_nonneg hp kp)
  let R := (O.c+t)*((1-A.c)-(7/20)*A.s^2)-
    (O.c-t)*A.s*(1-(7/20)*A.c)+(9/100)*A.c*(t*A.c+O.c*A.s)
  have identity : H*(2*(A.c+A.s)+(9/100)*A.c)+
      K*((47/20)*A.c-(33/20)*A.s)-H-K=t+(27/20)*O.c+R := by
    dsimp [H,K,R]
    linear_combination (2*t+(47/20)*O.c)*an.2.2
  have upper : lower A t O.c≤t+(27/20)*O.c+R := by
    linear_combination form + first + second + width + identity
  have boundaryExact : O.c*boundary O.c t=O.c+O.c*t+t-t^2 := by
    unfold boundary
    field_simp [cp.ne']
    ring
  have gap : t+(27/20)*O.c+R<boundary O.c t := by
    rcases remainder on an small with low | high
    · have product := mul_nonneg on.1
        (show 0≤(7/20)*t-(9/100)*O.c by linarith only [steep,ob.2.1])
      have weighted := mul_nonneg cp.le (sub_nonneg.mpr low)
      change O.c*((9/100)*t-R)≥0 at weighted
      have strict : 0<O.c*(boundary O.c t-(t+(27/20)*O.c+R)) := by
        nlinarith only [boundaryExact,on.2.2,spread,product,weighted]
      exact sub_pos.mp (pos_of_mul_pos_right strict cp.le)
    · have cross : O.c*t≤1/2 := by nlinarith only [on.2.2,sq_nonneg (O.c-t)]
      have weighted := mul_nonneg cp.le (sub_nonneg.mpr high)
      change O.c*((3593/9500)*t-(93/475)*O.c-R)≥0 at weighted
      have strict : 0<O.c*(boundary O.c t-(t+(27/20)*O.c+R)) := by
        nlinarith only [boundaryExact,on.2.2,spread,cross,weighted,sq_nonneg t]
      exact sub_pos.mp (pos_of_mul_pos_right strict cp.le)
  linarith only [gap,upper,face,sep]

/-- Both missing-marker faces and the complete O/A separation are
exhausted. The actual next bottom wall may now consume the shallow result. -/
theorem small_bottom (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (aMarker : A.Inside (33/20) (33/20)) (aRight : A.Inside 2 (87/50))
    (small : A.s≤2/5) (cap : A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c)
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) : t<1/5 := by
  have ob := normal_bounds on
  have cp : 0<O.c := by linarith only [ob.1]
  have oSide : 1<O.side := by rwa [same]
  have faces := corner_face O t os on oSide box oMarker oNear oFar missingCorner
  have escape : O.loU+O.side≤2*O.c-(457/500)*t ∨
      O.loV+O.side≤2*t+(457/500)*O.c := by
    by_cases upperU : O.loU+O.side≤2*O.c-(457/500)*t
    · exact Or.inl upperU
    · right
      apply le_of_not_gt
      intro upperV
      apply missingMarker
      apply (negative_bands O t 2 (457/500) os).mpr
      have marker := (negative_bands O t 1 (457/500) os).mp oMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [marker.1,marker.2.2.1,cp,on.1,upperU,upperV]
  rcases escape with upperU | upperV
  · have chord : 1-O.c<(43/500)*t := by linarith only [faces.1,upperU,oSide]
    have positive : 0<t := by nlinarith only [chord,ob.2.1]
    have weighted := mul_lt_mul_of_pos_left chord (show 0<1+O.c by linarith only [cp])
    have replace := mul_nonneg on.1 (sub_nonneg.mpr ob.2.1)
    have square : t^2<(43/250)*t := by nlinarith only [weighted,replace,on.2.2]
    have product : 0<t*(43/250-t) := by nlinarith only [square]
    have gap := pos_of_mul_pos_right product positive.le
    linarith only [gap]
  · have spread := OwnedWestBottomAngle.upper_v_spread on (lt_of_lt_of_le faces.2.2 upperV)
    rcases transverse O A t os on an same side small oNear oFar aMarker aRight cap apart
      with own | central
    · exact False.elim (own_axis_impossible O A t on an side.le small
        spread.1 spread.2 cap northwest faces.2.2 own)
    · exact False.elim (OwnedWestBottomAngle.central_axis_impossible O A t os on an
        same oSide.le spread.2 faces.2.1 oMarker northwest central)

#print axioms small_bottom
end N12Compact.CentralSteeperNegativeBottom
