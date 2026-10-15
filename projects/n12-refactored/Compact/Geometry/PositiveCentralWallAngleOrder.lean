import Compact.Geometry.PositiveCentralTransverse
import Compact.Geometry.C696PositiveCorner
import Compact.Geometry.NegativeWallAngleOrder

/-! A continuous angle-order obstruction for the actual bottom, central,
and negative left-wall squares. The strict central point (1,2) remains
an explicit premise; this file does not assert the full corner closure. -/
namespace N12Compact.PositiveCentralWallAngleOrder

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

/-- The common two-angle margin. The proof uses monotonicity of one
cubic on a single interval, certified by two elementary factorizations. -/
theorem margin {C S d t : ℝ}
    (an : Normal C S) (wn : Normal d t)
    (hd : 4/5≤d) (ht : t≤3/5) (orderC : d≤C) (orderS : S≤t) :
    (d^2-(d+t-1))*(1+C*S)+d*t*(2-S^2-(d+t-1))-
      d*((d+t)*C+(d-t)*S) ≤ 0 := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have cd : 0≤1-C := sub_nonneg.mpr ab.2.1
  have dd : 0≤1-d := sub_nonneg.mpr wb.2.1
  have dp : 0<1+d := by linarith only [hd]
  let z := d+t-1
  let R := d^2-z
  let B := d^2*(1-t)
  let E := R*(1+C*S)+d*t*(2-S^2-z)-d*((d+t)*C+(d-t)*S)
  let E0 := -z^2*(1+z)/2
  let delta := (1-C)*(d^2-d*t*C-R*S)+S*z^2/2
  let G := fun x : ℝ => x^2*(B-R*x)+(1+d)*x*z^2/2
  have rp : 0≤R := by
    dsimp [R,z]
    nlinarith only [ht,sq_nonneg (d-1/2)]
  have hp : 0≤2*B-3*R*t := by
    have first := mul_nonneg wn.1 (show 0≤d-4/5 by linarith only [hd])
    have second := mul_nonneg (sq_nonneg (t-1/2))
      (show 0≤t+1 by linarith only [wn.1])
    have third := mul_nonneg (sub_nonneg.mpr ht)
      (show 0≤5/4-t by linarith only [ht])
    have identity :
        2*B-3*R*t =
          3*t*(d-4/5)+5*(t-1/2)^2*(t+1)+(3/5-t)*(5/4-t) := by
      dsimp [B,R,z]
      linear_combination (2-5*t)*wn.2.2
    nlinarith only [first,second,third,identity]
  have bs : 0≤B-R*S := by
    have rt := mul_nonneg rp wn.1
    have replacement := mul_nonneg rp (sub_nonneg.mpr orderS)
    nlinarith only [hp,rt,replacement]
  have changeC := mul_nonneg (mul_nonneg cd (mul_nonneg (show 0≤d by linarith only [hd]) wn.1))
    (sub_nonneg.mpr orderC)
  have denominator : (1+d)*(1-C)≤S^2 := by
    have replacement := mul_nonneg cd (sub_nonneg.mpr orderC)
    nlinarith only [replacement,an.2.2]
  have deltaBound : (1+d)*delta≤G S := by
    have replacement := mul_nonneg (le_of_lt dp) changeC
    have denominatorBound := mul_nonneg bs (sub_nonneg.mpr denominator)
    dsimp [delta,G,B] at *
    nlinarith only [replacement,denominatorBound]
  have bracket : 0≤B*(t+S)-R*(t^2+t*S+S^2) := by
    have first := mul_nonneg
      (show 0≤t+S by linarith only [wn.1,an.1]) hp
    have second := mul_nonneg rp
      (mul_nonneg (sub_nonneg.mpr orderS)
        (show 0≤t+2*S by linarith only [wn.1,an.1]))
    nlinarith only [first,second]
  have increasing : G S≤G t := by
    have first := mul_nonneg (sub_nonneg.mpr orderS) bracket
    have second := mul_nonneg (sub_nonneg.mpr orderS)
      (mul_nonneg dp.le (sq_nonneg z))
    dsimp [G]
    nlinarith only [first,second]
  have short : 1-d≤t/2 := by
    by_contra no
    have positive := mul_pos
      (show 0<1-(d+t/2) by linarith only [no])
      (show 0<1+(d+t/2) by linarith only [hd,wn.1])
    have tangent := mul_nonneg wn.1
      (show 0≤d-(3/4)*t by linarith only [hd,ht])
    nlinarith only [positive,tangent,wn.2.2]
  have endpoint : (1-d)*(1-d-t*(2*d^2-2*d+1))≤0 := by
    have square := mul_nonneg wn.1 (sq_nonneg (d-1/2))
    have inner : 1-d-t*(2*d^2-2*d+1)≤0 := by
      nlinarith only [short,square]
    exact mul_nonpos_of_nonneg_of_nonpos dd inner
  have decomposition : E=E0+delta := by
    dsimp [E,E0,delta,R,z]
    linear_combination -d*t*an.2.2-
      ((2-d-t+S)/2)*wn.2.2
  have endpointIdentity :
      (1+d)*E0+G t=(1+d)*(1-d)*(1-d-t*(2*d^2-2*d+1)) := by
    dsimp [E0,G,B,R,z]
    linear_combination
      ((1+d)*(1-3*d/2)+d^2*(1-t)-(d^2-(d+t-1))*t)*wn.2.2
  have scaledEndpoint := mul_nonpos_of_nonneg_of_nonpos dp.le endpoint
  have scaledDecomposition := congrArg (fun x : ℝ => (1+d)*x) decomposition
  have scaled : (1+d)*E≤0 := by
    nlinarith only [deltaBound,increasing,scaledDecomposition,endpointIdentity,scaledEndpoint]
  have result : E≤0 := by
    exact nonpos_of_mul_nonpos_right scaled dp
  exact result

private theorem ordered {p q d t : ℝ} (on : Normal p q) (wn : Normal d t)
    (order : t≤q) : p≤d ∧ d+t≤p+q ∧ p*t≤d*q := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have squares := mul_nonneg (sub_nonneg.mpr order) (add_nonneg on.1 wn.1)
  have cosine : p≤d := by
    by_contra no
    have bad := mul_pos
      (show 0<p-d by linarith only [no])
      (show 0<p+d by linarith only [ob.1,wb.1])
    nlinarith only [bad,squares,on.2.2,wn.2.2]
  have product := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤p+d-q-t by linarith only [on.2.1,wn.2.1])
  have sum : d+t≤p+q := by
    have identity :
        (p+d)*(p+q-d-t)=(q-t)*(p+d-q-t) := by
      linear_combination on.2.2-wn.2.2
    have scaled : 0≤(p+d)*(p+q-d-t) := by linarith only [identity,product]
    have gap := nonneg_of_mul_nonneg_left scaled
      (show 0<p+d by linarith only [ob.1,wb.1])
    linarith only [gap]
  have first := mul_nonneg on.1 (sub_nonneg.mpr cosine)
  have second := mul_nonneg (show 0≤p by linarith only [ob.1]) (sub_nonneg.mpr order)
  exact ⟨cosine,sum,by nlinarith only [first,second]⟩

/-- Both genuine O/A support alternatives have the same relaxed
obstruction. The side and all three actual container-wall inequalities
are retained; no virtual coordinate wall is introduced. -/
theorem support_obstruction {p q C S d t a ou ov au av wu wv : ℝ}
    (on : Normal p q) (an : Normal C S) (wn : Normal d t)
    (side : 1<a) (small : t≤3/5) (centralOrder : S≤t) (outerOrder : t≤q)
    (bottom : 0≤q*ou+p*ov) (bottomCap : ou+a≤2*p+q)
    (centerCap : au+a≤2*(C+S))
    (wallTop : wv+a≤t+3*d)
    (wall : a*(d+t)≤d*(wu+a)+t*(wv+a))
    (oa : ov+a≤-(q*C-p*S)*(au+a)+(p*C+q*S)*av ∨
      (q*C-p*S)*(ou+a)+(p*C+q*S)*(ov+a)≤av)
    (aw : wu+a≤(C*d-S*t)*au-(S*d+C*t)*(av+a)) : False := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0<C := by linarith only [ab.1]
  have dp : 0<d := by linarith only [wb.1]
  have large : 4/5≤d := by
    by_contra no
    have dsq := mul_pos (show 0<4/5-d by linarith only [no])
      (show 0<4/5+d by linarith only [dp])
    have tsq := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤3/5+t by linarith only [wn.1])
    nlinarith only [dsq,tsq,wn.2.2]
  have outer := ordered on wn outerOrder
  have inner := ordered wn an centralOrder
  have allOrder : S≤q := le_trans centralOrder outerOrder
  have fullOrder := ordered on an allOrder
  let K := p*C+q*S
  let D := q*C-p*S
  let k := C*d-S*t
  let h := S*d+C*t
  let J := p*d-q*t
  let U := 2*(C+S)-1
  let Uo := 2*p+q
  let B := (p+q-q*Uo)/p
  let V := 1+D*Uo+K*B
  let T := d*(1+C*(d+t)-2*S)+S*t*(d+t-1)
  have kp : 0<K := by
    have first := mul_pos pp cp
    have second := mul_nonneg on.1 an.1
    dsimp [K]
    linarith only [first,second]
  have dnon : 0≤D := by dsimp [D]; linarith only [fullOrder.2.2]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dp.le) (mul_nonneg cp.le wn.1)
  have km : 0<k := by
    have first := mul_pos cp (show 0<d-t by linarith only [large,small])
    have second := mul_nonneg wn.1 (sub_nonneg.mpr an.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have jp : 0<J := by
    have first := mul_pos pp (show 0<d-t by linarith only [large,small])
    have second := mul_nonneg wn.1 (sub_nonneg.mpr on.2.1)
    dsimp [J]
    nlinarith only [first,second]
  have pB : p*B=p+q-q*Uo := by dsimp [B]; field_simp [pp.ne']
  have normRelative : K^2+D^2=1 := by
    dsimp [K,D]
    linear_combination (C^2+S^2)*on.2.2+an.2.2
  have relative : K*k-D*h=J := by
    dsimp [K,D,k,h,J]
    linear_combination (p*d-q*t)*an.2.2
  have rotation : p*D-q*K=-S := by
    dsimp [K,D]
    linear_combination -S*on.2.2
  have strictBottom : B<ov+a := by
    have cap := mul_nonneg on.1 (sub_nonneg.mpr bottomCap)
    have width := mul_pos (sub_pos.mpr side)
      (show 0<p+q by linarith only [pp,on.1])
    have scaled : 0<p*(ov+a-B) := by
      dsimp [Uo] at pB
      nlinarith only [bottom,cap,width,pB]
    have gap := pos_of_mul_pos_right scaled pp.le
    linarith only [gap]
  have virtualX : p*Uo-q*B≤2 := by
    have first := mul_nonneg (mul_nonneg pp.le on.1) (sub_nonneg.mpr ob.2.1)
    have second := mul_nonneg (sq_nonneg q)
      (show 0≤1-q by linarith only [on.2.1,ob.2.1])
    have identity : p*(2-(p*Uo-q*B))=p*q*(1-p)+q^2*(1-q) := by
      dsimp [Uo] at *
      linear_combination q*pB-2*p*on.2.2
    have scaled : 0≤p*(2-(p*Uo-q*B)) := by
      nlinarith only [first,second,identity]
    have gap := nonneg_of_mul_nonneg_left scaled pp
    linarith only [gap]
  have virtualY : q*Uo+p*B≤2 := by
    linarith only [pB,ob.2.2.2.2.2]
  have virtualProjection : K*Uo-D*B≤2*(C+S) := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr virtualX)
    have second := mul_nonneg an.1 (sub_nonneg.mpr virtualY)
    dsimp [K,D]
    nlinarith only [first,second]
  have reduced : wu+a<k*U-h*V := by
    rcases oa with own | central
    · change ov+a≤-D*(au+a)+K*av at own
      have lower : B+D*(au+a)+K*a<K*(av+a) := by
        nlinarith only [own,strictBottom]
      have scaledSep := mul_le_mul_of_nonneg_left aw kp.le
      change K*(wu+a)≤K*(k*au-h*(av+a)) at scaledSep
      have scaledLower := mul_nonneg hp (sub_nonneg.mpr lower.le)
      have cap := mul_nonneg jp.le (sub_nonneg.mpr centerCap)
      have width := mul_pos (sub_pos.mpr side)
        (show 0<J+h*(D+K) by
          have nonnegative := mul_nonneg hp (show 0≤D+K by linarith only [dnon,kp])
          linarith only [jp,nonnegative])
      have relativeScaled := congrArg (fun x : ℝ => au*x) relative
      have first : K*(wu+a)<J*U-h*(B+D+K) := by
        dsimp [U]
        nlinarith only [scaledSep,scaledLower,cap,width,relativeScaled]
      have comparison := mul_nonneg (mul_nonneg hp dnon)
        (sub_nonneg.mpr virtualProjection)
      have identity :
          K*(k*U-h*V)-(J*U-h*(B+D+K))=
            h*D*(2*(C+S)-(K*Uo-D*B)) := by
        dsimp [U,V]
        linear_combination (2*(C+S)-1)*relative-h*B*normRelative
      have scaled : 0<K*((k*U-h*V)-(wu+a)) := by
        nlinarith only [first,comparison,identity]
      have gap := pos_of_mul_pos_right scaled kp.le
      linarith only [gap]
    · change D*(ou+a)+K*(ov+a)≤av at central
      have cap := mul_nonneg an.1 (sub_nonneg.mpr bottomCap)
      have wall := mul_nonneg kp.le bottom
      have width := mul_pos (sub_pos.mpr side)
        (mul_pos kp (show 0<p+q by linarith only [pp,on.1]))
      have identity :
          p*(D*(ou+a)+K*(ov+a)-(D*Uo+K*B))=
            K*(q*ou+p*ov)+a*p*(D+K)-S*ou-p*(D*Uo+K*B) := by
        linear_combination ou*rotation
      have virtualIdentity : p*(D*Uo+K*B)=K*(p+q)-S*Uo := by
        linear_combination Uo*rotation+K*pB
      have sumIdentity : p*(D+K)+S=K*(p+q) := by
        linarith only [rotation]
      have sumScaled := congrArg (fun x : ℝ => a*x) sumIdentity
      have scaled : 0<p*(av-(D*Uo+K*B)) := by
        have sep := mul_le_mul_of_nonneg_left central pp.le
        dsimp [Uo] at cap
        nlinarith only [sep,cap,wall,width,identity,virtualIdentity,sumScaled]
      have gap := pos_of_mul_pos_right scaled pp.le
      have vgap : V<av+a := by dsimp [V]; linarith only [gap,side]
      have vweight := mul_nonneg hp (sub_nonneg.mpr vgap.le)
      have uweight := mul_nonneg km.le (sub_nonneg.mpr centerCap)
      have width := mul_pos km (sub_pos.mpr side)
      dsimp [U]
      nlinarith only [aw,vweight,uweight,width]
  have virtualIdentity :
      p*V=p*(1+C*(p+q)-2*S)+S*q*(p+q-1) := by
    dsimp [V]
    linear_combination Uo*rotation+K*pB
  have monotone : T≤d*V := by
    have first := mul_nonneg (mul_nonneg (mul_nonneg pp.le dp.le) cp.le)
      (sub_nonneg.mpr outer.2.1)
    have second := mul_nonneg (mul_nonneg (mul_nonneg an.1 dp.le) on.1)
      (sub_nonneg.mpr outer.2.1)
    have third := mul_nonneg an.1
      (mul_nonneg (sub_nonneg.mpr outer.2.2)
        (show 0≤d+t-1 by linarith only [wb.2.2.2.2.1]))
    have identity :
        p*(d*V-T)=p*d*C*((p+q)-(d+t))+
          S*d*q*((p+q)-(d+t))+S*(d*q-p*t)*(d+t-1) := by
      dsimp [T]
      linear_combination d*virtualIdentity
    have scaled : 0≤p*(d*V-T) := by
      nlinarith only [first,second,third,identity]
    have gap := nonneg_of_mul_nonneg_left scaled pp
    linarith only [gap]
  have supportBound := mul_lt_mul_of_pos_left reduced dp
  have replaced := mul_nonneg hp (sub_nonneg.mpr monotone)
  have top := mul_nonneg wn.1 (sub_nonneg.mpr wallTop)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<d+t by linarith only [dp,wn.1])
  have necessary : 0<d*k*U-h*T-(d+t-t^2-3*d*t) := by
    nlinarith only [supportBound,replaced,top,wall,width]
  have identity :
      d*k*U-h*T-(d+t-t^2-3*d*t)=
        (d^2-(d+t-1))*(1+C*S)+d*t*(2-S^2-(d+t-1))-
          d*((d+t)*C+(d-t)*S) := by
    dsimp [k,h,U,T]
    linear_combination (2*d^2-d*t*(d+t))*an.2.2+
      (1-(d+t-1)*C*S)*wn.2.2
  have impossible := margin an wn large small inner.1 centralOrder
  linarith only [necessary,identity,impossible]

/-- The full original support premises force the negative wall tilt to
exceed the positive bottom tilt. Both O/A separating axes are covered.
The central point (1,2) remains an explicit premise. -/
theorem angle_order (O A W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (an : Normal A.c A.s) (wn : Normal W.c t)
    (ws : W.s=-t) (sameOA : O.side=A.side) (sameAW : A.side=W.side)
    (side : 1<A.side) (sideCap : A.side≤1001/1000)
    (oBox : InsideContainer O) (wBox : InsideContainer W)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (oMissing : ¬O.Inside 1 1) (oMissingNext : ¬O.Inside 2 (457/500))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aLeft : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (aWest : A.Inside 1 2)
    (aMissingNW : ¬A.Inside (33/20) (47/20))
    (aForeignLow : ¬A.Inside 1 (8/5))
    (centerCap : A.loU+A.side≤2*(A.c+A.s))
    (wMarker : W.Inside (457/500) 2) (wPoint : W.Inside 1 (113/50))
    (wMissingTop : ¬W.Inside (457/500) 3)
    (wMissingFar : ¬W.Inside (19/25) (187/100))
    (apartOA : ∀ x y, ¬ (O.Inside x y ∧ A.Inside x y))
    (apartAW : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) : O.s<t := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  have dc : 0<W.c := by linarith only [wb.1]
  have sideO : 1<O.side := by rwa [sameOA]
  have sideW : 1<W.side := by rwa [←sameAW]
  have centralOrder := NegativeWallAngleOrder.angle_order A W t an wn ws sameAW
    side sideCap centerCap aWest aLeft aLow aMissingNW aForeignLow wBox
    wMarker wPoint wMissingTop wMissingFar apartAW
  have wMissing : ¬W.Inside 1 2 := fun w => apartAW 1 2 ⟨aWest,w⟩
  obtain ⟨_,wTop,wWall⟩ := LeftWallNegativeFaces.faces W t ws wn sideW wBox
    wMarker wPoint wMissing wMissingTop
  have small := (LeftWallNegativeFaces.lower_face_and_tilt W t ws wn sideW wBox
    wMarker wPoint wMissing wMissingTop wMissingFar).2
  obtain ⟨_,_,oCap,oWall,_⟩ := C696PositiveCorner.corner_faces O on sideO oBox
    oMarker oNear oMissing oMissingNext
  have oa := PositiveCentralTransverse.alternatives O A oc
    (by rw [abs_of_nonneg on.1]; exact on.2.1) an sameOA side oNear oFar
    aP aD aLeft aLow centerCap apartOA
  have aw := CentralLeftWallNegative.wall_axis A W t an wn ws sameAW sideW
    sideCap aWest aLow wBox wMarker wPoint wMissingTop wMissingFar apartAW
  by_contra no
  have outerOrder : t≤O.s := le_of_not_gt no
  have relativeOrder := ordered on an (le_trans centralOrder.le outerOrder)
  let K := O.c*A.c+O.s*A.s
  let D := O.s*A.c-O.c*A.s
  let k := A.c*W.c-A.s*t
  let h := A.s*W.c+A.c*t
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg oc.le ac.le) (mul_nonneg on.1 an.1)
  have dnon : 0≤D := by dsimp [D]; linarith only [relativeOrder.2.2]
  have km : 0≤k := by
    have first := mul_nonneg dc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dc.le) (mul_nonneg ac.le wn.1)
  have lowerA : lower A (-O.s) O.c=-D*(A.loU+A.side)+K*A.loV := by
    rw [lower_in_bands]
    have first : -O.s*A.c+O.c*A.s=-D := by dsimp [D]; ring
    have second : -(-O.s)*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [first,second,abs_of_nonpos (neg_nonpos.mpr dnon),abs_of_nonneg kp]
    ring
  have upperO : upper O (-A.s) A.c=D*(O.loU+O.side)+K*(O.loV+O.side) := by
    rw [upper_in_bands]
    have first : -A.s*O.c+A.c*O.s=D := by dsimp [D]; ring
    have second : -(-A.s)*O.s+A.c*O.c=K := by dsimp [K]; ring
    rw [first,second,abs_of_nonneg dnon,abs_of_nonneg kp]
    ring
  have lowerWall : lower A W.c W.s=k*A.loU-h*(A.loV+A.side) := by
    rw [lower_in_bands,ws]
    have first : W.c*A.c+(-t)*A.s=k := by dsimp [k]; ring
    have second : -W.c*A.s+(-t)*A.c=-h := by dsimp [h]; ring
    rw [first,second,abs_of_nonneg km,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  rw [lowerA,upperO,sameOA] at oa
  rw [lowerWall,←sameAW] at aw
  rw [sameOA] at oCap
  rw [←sameAW] at wTop wWall
  have bottomCap : O.loU+A.side≤2*O.c+O.s := by
    nlinarith only [oCap,on.1]
  have wallTop : W.loV+A.side≤t+3*W.c := by
    nlinarith only [wTop,wn.1]
  exact support_obstruction on an wn side small.le centralOrder.le outerOrder
    oWall bottomCap centerCap wallTop wWall oa aw

end N12Compact.PositiveCentralWallAngleOrder
