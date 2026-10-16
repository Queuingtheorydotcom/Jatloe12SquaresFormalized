import Compact.Geometry.UpperRightNegativeTopReach
import Compact.Geometry.UpperRightNegativePairLongitudinalBounds
import Compact.Geometry.UpperRightNegativePairBounds

/-! The final northeast sign sector: both complete squares have negative
canonical sine. The genuine vertical farther point is retained explicitly.
Both top boundaries and every foreign-point face alternative are used. -/
namespace N12Compact.UpperRightNegativePairReach

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner C977ChainBridge

private theorem longitudinal_growth (T : OpenSquare) (s e f : ℝ)
    (sign : T.s=-s) (en : Normal e f) (tn : Normal T.c s)
    (side : 1<T.side) (box : InsideContainer T)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20)) :
    (7/2)*e-3*f<upper T e (-f)+T.side := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<e := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  let K := e*T.c+f*s
  let H := e*s-f*T.c
  let Q := (7/2)*e-3*f
  have kp : 0<K := by
    have a := mul_pos ep cp
    have b := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [a,b]
  have data := UpperRightNegativeTopReach.faces T s sign tn side marker row missingWing missingNE
  have wall := UpperRightNegativeTopReach.top_wall T s sign box
  have r := (negative_bands T s _ _ sign).mp row
  by_cases hp : 0≤H
  · have support : upper T e (-f)=K*(T.loU+T.side)+H*(T.loV+T.side) := by
      rw [upper_in_bands,sign]
      have a : e*T.c+(-f)*(-s)=K := by dsimp [K]; ring
      have b : -e*(-s)+(-f)*T.c=H := by dsimp [H]; ring
      rw [a,b,abs_of_nonneg kp.le,abs_of_nonneg hp]; ring
    rcases data.2 with low | high
    · have first := mul_nonneg kp.le (sub_nonneg.mpr low)
      have last := mul_nonneg hp (sub_nonneg.mpr data.1)
      have size := mul_pos (show 0<K+H+1 by linarith only [kp,hp]) (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.forward_lower en tn
      have identity : K*((87/50)*T.c-3*s)+H*((47/20)*(T.c+s))+K+H+1-Q=
          1+e*(T.c+s-44/25+(61/100)*s^2-(13/20)*T.c*s)+
            f*(s-T.c+13/20-(13/20)*s^2-(61/100)*T.c*s) := by
        dsimp [K,H,Q]
        linear_combination ((87/50)*e-(47/20)*f)*tn.2.2
      dsimp [Q] at identity
      clear_value K H Q
      nlinarith only [support,first,last,size,margin,identity]
    · have first := mul_nonneg kp.le
        (show 0≤s*T.loU-T.c*(T.loV+T.side)+4 by linarith only [wall])
      have last := mul_nonneg ep.le (sub_nonneg.mpr high)
      have sk := mul_nonneg tn.1 kp.le
      have size := mul_pos (show 0<e+s*K+s by linarith only [ep,sk,tn.1])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.forward_upper en tn hp
      have scaled : s*(upper T e (-f)+T.side-Q)=
          K*(s*T.loU-T.c*(T.loV+T.side)+4)+
          e*(T.loV-(3*T.c+(87/50)*s))+
          (T.side-1)*(e+s*K+s)+
          (s+e*(1-T.c-(44/25)*s+T.c*s)+f*(s^2-s)) := by
        rw [support]; dsimp [K,H,Q]
        linear_combination e*(T.loV+T.side)*tn.2.2
      have positive : 0<s*(upper T e (-f)+T.side-Q) := by
        clear_value K H Q
        nlinarith only [scaled,first,last,size,margin]
      have result := pos_of_mul_pos_right positive tn.1
      dsimp [Q] at result
      linarith only [result]
  · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
    have support : upper T e (-f)=K*(T.loU+T.side)+H*T.loV := by
      rw [upper_in_bands,sign]
      have a : e*T.c+(-f)*(-s)=K := by dsimp [K]; ring
      have b : -e*(-s)+(-f)*T.c=H := by dsimp [H]; ring
      rw [a,b,abs_of_nonneg kp.le,abs_of_nonpos hn]; ring
    rcases data.2 with low | high
    · have first := mul_nonneg kp.le (sub_nonneg.mpr low)
      have last := mul_nonneg (neg_nonneg.mpr hn)
        (show 0≤(12/5)*s+3*T.c-T.loV by linarith only [r.2.2.1])
      have size := mul_pos (show 0<K+1 by linarith only [kp]) (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.forward_row en tn
      have identity : K*((87/50)*T.c-3*s)+H*((12/5)*s+3*T.c)+K+1-Q=
          1+e*(T.c-44/25+(33/50)*s^2)+f*(s-(33/50)*T.c*s) := by
        dsimp [K,H,Q]
        linear_combination ((87/50)*e-3*f)*tn.2.2
      dsimp [Q] at identity
      clear_value K H Q
      nlinarith only [support,first,last,size,margin,identity]
    · have first := mul_nonneg kp.le
        (show 0≤s*T.loU-T.c*(T.loV+T.side)+4 by linarith only [wall])
      have last := mul_nonneg ep.le (sub_nonneg.mpr high)
      have sk := mul_nonneg tn.1 kp.le
      have sh := mul_nonneg tn.1 (neg_nonneg.mpr hn)
      have size := mul_pos (show 0<e+s*K+s-s*H by linarith only [ep,sk,sh,tn.1])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.forward_reverse_upper en tn hn
      have scaled : s*(upper T e (-f)+T.side-Q)=
          K*(s*T.loU-T.c*(T.loV+T.side)+4)+
          e*(T.loV-(3*T.c+(87/50)*s))+
          (T.side-1)*(e+s*K+s-s*H)+
          (s+e*(1-T.c-(44/25)*s+T.c*s)+f*(s^2-s)-s*H) := by
        rw [support]; dsimp [K,H,Q]
        linear_combination e*(T.loV+T.side)*tn.2.2
      have positive : 0<s*(upper T e (-f)+T.side-Q) := by
        change 0≤s+e*(1-T.c-(44/25)*s+T.c*s)+f*(s^2-s)-s*H at margin
        clear_value K H Q
        nlinarith only [scaled,first,last,size,margin]
      have result := pos_of_mul_pos_right positive tn.1
      dsimp [Q] at result
      linarith only [result]

private theorem top_longitudinal_impossible (E T : OpenSquare) (f s : ℝ)
    (eSign : E.s=-f) (tSign : T.s=-s) (en : Normal E.c f) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side) (box : InsideContainer T)
    (cap : E.loU+E.side≤(7/2)*E.c-3*f)
    (corner : E.Inside 3 3) (verticalFar : E.Inside 3 (7/2))
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3) (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : T.loU+T.side≤lower E T.c (-s)) : False := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  let K := E.c*T.c+f*s
  let H := E.c*s-f*T.c
  let Q := (7/2)*E.c-3*f
  let L := (87/50)*T.c-3*s
  have kp : 0<K := by
    have a := mul_pos ep cp
    have b := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [a,b]
  have data := UpperRightNegativeTopReach.faces T s tSign tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  have wall := UpperRightNegativeTopReach.top_wall T s tSign box
  rw [←same] at wall separator
  have ec := (negative_bands E f _ _ eSign).mp corner
  have ev := (negative_bands E f _ _ eSign).mp verticalFar
  have first := mul_nonneg kp.le (sub_nonneg.mpr cap)
  by_cases hp : 0≤H
  · have support : lower E T.c (-s)=K*E.loU-H*(E.loV+E.side) := by
      rw [lower_in_bands,eSign]
      have a : T.c*E.c+(-s)*(-f)=K := by dsimp [K]; ring
      have b : -T.c*(-f)+(-s)*E.c=-H := by dsimp [H]; ring
      rw [a,b,abs_of_nonneg kp.le,abs_of_nonpos (neg_nonpos.mpr hp)]; ring
    rw [support] at separator
    have last := mul_nonneg hp
      (show 0≤E.loV+E.side-(3*f+(7/2)*E.c) by linarith only [ev.2.2.2])
    have bound : E.side*(1+K)+T.loU-K*Q+H*(3*f+(7/2)*E.c)≤0 := by
      dsimp [Q]
      clear_value K H
      nlinarith only [separator,first,last]
    let G := 1+T.c*(E.c-44/25+(1/2)*f^2-(1/2)*E.c*f)+
      s*(f+1/2-(1/2)*f^2-(1/2)*E.c*f)
    have identity : 1+K+L-K*Q+H*(3*f+(7/2)*E.c)=G := by
      dsimp [K,H,L,Q,G]
      linear_combination (-(7/2)*(T.c-s))*en.2.2
    rcases data.2 with low | high
    · have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.reverse_parallel en tn hp
      change 0<G at margin
      dsimp [L] at identity
      clear_value K H Q L G
      nlinarith only [bound,low,size,margin,identity]
    · have scaled := mul_nonpos_of_nonneg_of_nonpos tn.1 bound
      have face := mul_nonneg cp.le (sub_nonneg.mpr high)
      have sk := mul_nonneg tn.1 (show 0≤1+K by linarith only [kp])
      have size := mul_pos (show 0<T.c+s*(1+K) by linarith only [cp,sk])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.reverse_parallel_top en tn hp
      change 0≤T.c-1+s*G at margin
      have target : T.c*(3*T.c+(87/50)*s)-s*L=3 := by
        dsimp [L]; linear_combination 3*tn.2.2
      have identityScaled := congrArg (fun z : ℝ => s*z) identity
      clear_value K H Q L G
      nlinarith only [scaled,face,size,margin,target,identityScaled,wall]
  · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
    have support : lower E T.c (-s)=K*E.loU-H*E.loV := by
      rw [lower_in_bands,eSign]
      have a : T.c*E.c+(-s)*(-f)=K := by dsimp [K]; ring
      have b : -T.c*(-f)+(-s)*E.c=-H := by dsimp [H]; ring
      rw [a,b,abs_of_nonneg kp.le,abs_of_nonneg (neg_nonneg.mpr hn)]; ring
    rw [support] at separator
    have last := mul_nonneg (neg_nonneg.mpr hn)
      (show 0≤3*f+3*E.c-E.loV by linarith only [ec.2.2.1])
    have bound : E.side*(1+K)+T.loU-K*Q+H*(3*f+3*E.c)≤0 := by
      dsimp [Q]
      clear_value K H
      nlinarith only [separator,first,last]
    let G := 1+T.c*(E.c-63/50-E.c^2/2)+s*f*(1-E.c/2)
    have identity : 1+K+L-K*Q+H*(3*f+3*E.c)=G := by
      dsimp [K,H,L,Q,G]
      linear_combination (-3*(T.c-s))*en.2.2
    rcases data.2 with low | high
    · have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.reverse_row en tn
      change 0<G at margin
      dsimp [L] at identity
      clear_value K H Q L G
      nlinarith only [bound,low,size,margin,identity]
    · have scaled := mul_nonpos_of_nonneg_of_nonpos tn.1 bound
      have face := mul_nonneg cp.le (sub_nonneg.mpr high)
      have sk := mul_nonneg tn.1 (show 0≤1+K by linarith only [kp])
      have size := mul_pos (show 0<T.c+s*(1+K) by linarith only [cp,sk])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairLongitudinalBounds.reverse_row_top en tn
      change 0≤T.c-1+s*G at margin
      have target : T.c*(3*T.c+(87/50)*s)-s*L=3 := by
        dsimp [L]; linear_combination 3*tn.2.2
      have identityScaled := congrArg (fun z : ℝ => s*z) identity
      clear_value K H Q L G
      nlinarith only [scaled,face,size,margin,target,identityScaled,wall]

private theorem corner_transverse_impossible (E T : OpenSquare) (f s : ℝ)
    (eSign : E.s=-f) (tSign : T.s=-s) (en : Normal E.c f) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side)
    (eBox : InsideContainer E) (tBox : InsideContainer T)
    (cap : E.loU+E.side≤(7/2)*E.c-3*f)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3) (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : upper T f E.c≤E.loV) : False := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  let K := E.c*T.c+f*s
  let H := E.c*s-f*T.c
  let Q := (7/2)*E.c-3*f
  let P := E.c+f
  have kp : 0<K := by
    have a := mul_pos ep cp
    have b := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [a,b]
  have pp : 0<P := by dsimp [P]; linarith only [ep,en.1]
  have data := UpperRightNegativeTopReach.faces T s tSign tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  have eWall := UpperRightNegativeTopReach.top_wall E f eSign eBox
  have tWall := UpperRightNegativeTopReach.top_wall T s tSign tBox
  have r := (negative_bands T s _ _ tSign).mp row
  have first := mul_nonneg en.1 (sub_nonneg.mpr cap)
  have last := mul_nonneg ep.le (sub_nonneg.mpr separator)
  have bound : E.c*upper T f E.c+E.side*P-4-f*Q≤0 := by
    dsimp [P,Q]; nlinarith only [eWall,first,last]
  by_cases hp : 0≤H
  · have support : upper T f E.c=-H*T.loU+K*(T.loV+T.side) := by
      rw [upper_in_bands,tSign]
      have a : f*T.c+E.c*(-s)=-H := by dsimp [H]; ring
      have b : -f*(-s)+E.c*T.c=K := by dsimp [K]; ring
      rw [a,b,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg kp.le]; ring
    have low := mul_nonneg (mul_nonneg ep.le kp.le) (sub_nonneg.mpr data.1)
    have rowBound := mul_nonneg (mul_nonneg ep.le hp)
      (show 0≤(12/5)*T.c-3*s-T.loU by linarith only [r.1])
    have prod := mul_nonneg ep.le kp.le
    have size := mul_pos (show 0<E.c*K+P by linarith only [prod,pp]) (sub_pos.mpr side)
    have margin := UpperRightNegativePairBounds.plus en tn
    have identity : E.c*(-H*((12/5)*T.c-3*s)+K*((47/20)*(T.c+s)))+
        E.c*K+P-4-f*Q=
        E.c+f-33/20+(13/20)*f^2+
        E.c^2*(T.c+(13/20)*s^2-(1/20)*T.c*s)+
        E.c*f*(s-11/10-(1/20)*s^2-(13/20)*T.c*s) := by
      dsimp [K,H,P,Q]
      linear_combination (47/20)*en.2.2+
        ((47/20)*E.c^2+(12/5)*E.c*f)*tn.2.2
    rw [←same] at support
    rw [support] at bound
    clear_value K H Q P
    nlinarith only [bound,support,low,rowBound,size,margin,identity]
  · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
    have order : E.c*s≤f*T.c := by dsimp [H] at hn; linarith only [hn]
    have support : upper T f E.c=-H*(T.loU+T.side)+K*(T.loV+T.side) := by
      rw [upper_in_bands,tSign]
      have a : f*T.c+E.c*(-s)=-H := by dsimp [H]; ring
      have b : -f*(-s)+E.c*T.c=K := by dsimp [K]; ring
      rw [a,b,abs_of_nonneg (neg_nonneg.mpr hn),abs_of_nonneg kp.le]; ring
    rcases data.2 with low | high
    · have first := mul_nonneg (mul_nonneg ep.le (neg_nonneg.mpr hn)) (sub_nonneg.mpr low)
      have last := mul_nonneg (mul_nonneg ep.le kp.le) (sub_nonneg.mpr data.1)
      have prod := mul_nonneg ep.le (show 0≤K-H by linarith only [kp,hn])
      have size := mul_pos (show 0<E.c*(K-H)+P by linarith only [prod,pp])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairBounds.minus en tn order
      have identity : E.c*(-H*((87/50)*T.c-3*s)+K*((47/20)*(T.c+s)))+
          E.c*(K-H)+P-4-f*Q=
          E.c+f-33/20+(13/20)*f^2+
          E.c^2*(T.c-s+(13/20)*s^2+(61/100)*T.c*s)+
          E.c*f*(T.c+s-44/25+(61/100)*s^2-(13/20)*T.c*s) := by
        dsimp [K,H,P,Q]
        linear_combination (47/20)*en.2.2+
          ((47/20)*E.c^2+(87/50)*E.c*f)*tn.2.2
      rw [←same] at support
      rw [support] at bound
      clear_value K H Q P
      nlinarith only [bound,support,first,last,size,margin,identity]
    · have sine : 0<s := by
        apply lt_of_not_ge
        intro no
        have zero : s=0 := by linarith only [no,tn.1]
        have cosine : T.c=1 := by nlinarith only [tn.2.2,zero,cp]
        rw [←same] at tWall
        rw [zero,cosine] at tWall high
        linarith only [tWall,high,side]
      have wallSlack := mul_nonneg (mul_nonneg ep.le (neg_nonneg.mpr hn))
        (show 0≤s*T.loU-T.c*(T.loV+T.side)+4 by linarith only [tWall])
      have faceSlack := mul_nonneg (mul_nonneg ep.le en.1) (sub_nonneg.mpr high)
      have ef := mul_nonneg ep.le en.1
      have esh := mul_nonneg (mul_nonneg ep.le tn.1) (neg_nonneg.mpr hn)
      have sp := mul_pos sine pp
      have size := mul_pos (show 0<E.c*f-E.c*s*H+s*P by linarith only [ef,esh,sp])
        (sub_pos.mpr side)
      have margin := UpperRightNegativePairBounds.upper en tn order
      have scaled : s*(E.c*upper T f E.c+T.side*P-4-f*Q)=
          E.c*(-H)*(s*T.loU-T.c*(T.loV+T.side)+4)+
          E.c*f*(T.loV-(3*T.c+(87/50)*s))+
          (T.side-1)*(E.c*f-E.c*s*H+s*P)+
          (E.c*f*(1-T.c)+s*(E.c+f-f^2+
            E.c*f*(T.c-44/25)-E.c^2*s)) := by
        rw [support]; dsimp [K,H,P,Q]
        linear_combination E.c*f*(T.loV+T.side)*tn.2.2+4*s*en.2.2
      rw [←same] at scaled wallSlack
      have negative := mul_nonpos_of_nonneg_of_nonpos tn.1 bound
      clear_value K H Q P
      nlinarith only [scaled,wallSlack,faceSlack,size,margin,negative]

theorem point (E T : OpenSquare) (f s : ℝ)
    (eSign : E.s=-f) (tSign : T.s=-s) (en : Normal E.c f) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side)
    (eBox : InsideContainer E) (tBox : InsideContainer T)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (verticalFar : E.Inside 3 (7/2))
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3) (missingNE : ¬T.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)) : E.Inside (7/2) 3 := by
  by_contra missing
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  have ec := (negative_bands E f _ _ eSign).mp corner
  have eo := (negative_bands E f _ _ eSign).mp outward
  have ev := (negative_bands E f _ _ eSign).mp verticalFar
  have cap : E.loU+E.side≤(7/2)*E.c-3*f := by
    apply le_of_not_gt
    intro high
    apply missing
    apply (negative_bands E f _ _ eSign).mpr
    exact ⟨by nlinarith only [eo.1,ep],by linarith only [high],
      by nlinarith only [ec.2.2.1,en.1],by nlinarith only [ev.2.2.2,en.2.1]⟩
  have data := UpperRightNegativeTopReach.faces T s tSign tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  have axes := CongruentSAT.faceSeparation_of_disjoint E T same apart
  change pairRadius E T≤|E.c*(centerX T-centerX E)+E.s*(centerY T-centerY E)| ∨
    pairRadius E T≤|-E.s*(centerX T-centerX E)+E.c*(centerY T-centerY E)| ∨
    pairRadius T E≤|T.c*(centerX T-centerX E)+T.s*(centerY T-centerY E)| ∨
    pairRadius T E≤|-T.s*(centerX T-centerX E)+T.c*(centerY T-centerY E)| at axes
  have separateAxis (nx ny radius : ℝ)
      (identity : supportRadius E nx ny+supportRadius T nx ny=radius)
      (sep : radius≤|nx*(centerX T-centerX E)+ny*(centerY T-centerY E)|) :=
    separated E T nx ny (by rwa [identity])
  rcases axes with eu | evAxis | tu | tv
  · have sep := separateAxis _ _ _ (parallel_radius E T) eu
    rw [eSign] at sep
    rcases sep with reverse | forward
    · have normal : E.c^2+(-f)^2=1 := by nlinarith only [en.2.2]
      have a := strict_bounds E _ _ E.c (-f) normal corner
      have b := strict_bounds T _ _ E.c (-f) normal marker
      nlinarith only [reverse,a.2,b.1,ep,en.1]
    · have own : lower E E.c (-f)=E.loU := by simpa only [eSign] using (ownU E).1
      rw [own] at forward
      have growth := longitudinal_growth T s E.c f tSign en tn
        (by simpa only [←same] using side) tBox marker row missingWing missingNE
      rw [←same] at growth
      linarith only [forward,growth,cap]
  · have sep := separateAxis _ _ _ (transverse_radius E T) evAxis
    rw [eSign,neg_neg] at sep
    rcases sep with reverse | forward
    · have normal : f^2+E.c^2=1 := by nlinarith only [en.2.2]
      have a := strict_bounds E _ _ f E.c normal verticalFar
      have b := strict_bounds T _ _ f E.c normal row
      nlinarith only [reverse,a.2,b.1,ep,en.1]
    · have own : lower E f E.c=E.loV := by simpa only [eSign,neg_neg] using (ownV E).1
      rw [own] at forward
      exact corner_transverse_impossible E T f s eSign tSign en tn same side
        eBox tBox cap marker row missingWing missingNE forward
  · have identity : supportRadius E T.c T.s+supportRadius T T.c T.s=pairRadius T E := by
      rw [add_comm]; exact parallel_radius T E
    have sep := separateAxis _ _ _ identity tu
    rw [tSign] at sep
    rcases sep with reverse | forward
    · have normal : T.c^2+(-s)^2=1 := by nlinarith only [tn.2.2]
      have a := strict_bounds E _ _ T.c (-s) normal corner
      have b := strict_bounds T _ _ T.c (-s) normal marker
      nlinarith only [reverse,a.2,b.1,cp,tn.1]
    · have own : upper T T.c (-s)=T.loU+T.side := by simpa only [tSign] using (ownU T).2
      rw [own] at forward
      exact top_longitudinal_impossible E T f s eSign tSign en tn same side tBox
        cap corner verticalFar marker row missingWing missingNE forward
  · have identity : supportRadius E (-T.s) T.c+supportRadius T (-T.s) T.c=pairRadius T E := by
      rw [add_comm]; exact transverse_radius T E
    have sep := separateAxis _ _ _ identity tv
    rw [tSign,neg_neg] at sep
    rcases sep with forward | reverse
    · have normal : s^2+T.c^2=1 := by nlinarith only [tn.2.2]
      have a := strict_bounds E _ _ s T.c normal corner
      have b := strict_bounds T _ _ s T.c normal row
      nlinarith only [forward,a.2,b.1,tn.1]
    · have own : upper T s T.c=T.loV+T.side := by simpa only [tSign,neg_neg] using (ownV T).2
      rw [own,←same] at reverse
      have normal : s^2+T.c^2=1 := by nlinarith only [tn.2.2]
      have a := strict_bounds E _ _ s T.c normal corner
      nlinarith only [reverse,a.1,data.1,side,tb.2.2.2.2.2]

end N12Compact.UpperRightNegativePairReach
