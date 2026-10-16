import Compact.Geometry.UpperRightCornerTopLongitudinal
import Compact.Geometry.UpperRightNegativeTopReach

/-! The negative-corner/positive-top sector. The genuine vertical farther
point removes the second escape face of the horizontal target. It is
supplied separately by the already proved diagonal corner reach. -/
namespace N12Compact.UpperRightNegativeCornerPositiveTop

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner UpperRightCornerLongitudinalBounds C977ChainBridge

private theorem coefficient {c s : ℝ} (tn : Normal c s) :
    -(4/5)≤c-9/5+(7/10)*s^2 ∧ -(3/8)≤-s+(7/10)*c*s := by
  have b := normal_bounds tn
  have product := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(7/10)*c-3/10 by linarith only [b.1])
  have sine : s≤5/7 := by linarith only [tn.2.1,b.2.2.2.2.2]
  have mixed := mul_nonneg tn.1 (sub_nonneg.mpr b.1)
  exact ⟨by nlinarith only [product,tn.2.2],by nlinarith only [mixed,sine]⟩

private theorem first_margin {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<1+e*(c-9/5+(7/10)*s^2)+f*(-s+(7/10)*c*s) := by
  have eb := normal_bounds en
  have coeff := coefficient tn
  have first := mul_nonneg (show 0≤e by linarith only [eb.1]) (sub_nonneg.mpr coeff.1)
  have last := mul_nonneg en.1 (sub_nonneg.mpr coeff.2)
  have disk := disk_margin en (show (4/5 : ℝ)^2+(3/8)^2<1 by norm_num)
  nlinarith only [first,last,disk]

private theorem second_margin {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<1-(13/10)*c+(e*c-f*s)*(1-e/2) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have chord := mul_nonneg (sub_nonneg.mpr eb.1) (sub_nonneg.mpr eb.2.1)
  have slope : 91/200≤e*(1-e/2) := by nlinarith only [chord,eb.1]
  have difference := mul_nonneg (mul_nonneg (sub_nonneg.mpr en.2.1) tn.1)
    (show 0≤1-e/2 by linarith only [eb.2.1])
  have weighted := mul_nonneg (sub_nonneg.mpr tn.2.1) (sub_nonneg.mpr slope)
  have disk := disk_margin tn (show (169/200 : ℝ)^2+(91/200)^2<1 by norm_num)
  nlinarith only [difference,weighted,disk]

private theorem third_margin {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤e+f-1+e*f*(c-9/5+(7/10)*s^2)+e^2*s*(1-(7/10)*c) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ef := mul_nonneg (show 0≤e by linarith only [eb.1]) en.1
  have coeff := coefficient tn
  have first := mul_nonneg ef (sub_nonneg.mpr coeff.1)
  have last := mul_nonneg (mul_nonneg (sq_nonneg e) tn.1)
    (show 0≤1-(7/10)*c by linarith only [tb.2.1])
  have arc := UpperRightNegativeTopBounds.arc en
  nlinarith only [first,last,arc,ef]

private theorem fourth_margin {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<c*(1/2+f-f*(e+f)/2)+s*(e-11/10+f*(f-e)/2) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  let A := 1/2+f-f*(e+f)/2
  let B := e-11/10+f*(f-e)/2
  have product := mul_nonneg en.1
    (show 0≤1-(e+f)/2 by linarith only [eb.2.2.2.2.2])
  have aBound : 1/2≤A := by dsimp [A]; nlinarith only [product]
  have ef : e*f≤1/2 := by nlinarith only [en.2.2,sq_nonneg (e-f)]
  have arc := UpperRightNegativeTopBounds.arc en
  have sum : 3/10≤A+B := by dsimp [A,B]; nlinarith only [arc,ef]
  have first := mul_nonneg (sub_nonneg.mpr tn.2.1)
    (show 0≤A-3/10 by linarith only [aBound])
  have last := mul_nonneg tn.1 (sub_nonneg.mpr sum)
  change 0<c*A+s*B
  clear_value A B
  nlinarith only [first,last,tb.1]

theorem point (E T : OpenSquare) (f : ℝ) (sign : E.s=-f)
    (en : Normal E.c f) (tn : Normal T.c T.s)
    (same : E.side=T.side) (side : 1<E.side) (box : InsideContainer E)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (verticalFar : E.Inside 3 (7/2))
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)) : E.Inside (7/2) 3 := by
  by_contra missing
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  have ec := (negative_bands E f _ _ sign).mp corner
  have eo := (negative_bands E f _ _ sign).mp outward
  have ev := (negative_bands E f _ _ sign).mp verticalFar
  have cap : E.loU+E.side≤(7/2)*E.c-3*f := by
    apply le_of_not_gt
    intro high
    apply missing
    apply (negative_bands E f _ _ sign).mpr
    exact ⟨by nlinarith only [eo.1,ep],by linarith only [high],
      by nlinarith only [ec.2.2.1,en.1],by nlinarith only [ev.2.2.2,en.2.1]⟩
  have base := UpperRightCornerTopLongitudinal.top_lower T tn
    (by simpa only [←same] using side) marker row missingWing missingNE
  let K := E.c*T.c-f*T.s
  let H := E.c*T.s+f*T.c
  have kp : 0≤K := by
    have first := mul_nonneg ep.le (sub_nonneg.mpr tn.2.1)
    have last := mul_nonneg tn.1 (sub_nonneg.mpr en.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    exact add_nonneg (mul_nonneg ep.le tn.1) (mul_nonneg en.1 cp.le)
  have upperEU : upper T E.c (-f)=K*(T.loU+T.side)-H*T.loV := by
    rw [upper_in_bands]
    have a : E.c*T.c+(-f)*T.s=K := by dsimp [K]; ring
    have b : -E.c*T.s+(-f)*T.c=-H := by dsimp [H]; ring
    rw [a,b,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  have upperEV : upper T f E.c=H*(T.loU+T.side)+K*(T.loV+T.side) := by
    rw [upper_in_bands]
    have a : f*T.c+E.c*T.s=H := by dsimp [H]; ring
    have b : -f*T.s+E.c*T.c=K := by dsimp [K]; ring
    rw [a,b,abs_of_nonneg hp,abs_of_nonneg kp]
    ring
  have lowerTU : lower E T.c T.s=K*E.loU+H*E.loV := by
    have ku : 0≤T.c*E.c-T.s*f := by dsimp [K] at kp; nlinarith only [kp]
    have hv : 0≤T.c*f+T.s*E.c := by dsimp [H] at hp; nlinarith only [hp]
    have value := lower_negative_pos E f T.c T.s sign ku hv
    dsimp [K,H]
    nlinarith only [value]
  have upperTV : upper E (-T.s) T.c=-H*E.loU+K*(E.loV+E.side) := by
    rw [upper_in_bands,sign]
    have a : (-T.s)*E.c+T.c*(-f)=-H := by dsimp [H]; ring
    have b : -(-T.s)*(-f)+T.c*E.c=K := by dsimp [K]; ring
    rw [a,b,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg kp]
    ring
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
    rw [sign] at sep
    rcases sep with reverse | forward
    · have normal : E.c^2+(-f)^2=1 := by nlinarith only [en.2.2]
      have a := strict_bounds E _ _ E.c (-f) normal corner
      have b := strict_bounds T _ _ E.c (-f) normal marker
      nlinarith only [reverse,a.2,b.1,ep,en.1]
    · have own : lower E E.c (-f)=E.loU := by simpa only [sign] using (ownU E).1
      rw [own,upperEU,←same] at forward
      have first := mul_nonneg kp (sub_nonneg.mpr base)
      have last := mul_nonneg hp (show 0≤3*T.c-(12/5)*T.s-T.loV by
        linarith only [row.2.2.1])
      have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have margin := first_margin en tn
      have identity : K*((17/10)*T.c+3*T.s)-H*(3*T.c-(12/5)*T.s)+K+1-
          ((7/2)*E.c-3*f)=
          1+E.c*(T.c-9/5+(7/10)*T.s^2)+f*(-T.s+(7/10)*T.c*T.s) := by
        dsimp [K,H]
        linear_combination ((17/10)*E.c-3*f)*tn.2.2
      clear_value K H
      nlinarith only [forward,cap,first,last,size,margin,identity]
  · have sep := separateAxis _ _ _ (transverse_radius E T) evAxis
    rw [sign,neg_neg] at sep
    rcases sep with reverse | forward
    · have normal : f^2+E.c^2=1 := by nlinarith only [en.2.2]
      have a := strict_bounds E _ _ f E.c normal verticalFar
      have b := strict_bounds T _ _ f E.c normal row
      nlinarith only [reverse,a.2,b.1,ep,en.1]
    · have own : lower E f E.c=E.loV := by simpa only [sign,neg_neg] using (ownV E).1
      rw [own,upperEV,←same] at forward
      have wall := UpperRightNegativeTopReach.top_wall E f sign box
      have first := mul_nonneg (mul_nonneg ep.le hp) (sub_nonneg.mpr base)
      have last := mul_nonneg (mul_nonneg ep.le kp)
        (show 0≤T.loV+E.side-(3*T.c-(12/5)*T.s) by rw [same]; linarith only [row.2.2.2])
      have sep := mul_nonneg ep.le (sub_nonneg.mpr forward)
      have target := mul_nonneg en.1 (sub_nonneg.mpr cap)
      have coefficient : 0<E.c*H+E.c+f := by
        have prod := mul_nonneg ep.le hp
        linarith only [prod,ep,en.1]
      have size := mul_pos coefficient (sub_pos.mpr side)
      have margin := third_margin en tn
      have identity :
          E.c*(H*((17/10)*T.c+3*T.s)+K*(3*T.c-(12/5)*T.s))+E.c*H+E.c+f-
            (4+f*((7/2)*E.c-3*f))=
          E.c+f-1+E.c*f*(T.c-9/5+(7/10)*T.s^2)+
            E.c^2*T.s*(1-(7/10)*T.c) := by
        dsimp [K,H]
        linear_combination ((17/10)*E.c*f+3*E.c^2)*tn.2.2+3*en.2.2
      clear_value K H
      nlinarith only [wall,first,last,sep,target,size,margin,identity]
  · have identity : supportRadius E T.c T.s+supportRadius T T.c T.s=pairRadius T E := by
      rw [add_comm]; exact parallel_radius T E
    have sep := separateAxis _ _ _ identity tu
    rcases sep with reverse | forward
    · have a := strict_bounds E _ _ T.c T.s tn.2.2 corner
      have b := strict_bounds T _ _ T.c T.s tn.2.2 marker
      nlinarith only [reverse,a.2,b.1,cp,tn.2.1]
    · rw [(ownU T).2,lowerTU,←same] at forward
      have first := mul_nonneg kp (sub_nonneg.mpr cap)
      have last := mul_nonneg hp (show 0≤3*f+3*E.c-E.loV by linarith only [ec.2.2.1])
      have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have margin := second_margin en tn
      have identity : K*((7/2)*E.c-3*f)+H*(3*f+3*E.c)=
          3*(T.c+T.s)+(1/2)*E.c*K := by
        dsimp [K,H]
        linear_combination (3*T.c+3*T.s)*en.2.2
      change 0<1-(13/10)*T.c+K*(1-E.c/2) at margin
      clear_value K H
      nlinarith only [forward,base,first,last,size,margin,identity]
  · have identity : supportRadius E (-T.s) T.c+supportRadius T (-T.s) T.c=pairRadius T E := by
      rw [add_comm]; exact transverse_radius T E
    have sep := separateAxis _ _ _ identity tv
    rcases sep with forward | reverse
    · rw [upperTV,(ownV T).1] at forward
      have first := mul_nonneg hp (sub_nonneg.mpr cap)
      have last := mul_nonneg kp (show 0≤E.loV+E.side-(3*f+(7/2)*E.c) by
        linarith only [ev.2.2.2])
      have size := mul_nonneg hp (sub_nonneg.mpr side.le)
      have margin := fourth_margin en tn
      have identity : -H*((7/2)*E.c-3*f)+K*(3*f+(7/2)*E.c)+H-
          (3*T.c-(12/5)*T.s)=
          T.c*(1/2+f-f*(E.c+f)/2)+T.s*(E.c-11/10+f*(f-E.c)/2) := by
        dsimp [K,H]
        linear_combination ((7/2)*T.c-(7/2)*T.s)*en.2.2
      clear_value K H
      nlinarith only [forward,first,last,size,margin,identity,row.2.2.1]
    · have normal : (-T.s)^2+T.c^2=1 := by nlinarith only [tn.2.2]
      have a := strict_bounds E _ _ (-T.s) T.c normal corner
      have b := strict_bounds T _ _ (-T.s) T.c normal row
      nlinarith only [reverse,a.1,b.2,tn.1]

end N12Compact.UpperRightNegativeCornerPositiveTop
