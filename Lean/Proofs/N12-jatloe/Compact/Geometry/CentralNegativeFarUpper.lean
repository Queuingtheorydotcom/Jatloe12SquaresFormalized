import Compact.Geometry.CentralNegativeBottomAxes

/-! An incoming positive central axis and the full negative bottom wall
exclude the upper-U escape of the genuine farther point (2.86,1).
Both transverse bottom-wall separators are retained throughout. -/
namespace N12Compact.CentralNegativeFarUpper

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner CentralNegativeNeighborBounds
set_option Elab.async false

private theorem scalar_entrance {C S c t : ℝ}
    (an : Normal C S) (bn : Normal c t)
    (positive : 0<C*(43/50-c-t+(7/50)*t^2+c*t)+
      S*(-t^2+(7/50)*c*t-c+t)) :
    3/5<t ∧ S<C := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤C := by linarith only [ab.1]
  have mixed : c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (c-t)]
  have steep : 3/5<t := by
    by_contra no
    have small : t≤3/5 := le_of_not_gt no
    have smallSquare := mul_self_le_mul_self bn.1 small
    have wide : 4/5≤c := by nlinarith only [smallSquare,bn.2.2,bb.1]
    have wideSquare := mul_self_le_mul_self (by norm_num : (0:ℝ)≤4/5) wide
    have coeff := own_coefficients bn
    have horizontal : 43/50-c-t+(7/50)*t^2+c*t≤0 := by
      nlinarith only [coeff.1,wideSquare,bn.2.2]
    have vertical : -t^2+(7/50)*c*t-c+t≤0 := by
      nlinarith only [mixed,wide,small,sq_nonneg t]
    have first := mul_nonneg cp (neg_nonneg.mpr horizontal)
    have last := mul_nonneg an.1 (neg_nonneg.mpr vertical)
    nlinarith only [first,last,positive]
  have steepSquare := mul_self_le_mul_self (by norm_num : (0:ℝ)≤3/5) steep.le
  have diagonal : (43/50-c-t+(7/50)*t^2+c*t)+
      (-t^2+(7/50)*c*t-c+t)≤0 := by
    nlinarith only [bb.1,mixed,steepSquare]
  have strictOrder : S<C := by
    by_contra no
    have equality : S=C := by linarith only [no,an.2.1]
    have product := mul_nonneg cp (neg_nonneg.mpr diagonal)
    rw [equality] at positive
    nlinarith only [product,positive]
  exact ⟨steep,strictOrder⟩

private theorem mixed_margin {C S c t d r : ℝ}
    (an : Normal C S) (bn : Normal c t) (dn : Normal d r)
    (small : c≤4/5) (order : r*c-d*t≤0) :
    (C*d-S*r)*(2*c+3*t-1)+(r*c-d*t)*(C*c-S*t)+
      2*(r*c-d*t)*(C+S)-(C*c-S*t)*((143/50)*r+d)≤0 := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have cp : 0<c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  let X := d*(c+t-1-c*t)+r*c*(c-43/50)
  let Y := r*(1-(7/50)*t-c*t)-d*t*(1-t)
  have first := mul_nonneg (sub_nonneg.mpr bb.2.1)
    (sub_nonneg.mpr bb.2.2.2.1)
  have firstWeight := mul_nonneg dp first
  have lastWeight := mul_nonneg (mul_nonneg dn.1 cp.le)
    (show 0≤43/50-c by linarith only [small])
  have horizontal : X≤0 := by dsimp [X]; nlinarith only [firstWeight,lastWeight]
  let V := (c+7/50)*(c-t)+1-c
  have vp : 0≤V := by
    have product := mul_nonneg (show 0≤c+7/50 by linarith only [cp])
      (sub_nonneg.mpr bn.2.1)
    dsimp [V]; nlinarith only [product,bb.2.1]
  have chord : c-1+(7/50)*t≤0 := by linarith only [small,bb.2.2.2.1]
  have endpoint := mul_nonneg (sub_nonneg.mpr bn.2.1) (neg_nonneg.mpr chord)
  have endpointWeight := mul_nonneg dp endpoint
  have orderWeight := mul_nonneg (neg_nonneg.mpr order) vp
  have identity : c*(X+Y)=d*(c-t)*(c-1+(7/50)*t)+(r*c-d*t)*V := by
    dsimp [X,Y,V]; ring
  have diagonal : X+Y≤0 := by
    have scaled : c*(X+Y)≤0 := by
      clear_value X Y V
      nlinarith only [identity,endpointWeight,orderWeight]
    exact nonpos_of_mul_nonpos_right scaled cp
  have firstCentral := mul_nonneg (sub_nonneg.mpr an.2.1) (neg_nonneg.mpr horizontal)
  have lastCentral := mul_nonneg an.1 (neg_nonneg.mpr diagonal)
  have expansion : (C*d-S*r)*(2*c+3*t-1)+(r*c-d*t)*(C*c-S*t)+
      2*(r*c-d*t)*(C+S)-(C*c-S*t)*((143/50)*r+d)=C*X+S*Y := by
    dsimp [X,Y]; ring
  clear_value X Y V
  nlinarith only [firstCentral,lastCentral,expansion]

theorem impossible (D B : OpenSquare) (r t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (dn : Normal D.c r)
    (bs : B.s=-t) (ds : D.s=-r) (side : 1≤B.side)
    (far : D.Inside (143/50) 1)
    (capU : B.loU+B.side≤(143/50)*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*(C+S)<lower B C S)
    (separation : upper D t B.c≤B.loV ∨
      D.loV+D.side≤lower B r D.c) : False := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have cp : 0<C := by linarith only [ab.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have dc : 0<D.c := by linarith only [db.1]
  let K := C*B.c-S*t
  let H := C*t+S*B.c
  have kp : 0≤K := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr an.2.1)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg cp.le bn.1) (mul_nonneg an.1 bc.le)
  have centralFormula : lower B C S=K*B.loU+H*B.loV :=
    lower_negative_pos B t C S bs kp hp
  have first := mul_nonneg kp (sub_nonneg.mpr capU)
  have last := mul_nonneg hp (sub_nonneg.mpr capV)
  have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr side)
  have expansion : K*((143/50)*B.c-t-1)+H*(2*B.c+3*t-1)-2*(C+S)=
      C*(43/50-B.c-t+(7/50)*t^2+B.c*t)+
        S*(-t^2+(7/50)*B.c*t-B.c+t) := by
    dsimp [K,H]
    linear_combination ((143/50)*C+2*S)*bn.2.2
  have entrance := scalar_entrance an bn
    (by clear_value K H; nlinarith only [centralFormula,first,last,width,expansion,incoming])
  have steepSquare := mul_self_le_mul_self (by norm_num : (0:ℝ)≤3/5) entrance.1.le
  have small : B.c≤4/5 := by nlinarith only [steepSquare,bn.2.2,bb.1]
  have short : B.c+(7/50)*t<1 := by linarith only [small,bb.2.2.2.1]
  have strictK : 0<K := by
    have first := mul_pos bc (sub_pos.mpr entrance.2)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  rcases separation with onB | onD
  · have point := strict_bounds D _ _ t B.c (by nlinarith only [bn.2.2]) far
    nlinarith only [point.2,onB,capV,side,short]
  · have point := strict_bounds D _ _ r D.c (by nlinarith only [dn.2.2]) far
    have upperD : upper D r D.c=D.loV+D.side := by
      have value := (ownV D).2
      simpa only [ds,neg_neg] using value
    rw [upperD] at point
    have incomingD : (143/50)*r+D.c<lower B r D.c := by
      linarith only [point.2,onD]
    let J := r*B.c-D.c*t
    let L := r*t+D.c*B.c
    have lp : 0≤L := by
      dsimp [L]
      exact add_nonneg (mul_nonneg dn.1 bn.1) (mul_nonneg dc.le bc.le)
    by_cases jp : 0≤J
    · have formula : lower B r D.c=J*B.loU+L*B.loV :=
        lower_negative_pos B t r D.c bs jp lp
      let X := (7/50)*t^2+B.c*t-B.c-t
      let Y := 1-t^2+(7/50)*B.c*t+t-B.c
      have first := mul_nonneg jp (sub_nonneg.mpr capU)
      have last := mul_nonneg lp (sub_nonneg.mpr capV)
      have width := mul_nonneg (add_nonneg jp lp) (sub_nonneg.mpr side)
      have expansion : J*((143/50)*B.c-t-1)+L*(2*B.c+3*t-1)-
          ((143/50)*r+D.c)=r*X+D.c*Y := by
        dsimp [J,L,X,Y]
        linear_combination (((143/50)*r)+2*D.c)*bn.2.2
      have xNonpos : X≤0 := by
        have first := mul_nonneg bc.le (sub_nonneg.mpr bb.2.2.2.1)
        have last := mul_nonneg bn.1
          (show 0≤1-(7/50)*t by linarith only [bb.2.2.2.1])
        dsimp [X]; nlinarith only [first,last]
      have endpoint : t*X+B.c*Y=B.c+(7/50)*t-1 := by
        dsimp [X,Y]
        linear_combination ((7/50)*t-1)*bn.2.2
      have orderWeight := mul_nonneg jp (neg_nonneg.mpr xNonpos)
      have endWeight := mul_nonneg dc.le
        (show 0≤1-B.c-(7/50)*t by linarith only [short])
      have scaledEndpoint := congrArg (fun z : ℝ => D.c*z) endpoint
      have comparison : B.c*(r*X+D.c*Y)=J*X+D.c*(t*X+B.c*Y) := by
        dsimp [J]; ring
      have nonpositive : r*X+D.c*Y≤0 := by
        have scaled : B.c*(r*X+D.c*Y)≤0 := by
          clear_value J L X Y
          nlinarith only [comparison,orderWeight,endWeight,scaledEndpoint]
        exact nonpos_of_mul_nonpos_right scaled bc
      clear_value J L X Y
      nlinarith only [formula,first,last,width,expansion,nonpositive,incomingD]
    · have jn : J≤0 := le_of_lt (lt_of_not_ge jp)
      have formula : lower B r D.c=J*(B.loU+B.side)+L*B.loV := by
        rw [lower_in_bands,bs]
        have u : r*B.c+D.c*(-t)=J := by dsimp [J]; ring
        have v : -r*(-t)+D.c*B.c=L := by dsimp [L]; ring
        rw [u,v,abs_of_nonpos jn,abs_of_nonneg lp]; ring
      let Z := C*D.c-S*r
      have zp : 0≤Z := by
        have first := mul_nonneg dc.le (sub_nonneg.mpr an.2.1)
        have last := mul_nonneg an.1 (sub_nonneg.mpr dn.2.1)
        dsimp [Z]; nlinarith only [first,last]
      have centralWeight := mul_nonneg (neg_nonneg.mpr jn)
        (show 0≤lower B C S-2*(C+S) by linarith only [incoming])
      have wallWeight := mul_pos strictK (sub_pos.mpr incomingD)
      have topWeight := mul_nonneg zp
        (show 0≤2*B.c+3*t-1-B.loV by linarith only [capV,side])
      have sideWeight := mul_nonneg
        (mul_nonneg (neg_nonneg.mpr jn) kp) (sub_nonneg.mpr side)
      have identity : (-J)*(K*B.loU+H*B.loV)+
          K*(J*(B.loU+B.side)+L*B.loV)=Z*B.loV+J*K*B.side := by
        dsimp [J,K,H,L,Z]
        linear_combination (C*D.c-S*r)*B.loV*bn.2.2
      have residual := mixed_margin an bn dn small jn
      rw [centralFormula] at centralWeight
      rw [formula] at wallWeight
      dsimp [J,K,H,L,Z] at centralFormula formula identity centralWeight wallWeight topWeight sideWeight
      nlinarith only [centralFormula,formula,identity,centralWeight,wallWeight,
        topWeight,sideWeight,residual]

#print axioms impossible
end N12Compact.CentralNegativeFarUpper
