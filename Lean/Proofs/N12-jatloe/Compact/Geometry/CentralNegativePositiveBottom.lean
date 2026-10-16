import Compact.Geometry.CentralNegativeBottomAxes

/-! An incoming positive central axis cannot coexist with a positive
bottom wall below the negative southeast neighbor on the wall's axis.
The bottom marker and full container, rather than a virtual floor,
supply the final support bound. -/
namespace N12Compact.CentralNegativePositiveBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem coefficients {c t d r : ℝ} (bn : Normal c t) (dn : Normal d r) :
    d^2*(c+t-1-c*t)+c*(1-d-(43/500)*r^2-d*r*c)≤0 ∧
    d*r*(t-1+c*t)+d^2*(t^2-2*t)+d*t-(457/500)*t*r^2≤0 := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have cp : 0≤c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  have halfSquare : r^2≤1/2 := by
    have product := mul_nonneg (sub_nonneg.mpr dn.2.1) (add_nonneg dp dn.1)
    nlinarith only [product,dn.2.2]
  have mixedB : c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (c-t)]
  have mixedD : d*r≤1/2 := by nlinarith only [dn.2.2,sq_nonneg (d-r)]
  have chord : 1-d≤(3/7)*r := by
    have product := mul_nonneg dn.1
      (show 0≤21*d-20*r by linarith only [dn.2.1,dn.1])
    by_contra no
    have first : 0<7-7*d-3*r := by linarith only [no]
    have last : 0<7+7*d+3*r := by linarith only [db.1,dn.1]
    have square := mul_pos first last
    nlinarith only [product,dn.2.2,square]
  have productDC : (49/100 : ℝ)≤d*c := by
    have product := mul_nonneg (sub_nonneg.mpr db.1) cp
    nlinarith only [product,bb.1]
  have floorWeight := mul_nonneg dn.1 (sub_nonneg.mpr productDC)
  have firstCoefficient : 1-d-(43/500)*r^2-d*r*c≤0 := by
    nlinarith only [chord,floorWeight,dn.1,sq_nonneg r]
  have first := mul_nonneg (sq_nonneg d)
    (mul_nonneg (sub_nonneg.mpr bb.2.1) (sub_nonneg.mpr bb.2.2.2.1))
  have last := mul_nonneg cp (neg_nonneg.mpr firstCoefficient)
  refine ⟨by nlinarith only [first,last],?_⟩
  have ceiling : d≤1-r^2/2 := by nlinarith only [dn.2.2,sq_nonneg (1-d)]
  have ceilingWeight := mul_nonneg bn.1 (sub_nonneg.mpr ceiling)
  have identity : d*r*(t-1+c*t)+d^2*(t^2-2*t)+d*t-(457/500)*t*r^2=
      t*(t-1)+d*r*(t-1+c*t)+t*r^2*(293/500-t)+t*(d-1+r^2/2) := by
    linear_combination (t^2-2*t)*dn.2.2
  have dr : 0≤d*r := mul_nonneg dp dn.1
  have rt : 0≤t*r^2 := mul_nonneg bn.1 (sq_nonneg r)
  by_cases small : t≤1/2
  · have product := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
    have coefficient : t-1+c*t≤0 := by nlinarith only [product,small]
    have crossWeight := mul_nonneg dr (neg_nonneg.mpr coefficient)
    have remainder : r^2*(293/500-t)≤293/1000 := by
      nlinarith only [halfSquare,rt]
    have remainderWeight := mul_nonneg bn.1 (sub_nonneg.mpr remainder)
    have square := mul_nonneg bn.1 (sub_nonneg.mpr small)
    nlinarith only [identity,ceilingWeight,crossWeight,remainderWeight,square,bn.1]
  · have large : 1/2≤t := le_of_lt (lt_of_not_ge small)
    have firstWeight := mul_nonneg dr (sub_nonneg.mpr mixedB)
    have lastWeight := mul_nonneg (sub_nonneg.mpr mixedD) (sub_nonneg.mpr large)
    have crossBound : d*r*(t-1+c*t)≤t/2-1/4 := by
      nlinarith only [firstWeight,lastWeight]
    have product := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr large)
    have remainder : r^2*(293/500-t)≤43/1000 := by
      nlinarith only [product,halfSquare]
    have remainderWeight := mul_nonneg bn.1 (sub_nonneg.mpr remainder)
    have bound : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
    have square := mul_nonneg bn.1 (sub_nonneg.mpr bound)
    have numerical : t^2-(457/1000)*t-1/4≤0 := by
      nlinarith only [square,bound]
    nlinarith only [identity,ceilingWeight,crossBound,remainderWeight,numerical]

theorem impossible (D B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (dn : Normal D.c D.s)
    (signed : B.s=-t) (side : 1<B.side) (dSide : 1≤D.side)
    (box : InsideContainer D) (marker : D.Inside 2 (457/500))
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*(C+S)<lower B C S)
    (outgoing : D.loV+D.side≤lower B (-D.s) D.c) : False := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have cp : 0<C := by linarith only [ab.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have dc : 0<D.c := by linarith only [db.1]
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dc.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  have markerWeight := mul_nonneg dn.1
    (show 0≤2*D.c+(457/500)*D.s-D.loU by linarith only [marker.1])
  have sideWeight := mul_nonneg dc.le (sub_nonneg.mpr dSide)
  have wallSupport : D.c-2*D.c*D.s-(457/500)*D.s^2≤
      D.c*(D.loV+D.side) := by nlinarith only [wall,markerWeight,sideWeight]
  let K := C*B.c-S*t
  let H := C*t+S*B.c
  let J := -D.s*B.c-D.c*t
  let L := D.c*B.c-D.s*t
  let Z := C*D.c+S*D.s
  have kp : 0≤K := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr an.2.1)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg cp.le bn.1) (mul_nonneg an.1 bc.le)
  have jn : J≤0 := by
    have first := mul_nonneg dn.1 bc.le
    have last := mul_nonneg dc.le bn.1
    dsimp [J]; nlinarith only [first,last]
  have lp : 0≤L := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [L]; nlinarith only [first,last]
  have zp : 0<Z := by
    have first := mul_pos cp dc
    have last := mul_nonneg an.1 dn.1
    dsimp [Z]; nlinarith only [first,last]
  have centralFormula : lower B C S=K*B.loU+H*B.loV :=
    C977NegativeCorner.lower_negative_pos B t C S signed kp hp
  have wallFormula : lower B (-D.s) D.c=J*(B.loU+B.side)+L*B.loV := by
    rw [lower_in_bands,signed]
    have u : (-D.s)*B.c+D.c*(-t)=J := by dsimp [J]; ring
    have v : -(-D.s)*(-t)+D.c*B.c=L := by dsimp [L]; ring
    rw [u,v,abs_of_nonpos jn,abs_of_nonneg lp]; ring
  have centralWeight := mul_nonneg (neg_nonneg.mpr jn)
    (show 0≤lower B C S-2*(C+S) by linarith only [incoming])
  have wallWeight := mul_nonneg kp (sub_nonneg.mpr outgoing)
  have topWeight := mul_nonneg zp.le (sub_nonneg.mpr cap)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<Z-J*K by nlinarith only [zp,mul_nonneg (neg_nonneg.mpr jn) kp])
  have identity : (-J)*(K*B.loU+H*B.loV)+
      K*(J*(B.loU+B.side)+L*B.loV)=Z*B.loV+J*K*B.side := by
    dsimp [J,K,H,L,Z]
    linear_combination (C*D.c+S*D.s)*B.loV*bn.2.2
  have pressure : 0<Z*(2*B.c+3*t-1)+J*K+2*J*(C+S)-K*(D.loV+D.side) := by
    rw [centralFormula] at centralWeight
    rw [wallFormula] at wallWeight
    clear_value J K H L Z
    nlinarith only [centralFormula,wallFormula,centralWeight,wallWeight,topWeight,width,identity]
  have scaledPressure := mul_pos dc pressure
  have floorWeight := mul_nonneg kp (sub_nonneg.mpr wallSupport)
  have margins := coefficients bn dn
  have first := mul_nonneg cp.le (neg_nonneg.mpr margins.1)
  have last := mul_nonneg an.1 (neg_nonneg.mpr margins.2)
  have expansion : D.c*(Z*(2*B.c+3*t-1)+J*K+2*J*(C+S))-
      K*(D.c-2*D.c*D.s-(457/500)*D.s^2)=
      C*(D.c^2*(B.c+t-1-B.c*t)+B.c*(1-D.c-(43/500)*D.s^2-D.c*D.s*B.c))+
      S*(D.c*D.s*(t-1+B.c*t)+D.c^2*(t^2-2*t)+D.c*t-(457/500)*t*D.s^2) := by
    dsimp [J,K,Z]
    linear_combination C*B.c*dn.2.2
  clear_value J K Z
  nlinarith only [scaledPressure,floorWeight,first,last,expansion]

#print axioms impossible
end N12Compact.CentralNegativePositiveBottom
