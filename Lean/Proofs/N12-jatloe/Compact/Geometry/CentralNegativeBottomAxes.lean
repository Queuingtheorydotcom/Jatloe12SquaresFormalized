import Compact.Geometry.CentralNegativeNeighbor

/-! The complete bottom-wall/negative-central pair has only two upward
transverse separators. Both genuine central upper faces, the real wall
point at 2.6, and complete square supports are retained. -/
namespace N12Compact.CentralNegativeBottomAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner CentralNegativeNeighborBounds C977ChainBridge

private theorem virtual_point {c t : ℝ} (bn : Normal c t) :
    3+c*t-c-t≤13/5 ∧ 1≤2-t^2+t-c ∧
      (3+c*t-c-t)+(2-t^2+t-c)≤18/5 := by
  have b := normal_bounds bn
  have coeff := own_coefficients bn
  have first := mul_nonneg (show 0≤c by linarith only [b.1])
    (sub_nonneg.mpr b.2.2.2.2.2)
  have last := mul_nonneg (sub_nonneg.mpr b.2.1) (sub_nonneg.mpr b.2.1)
  refine ⟨?_,?_,?_⟩
  · nlinarith only [coeff.1]
  · nlinarith only [bn.2.2,b.2.2.2.2.1,last]
  · nlinarith only [first,b.1,bn.2.2]

private theorem positive_lower (B : OpenSquare) (t d r : ℝ)
    (signed : B.s=-t) (bn : Normal B.c t) (dn : Normal d r)
    (side : 1≤B.side) (capU : B.loU+B.side≤3*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t) : lower B d r≤(13/5)*d+r := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have bc : 0≤B.c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  let K := d*B.c-r*t
  let H := d*t+r*B.c
  have kp : 0≤K := by
    have first := mul_nonneg bc (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg dp bn.1) (mul_nonneg dn.1 bc)
  have formula : lower B d r=K*B.loU+H*B.loV := by
    exact lower_negative_pos B t d r signed kp hp
  have first := mul_nonneg kp (sub_nonneg.mpr capU)
  have last := mul_nonneg hp (sub_nonneg.mpr capV)
  have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr side)
  have identity : K*(3*B.c-t-1)+H*(2*B.c+3*t-1)=
      d*(3+B.c*t-B.c-t)+r*(2-t^2+t-B.c) := by
    dsimp [K,H]
    linear_combination (3*d+2*r)*bn.2.2
  have virtual := virtual_point bn
  have cWeight := mul_nonneg dp (sub_nonneg.mpr virtual.2.2)
  have rWeight := mul_nonneg (sub_nonneg.mpr dn.2.1) (sub_nonneg.mpr virtual.2.1)
  nlinarith only [formula,first,last,width,identity,cWeight,rWeight]

private theorem negative_lower (B : OpenSquare) (t d r : ℝ)
    (signed : B.s=-t) (bn : Normal B.c t) (dn : Normal d r)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t) :
    lower B d (-r)≤(13/5)*d-r := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have bc : 0≤B.c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  let K := d*B.c+r*t
  let H := d*t-r*B.c
  have kp : 0≤K := by
    dsimp [K]; exact add_nonneg (mul_nonneg dp bc) (mul_nonneg dn.1 bn.1)
  by_cases hp : 0≤H
  · have formula : lower B d (-r)=K*B.loU+H*B.loV := by
      have ku : 0≤d*B.c-(-r)*t := by dsimp [K] at kp; nlinarith only [kp]
      have hv : 0≤d*t+(-r)*B.c := by dsimp [H] at hp; nlinarith only [hp]
      have value := lower_negative_pos B t d (-r) signed ku hv
      dsimp [K,H]
      nlinarith only [value]
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg hp (sub_nonneg.mpr capV)
    have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr side)
    have identity : K*(3*B.c-t-1)+H*(2*B.c+3*t-1)=
        d*(3+B.c*t-B.c-t)-r*(2-t^2+t-B.c) := by
      dsimp [K,H]
      linear_combination (3*d-2*r)*bn.2.2
    have virtual := virtual_point bn
    have firstWeight := mul_nonneg dp (sub_nonneg.mpr virtual.1)
    have lastWeight := mul_nonneg dn.1 (sub_nonneg.mpr virtual.2.1)
    nlinarith only [formula,first,last,width,identity,firstWeight,lastWeight]
  · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
    have formula : lower B d (-r)=K*B.loU+H*(B.loV+B.side) := by
      rw [lower_in_bands,signed]
      have a : d*B.c+(-r)*(-t)=K := by dsimp [K]; ring
      have b : -d*(-t)+(-r)*B.c=H := by dsimp [H]; ring
      rw [a,b,abs_of_nonneg kp,abs_of_nonpos hn]; ring
    have m := (negative_bands B t _ _ signed).mp marker
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg (neg_nonneg.mpr hn)
      (show 0≤B.loV+B.side-((47/20)*t+(33/20)*B.c) by linarith only [m.2.2.2])
    have width := mul_nonneg kp (sub_nonneg.mpr side)
    let X := 2/5-B.c-(13/20)*t^2+(13/20)*B.c*t
    let Y := -(13/20)+(13/20)*t^2+(13/20)*B.c*t-t
    have identity : K*(3*B.c-t-1)+H*((47/20)*t+(33/20)*B.c)-((13/5)*d-r)=
        d*X+r*Y := by
      dsimp [K,H,X,Y]
      linear_combination (3*d-(33/20)*r)*bn.2.2
    have circleProduct := mul_nonneg (sub_nonneg.mpr bb.2.1)
      (show 0≤(13/20)*B.c-7/20 by linarith only [bb.1])
    have mixed : B.c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (B.c-t)]
    have xNonpos : X≤0 := by dsimp [X]; nlinarith only [circleProduct,bn.2.2,mixed]
    have yProduct := mul_nonneg bc (sub_nonneg.mpr bn.2.1)
    have yNonpos : Y≤0 := by dsimp [Y]; nlinarith only [bn.2.2,yProduct,bn.1]
    have firstWeight := mul_nonneg dp (neg_nonneg.mpr xNonpos)
    have lastWeight := mul_nonneg dn.1 (neg_nonneg.mpr yNonpos)
    clear_value K H X Y
    nlinarith only [formula,first,last,width,identity,firstWeight,lastWeight]

theorem alternatives (D B : OpenSquare) (t : ℝ) (signed : B.s=-t)
    (bn : Normal B.c t) (dc : 0<D.c) (canonicalD : |D.s|≤D.c)
    (same : D.side=B.side) (side : 1<B.side)
    (dMarker : D.Inside 2 (457/500)) (dHigh : D.Inside (13/5) 1)
    (marker : B.Inside (47/20) (33/20)) (wall : B.Inside 3 (87/50))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (apart : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) :
    upper D t B.c≤B.loV ∨ D.loV+D.side≤lower B (-D.s) D.c := by
  have bb := normal_bounds bn
  have bc : 0<B.c := by linarith only [bb.1]
  have ds := abs_le.mp canonicalD
  have lowerBound : lower B D.c D.s≤(13/5)*D.c+D.s := by
    by_cases sign : 0≤D.s
    · exact positive_lower B t D.c D.s signed bn
        ⟨sign,ds.2,D.unit_normal⟩ side.le capU capV
    · have negative : D.s≤0 := le_of_lt (lt_of_not_ge sign)
      have dn : Normal D.c (-D.s) :=
        ⟨neg_nonneg.mpr negative,by linarith only [ds.1],
          by nlinarith only [D.unit_normal]⟩
      simpa only [neg_neg, sub_neg_eq_add] using negative_lower B t D.c (-D.s) signed bn dn
        side.le marker capU capV
  have noD : ¬(upper D D.c D.s≤lower B D.c D.s ∨
      upper B D.c D.s≤lower D D.c D.s) := by
    have high := strict_bounds D _ _ D.c D.s D.unit_normal dHigh
    have bp := strict_bounds B _ _ D.c D.s D.unit_normal wall
    have dm := strict_bounds D _ _ D.c D.s D.unit_normal dMarker
    rintro (sep | sep)
    · nlinarith only [sep,high.2,lowerBound]
    · nlinarith only [sep,bp.2,dm.1,ds.1,dc]
  have noB : ¬(upper D B.c B.s≤lower B B.c B.s ∨
      upper B B.c B.s≤lower D B.c B.s) := by
    have high := strict_bounds D _ _ B.c B.s B.unit_normal dHigh
    have bp := strict_bounds B _ _ B.c B.s B.unit_normal wall
    have dm := strict_bounds D _ _ B.c B.s B.unit_normal dMarker
    rw [signed] at high bp dm
    rintro (sep | sep)
    · rw [(ownU B).1,signed] at sep
      nlinarith only [sep,high.2,capU,side,bb.2.1]
    · rw [signed] at sep
      nlinarith only [sep,bp.2,dm.1,bc,bn.2.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint D B same apart
  change pairRadius D B≤|D.c*(centerX B-centerX D)+D.s*(centerY B-centerY D)| ∨
    pairRadius D B≤|-D.s*(centerX B-centerX D)+D.c*(centerY B-centerY D)| ∨
    pairRadius B D≤|B.c*(centerX B-centerX D)+B.s*(centerY B-centerY D)| ∨
    pairRadius B D≤|-B.s*(centerX B-centerX D)+B.c*(centerY B-centerY D)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius D x y+supportRadius B x y=R)
      (sep : R≤|x*(centerX B-centerX D)+y*(centerY B-centerY D)|) :=
    separated D B x y (by rwa [identity])
  rcases axes with du | dv | bu | bv
  · exact False.elim (noD (separateAxis _ _ _ (parallel_radius D B) du))
  · rcases separateAxis _ _ _ (transverse_radius D B) dv with forward | reverse
    · exact Or.inr (by simpa only [(ownV D).2] using forward)
    · have normal : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
      have bp := strict_bounds B _ _ (-D.s) D.c normal marker
      have dh := strict_bounds D _ _ (-D.s) D.c normal dHigh
      exfalso
      nlinarith only [reverse,bp.2,dh.1,ds.1,dc]
  · have identity : supportRadius D B.c B.s+supportRadius B B.c B.s=pairRadius B D := by
      rw [add_comm]; exact parallel_radius B D
    exact False.elim (noB (separateAxis _ _ _ identity bu))
  · have identity : supportRadius D (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B D := by
      rw [add_comm]; exact transverse_radius B D
    rcases separateAxis _ _ _ identity bv with forward | reverse
    · rw [(ownV B).1] at forward
      exact Or.inl (by simpa only [signed,neg_neg] using forward)
    · have normal : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
      have bp := strict_bounds B _ _ (-B.s) B.c normal marker
      have dm := strict_bounds D _ _ (-B.s) B.c normal dMarker
      rw [signed,neg_neg] at bp dm reverse
      exfalso
      nlinarith only [reverse,bp.2,dm.1,bn.1,bc]

end N12Compact.CentralNegativeBottomAxes
