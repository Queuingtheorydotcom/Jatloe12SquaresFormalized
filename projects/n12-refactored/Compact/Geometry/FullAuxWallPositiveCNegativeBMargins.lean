import Compact.Geometry.C977CornerCubic

/-! Exact continuous margins for both genuine corner escapes of the
negative outer square. Rational disk bounds cover complete angle arcs;
there are no sampled orientations or saved pose intervals. -/
namespace N12Compact.FullAuxWallPositiveCNegativeBMargins

open C977CornerCubic
set_option Elab.async false

private theorem deficit {b t : ℝ} (bn : Normal b t) : 1-b≤(3/5)*t^2 := by
  have bounds := normal_bounds bn
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤3*b-2 by linarith only [bounds.1])
  nlinarith only [product,bn.2.2]

theorem lower_u {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t) :
    C*(2-b-t+(3/5)*b*t)+S*((3/5)-b+t-(3/5)*t^2)≤1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have Cp : 0≤C := by linarith only [cb.1]
  have bp : 0≤b := by linarith only [bb.1]
  let P := 2-b-t+(3/5)*b*t
  let Q := (3/5)-b+t-(3/5)*t^2
  have arcProduct := mul_nonneg
    (show 0≤b+t-1 by linarith only [bb.2.2.2.2.1])
    (show 0≤(3/2 : ℝ)-(b+t) by linarith only [bb.2.2.2.2.2])
  have arc : (4/5)*b*t≤b+t-1 := by
    nlinarith only [arcProduct,bn.2.2]
  have pBound : P≤1-(1/5)*b*t := by dsimp [P]; nlinarith only [arc]
  have qBound : Q≤t-2/5 := by dsimp [Q]; nlinarith only [deficit bn]
  change C*P+S*Q≤1
  by_cases small : t≤2/5
  · have product := mul_nonneg bp bn.1
    have p : P≤1 := by nlinarith only [pBound,product]
    have q : Q≤0 := by linarith only [qBound,small]
    have first := mul_nonneg Cp (sub_nonneg.mpr p)
    have second := mul_nonpos_of_nonneg_of_nonpos cn.1 q
    nlinarith only [first,second,cb.2.1]
  · have large : (2/5 : ℝ)≤t := (lt_of_not_ge small).le
    have product := mul_nonneg bp (sub_nonneg.mpr large)
    have p : P≤189/200 := by nlinarith only [pBound,product,bb.1]
    have tBound : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
    have q : Q≤11/35 := by linarith only [qBound,tBound]
    have disk : (189/200)*C+(11/35)*S<1 := by
      nlinarith only [cn.2.2,sq_nonneg (C-189/200),sq_nonneg (S-11/35)]
    have first := mul_nonneg Cp (sub_nonneg.mpr p)
    have second := mul_nonneg cn.1 (sub_nonneg.mpr q)
    nlinarith only [first,second,disk]

theorem upper_v {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t) :
    C*(2-b-(13/20)*t^2-(13/20)*b*t)+
      S*(-(1/20)+(13/20)*t^2-(13/20)*b*t+t)≤1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have Cp : 0≤C := by linarith only [cb.1]
  let P := 2-b-(13/20)*t^2-(13/20)*b*t
  let Q := -(1/20)+(13/20)*t^2-(13/20)*b*t+t
  have cosineWeight := mul_nonneg bn.1 (sub_nonneg.mpr bb.1)
  have pBound : P≤1-(9/20)*t := by
    dsimp [P]
    nlinarith only [deficit bn,cosineWeight,sq_nonneg t,bn.1]
  have orderWeight := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
  have qBound : Q≤t-1/20 := by dsimp [Q]; nlinarith only [orderWeight]
  change C*P+S*Q≤1
  by_cases small : t≤1/20
  · have p : P≤1 := by linarith only [pBound,bn.1]
    have q : Q≤0 := by linarith only [qBound,small]
    have first := mul_nonneg Cp (sub_nonneg.mpr p)
    have second := mul_nonpos_of_nonneg_of_nonpos cn.1 q
    nlinarith only [first,second,cb.2.1]
  · have large : (1/20 : ℝ)≤t := (lt_of_not_ge small).le
    have tBound : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
    have squareBound := mul_nonneg bn.1 (sub_nonneg.mpr tBound)
    have radius : (1-(9/20)*t)^2+(t-1/20)^2<1 := by
      nlinarith only [squareBound,large]
    have disk : (1-(9/20)*t)*C+(t-1/20)*S<1 := by
      nlinarith only [cn.2.2,radius,
        sq_nonneg (C-(1-(9/20)*t)),sq_nonneg (S-(t-1/20))]
    have first := mul_nonneg Cp (sub_nonneg.mpr pBound)
    have second := mul_nonneg cn.1 (sub_nonneg.mpr qBound)
    nlinarith only [first,second,disk]

#print axioms lower_u
#print axioms upper_v
end N12Compact.FullAuxWallPositiveCNegativeBMargins
