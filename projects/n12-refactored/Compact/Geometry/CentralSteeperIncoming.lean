import Compact.Geometry.CentralRightIncomingOrdered

/-! The reversed positive incoming-axis order retains the actual lower
corner escape and inward upper-U cap. Their complete support bounds make
the center owner shallow and allow at most .09 of extra upper-U width. -/
namespace N12Compact.CentralSteeperIncoming

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private def excess (C S c s : ℝ) : ℝ :=
  C*(1-c)*(1-s)+S*(c*(1-c)-s)

private theorem excess_bound {C S c s : ℝ} (an : Normal C S) (bn : Normal c s) :
    excess C S c s≤(9/100)*C := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤C := by linarith only [ab.1]
  have other : c*(1-c)-s≤0 := by
    have product := mul_nonneg (sub_nonneg.mpr bb.2.1) (sub_nonneg.mpr bb.2.1)
    nlinarith only [product,bb.2.2.2.2.1]
  have sumSquare : (c+s)^2≤2 := by nlinarith only [bn.2.2,sq_nonneg (c-s)]
  have sumBound : c+s≤71/50 := by nlinarith only [sumSquare]
  have chord := mul_nonneg (show 0≤c+s-1 by linarith only [bb.2.2.2.2.1])
    (show 0≤71/50-(c+s) by linarith only [sumBound])
  have square := mul_nonneg (show 0≤71/50-(c+s) by linarith only [sumBound])
    (show 0≤c+s+71/50-2 by linarith only [bb.2.2.2.2.1])
  have defect : (1-c)*(1-s)≤9/100 := by
    nlinarith only [square,bn.2.2]
  have first := mul_nonneg cp (sub_nonneg.mpr defect)
  have last := mul_nonneg an.1 (neg_nonneg.mpr other)
  dsimp [excess]
  nlinarith only [first,last]

private theorem excess_small {C S c s : ℝ} (an : Normal C S) (bn : Normal c s)
    (positive : 0<excess C S c s) : S<2/5 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0<C := by linarith only [ab.1]
  have sp : 0<s := by
    by_contra no
    have zero : s=0 := by linarith only [bn.1,no]
    have one : c=1 := by nlinarith only [zero,bn.2.2,bb.1]
    norm_num [excess,zero,one] at positive
  by_contra no
  have large : 2/5≤S := le_of_not_gt no
  have slope : 3*C≤7*S := by
    by_contra failure
    have weighted := mul_nonneg (show 0≤3*C-7*S by linarith only [failure])
      (show 0≤3*C+7*S by linarith only [cp,an.1])
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤S+2/5 by linarith only [an.1])
    nlinarith only [weighted,square,an.2.2]
  have halfSlope : 7*s≤3*(1+c) := by
    have sine : s≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
    linarith only [sine,bn.2.1]
  have first := mul_nonneg cp.le (sub_nonneg.mpr halfSlope)
  have second := mul_nonneg (show 0≤1+c by linarith only [bb.1])
    (sub_nonneg.mpr slope)
  have angle : C*s≤S*(1+c) := by nlinarith only [first,second]
  have firstWeight := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr bb.2.1) (sub_nonneg.mpr bb.2.2.2.1))
    (sub_nonneg.mpr angle)
  have lastWeight := mul_nonneg (mul_nonneg an.1 bn.1) (sub_nonneg.mpr bb.2.1)
  have identity : s*excess C S c s=
      (1-c)*(1-s)*(C*s-S*(1+c))-S*s*(1-c) := by
    dsimp [excess]
    linear_combination -S*bn.2.2
  have strict := mul_pos sp positive
  nlinarith only [identity,firstWeight,lastWeight,strict]

/-- No coordinate box replaces B: both original faces and the full
square width enter the lower-support comparison. -/
theorem central_cap (A B : OpenSquare) (an : Normal A.c A.s) (bn : Normal B.c B.s)
    (side : 1≤B.side) (center : A.Inside 2 2)
    (order : A.s*B.c<A.c*B.s)
    (floor : B.c-3*B.s≤B.loV)
    (cap : B.loU+B.side≤3*B.c+2*B.s)
    (incoming : A.loU+A.side≤lower B A.c A.s) :
    A.s<2/5 ∧ A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let K := A.c*B.c+A.s*B.s
  let H := A.s*B.c-A.c*B.s
  have kp : 0<K := by
    have first := mul_pos (show 0<A.c by linarith only [ab.1])
      (show 0<B.c by linarith only [bb.1])
    have last := mul_nonneg an.1 bn.1
    dsimp [K]; linarith only [first,last]
  have hn : H≤0 := by dsimp [H]; linarith only [order]
  have formula : lower B A.c A.s=K*B.loU+H*(B.loV+B.side) := by
    rw [lower_in_bands]
    have u : A.c*B.c+A.s*B.s=K := rfl
    have v : -A.c*B.s+A.s*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp.le,abs_of_nonpos hn]
    ring
  have first := mul_nonneg kp.le (sub_nonneg.mpr cap)
  have last := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr floor)
  have width := mul_nonneg (show 0≤K-H by linarith only [kp,hn])
    (sub_nonneg.mpr side)
  have identity : K*(3*B.c+2*B.s-1)+H*(B.c-3*B.s+1)=
      2*(A.c+A.s)+excess A.c A.s B.c B.s := by
    dsimp [K,H,excess]
    linear_combination (3*A.c+2*A.s)*bn.2.2
  have bound : lower B A.c A.s≤2*(A.c+A.s)+excess A.c A.s B.c B.s := by
    nlinarith only [formula,first,last,width,identity]
  have positive : 0<excess A.c A.s B.c B.s := by
    linarith only [center.2.1,incoming,bound]
  exact ⟨excess_small an bn positive,
    by linarith only [incoming,bound,excess_bound an bn]⟩

#print axioms central_cap
end N12Compact.CentralSteeperIncoming
