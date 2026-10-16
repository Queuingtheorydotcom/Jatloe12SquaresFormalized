import Compact.Geometry.CentralNegativeBottomUpper

/-! The negative central test direction also excludes the upper-U miss
of the farther actual bottom point. The proof retains the true lower
crosspoint, full square width, and both relative-angle ranges. -/
namespace N12Compact.CentralNegativeIncomingBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem arc {c t : ℝ} (bn : Normal c t) :
    1+(7/10)*c*t≤c+t ∧ t^2≤1/2 ∧ c*t≤1/2 := by
  have b := normal_bounds bn
  have product := mul_nonneg (sub_nonneg.mpr b.2.2.2.2.1)
    (show 0≤1-(7/20)*(c+t+1) by linarith only [b.2.2.2.2.2])
  have ordered := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤c+t by linarith only [b.1,bn.1])
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [product,ordered,bn.2.2,sq_nonneg (c-t)]

private theorem first_margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (order : 0≤C*t-S*c) :
    C*(3/5-c-t+(2/5)*t^2+c*t)-S*(1/2-t^2+(2/5)*c*t+t-c)≤0 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have geometry := arc bn
  let X := 3/5-c-t+(2/5)*t^2+c*t
  let Y := 1/2-t^2+(2/5)*c*t+t-c
  have horizontal : X≤0 := by dsimp [X]; nlinarith only [geometry.1,geometry.2.1,geometry.2.2]
  have parallel : c*X-t*Y=(3/5)*c+t/2-1 := by
    dsimp [X,Y]
    linear_combination (t-1)*bn.2.2
  have short : (3/5)*c+t/2≤1 := by
    nlinarith only [bn.2.2,sq_nonneg (c-3/5),sq_nonneg (t-1/2)]
  by_cases positive : 0<t
  · have first := mul_nonneg order (neg_nonneg.mpr horizontal)
    have last := mul_nonneg an.1 (sub_nonneg.mpr short)
    have scaledParallel := congrArg (fun z : ℝ => S*z) parallel
    have identity : t*(C*X-S*Y)=(C*t-S*c)*X+S*(c*X-t*Y) := by ring
    have scaled : t*(C*X-S*Y)≤0 := by
      nlinarith only [first,last,scaledParallel,identity]
    exact nonpos_of_mul_nonpos_right scaled positive
  · have zero : t=0 := by linarith only [positive,bn.1]
    rw [zero] at order
    have sine : S=0 := by nlinarith only [order,zero,an.1,bb.1]
    have product := mul_nonneg (show 0≤C by linarith only [ab.1])
      (neg_nonneg.mpr horizontal)
    change C*X-S*Y≤0
    rw [sine]
    nlinarith only [product]

private theorem last_margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (order : C*t-S*c≤0) :
    C*(3/5-c-t^2/4+(13/20)*c*t)-
      S*(3/20-(13/20)*t^2-c*t/4+t)≤0 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have geometry := arc bn
  let X := 3/5-c-t^2/4+(13/20)*c*t
  let Y := 3/20-(13/20)*t^2-c*t/4+t
  have parallel : c*X-t*Y=(3/5)*c+t/2-1 := by
    dsimp [X,Y]
    linear_combination ((13/20)*t-1)*bn.2.2
  have short : (3/5)*c+t/2≤1 := by
    nlinarith only [bn.2.2,sq_nonneg (c-3/5),sq_nonneg (t-1/2)]
  have diagonal : X-Y≤0 := by
    dsimp [X,Y]
    nlinarith only [geometry.1,geometry.2.1,geometry.2.2]
  by_cases equal : c=t
  · have same : C=S := by
      rw [← equal] at order
      exact le_antisymm
        ((mul_le_mul_iff_left₀ (show 0<c by linarith only [bb.1])).mp
          (by linarith only [order])) an.2.1
    have product := mul_nonneg (show 0≤C by linarith only [ab.1])
      (neg_nonneg.mpr diagonal)
    change C*X-S*Y≤0
    rw [← same]
    nlinarith only [product]
  · have positive : 0<c-t :=
      sub_pos.mpr ((lt_or_eq_of_le bn.2.1).resolve_right (Ne.symm equal))
    have first := mul_nonneg (sub_nonneg.mpr an.2.1) (sub_nonneg.mpr short)
    have last := mul_nonneg (show 0≤S*c-C*t by linarith only [order])
      (neg_nonneg.mpr diagonal)
    have scaledParallel := congrArg (fun z : ℝ => (C-S)*z) parallel
    have identity : (c-t)*(C*X-S*Y)=
        (C-S)*(c*X-t*Y)+(S*c-C*t)*(X-Y) := by ring
    have scaled : (c-t)*(C*X-S*Y)≤0 := by
      nlinarith only [first,last,scaledParallel,identity]
    exact nonpos_of_mul_nonpos_right scaled positive

/-- Both relative-angle ranges use the complete lower support. When
the transverse coefficient is negative, the genuine B marker supplies
the required opposite face rather than an invented upper bound. -/
theorem upper_u_impossible (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤(13/5)*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*C-(3/2)*S<lower B C (-S)) : False := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let K := C*B.c+S*t
  let H := C*t-S*B.c
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg (by linarith only [ab.1]) (by linarith only [bb.1]))
      (mul_nonneg an.1 bn.1)
  by_cases positive : 0≤H
  · have formula : lower B C (-S)=K*B.loU+H*B.loV := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonneg positive]; ring
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg positive (sub_nonneg.mpr capV)
    have width := mul_nonneg (add_nonneg kp positive) (sub_nonneg.mpr side)
    have identity : K*((13/5)*B.c-t-1)+H*(2*B.c+3*t-1)-(2*C-(3/2)*S)=
        C*(3/5-B.c-t+(2/5)*t^2+B.c*t)-
          S*(1/2-t^2+(2/5)*B.c*t+t-B.c) := by
      dsimp [K,H]
      linear_combination ((13/5)*C-2*S)*bn.2.2
    have margin := first_margin an bn positive
    nlinarith only [formula,first,last,width,identity,margin,incoming]
  · have negative : H≤0 := le_of_lt (lt_of_not_ge positive)
    have formula : lower B C (-S)=K*B.loU+H*(B.loV+B.side) := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonpos negative]; ring
    have marked := (negative_bands B t _ _ signed).mp marker
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg (neg_nonneg.mpr negative)
      (show 0≤B.loV+B.side-((33/20)*B.c+(47/20)*t) by linarith only [marked.2.2.2])
    have width := mul_nonneg kp (sub_nonneg.mpr side)
    have identity : K*((13/5)*B.c-t-1)+H*((33/20)*B.c+(47/20)*t)-(2*C-(3/2)*S)=
        C*(3/5-B.c-t^2/4+(13/20)*B.c*t)-
          S*(3/20-(13/20)*t^2-B.c*t/4+t) := by
      dsimp [K,H]
      linear_combination ((13/5)*C-(33/20)*S)*bn.2.2
    have margin := last_margin an bn negative
    nlinarith only [formula,first,last,width,identity,margin,incoming]

theorem lower_face (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*C-(3/2)*S<lower B C (-S))
    (missing : ¬B.Inside (13/5) 1) : B.c+(13/5)*t≤B.loV := by
  have b := normal_bounds bn
  have marked := (negative_bands B t _ _ signed).mp marker
  by_cases cap : B.loU+B.side≤(13/5)*B.c-t
  · exact False.elim (upper_u_impossible B t an bn signed side marker cap capV incoming)
  · apply le_of_not_gt
    intro low
    apply missing
    apply (negative_bands B t _ _ signed).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marked.1,marked.2.2.2,cap,low,b.1,bn.1,bn.2.1]

#print axioms lower_face
end N12Compact.CentralNegativeIncomingBottom
