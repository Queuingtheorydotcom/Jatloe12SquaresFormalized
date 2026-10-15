import Compact.Geometry.C868CentralSupport

/-! Extend the original southwest support argument to every positive normal
above the diagonal. The target is the southeast marker, which is the lower
of the two merged-owner corner projections in this cone. No sampled angle
or independent support optimization is used. -/
namespace N12Compact.Completion.OtherCases.ThreeCentral
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem normal_coarse {C S : ℝ} (h : Normal C S) :
    7/10 ≤ C ∧ C ≤ 1 ∧ 0 ≤ S ∧ S ≤ 3/4 ∧
      1 ≤ C+S ∧ C+S ≤ 17/12 ∧ C*S ≤ 1/2 := by
  have b := normal_bounds h
  have orderedSquares := mul_nonneg (sub_nonneg.mpr h.2.1)
    (show 0 ≤ C+S by linarith only [b.1,h.1])
  refine ⟨b.1,b.2.1,h.1,?_,b.2.2.2.2.1,?_,?_⟩
  · nlinarith only [h.2.2,orderedSquares,h.1,sq_nonneg (S-3/4)]
  · nlinarith only [h.2.2,sq_nonneg (C-S),sq_nonneg (C+S-17/12)]
  · nlinarith only [h.2.2,sq_nonneg (C-S)]

private theorem steep_linear (c s p q : ℝ) (cn : 0 ≤ c) (order : c ≤ s)
    (diagonal : 0 ≤ p+q) (vertical : 0 ≤ q) : 0 ≤ c*p+s*q := by
  have a := mul_nonneg cn diagonal
  have b := mul_nonneg (sub_nonneg.mpr order) vertical
  nlinarith only [a,b]

private theorem steep_I {c s C S : ℝ} (h : Normal C S)
    (cn : 0 ≤ c) (order : c ≤ s) :
    0 ≤ (c*C+s*S)*(1+(8/5)*C+S)+(s*C-c*S)*(2*C-(87/50)*S)
      -(47/20)*c-(33/20)*s := by
  obtain ⟨cl,cu,sn,su,sum,sumhi,prod⟩ := normal_coarse h
  have orderedSquares := mul_nonneg (sub_nonneg.mpr h.2.1)
    (show 0 ≤ C+S by linarith only [cl,sn])
  have square : S^2 ≤ 1/2 := by nlinarith only [h.2.2,orderedSquares]
  have sumstrong : 1+(4/5)*C*S ≤ C+S := by
    have product := mul_nonneg
      (show 0 ≤ 3/2-(C+S) by linarith only [sumhi]) (sub_nonneg.mpr sum)
    nlinarith only [h.2.2,product]
  let p := C+(8/5)*C^2+(87/50)*S^2-C*S-47/20
  let q := S+2*C^2+S^2-(7/50)*C*S-33/20
  have diagonal : 0 ≤ p+q := by
    dsimp [p,q]
    nlinarith only [h.2.2,sumstrong,square,prod]
  have vertical : 0 ≤ q := by
    have coef : 0 ≤ 1-S-(7/50)*C := by linarith only [su,cu]
    have positive := mul_nonneg sn coef
    dsimp [q]
    nlinarith only [h.2.2,positive]
  have bound := steep_linear c s p q cn order diagonal vertical
  dsimp [p,q] at bound
  nlinarith only [bound]

private theorem steep_II {c s C S : ℝ} (h : Normal C S)
    (cn : 0 ≤ c) (order : c ≤ s) (shallow : 13*S ≤ C) :
    0 ≤ (c*C+s*S)*(2*C+(87/50)*S)+(s*C-c*S)*(1+(8/5)*C-S)
      -(47/20)*c-(33/20)*s := by
  obtain ⟨cl,cu,sn,su,sum,sumhi,prod⟩ := normal_coarse h
  have small : S ≤ 1/13 := by linarith only [shallow,cu]
  have square : S^2 ≤ 1/169 := by
    have b := mul_nonneg sn (sub_nonneg.mpr small)
    nlinarith only [b,small,sn]
  have csharp : 9/10 ≤ C := by
    by_contra smaller
    have product := mul_nonneg (show 0 ≤ C by linarith only [cl])
      (show 0 ≤ 9/10-C by linarith only [smaller])
    nlinarith only [h.2.2,square,cl,smaller,product]
  let p := 2*C^2+(7/50)*C*S+S^2-S-47/20
  let q := C+(8/5)*C^2+(87/50)*S^2+C*S-33/20
  have diagonal : 0 ≤ p+q := by
    dsimp [p,q]
    nlinarith only [h.2.2,csharp,small,square,
      mul_nonneg (show 0 ≤ C by linarith only [cl]) sn]
  have vertical : 0 ≤ q := by
    dsimp [q]
    nlinarith only [h.2.2,csharp,sq_nonneg S,
      mul_nonneg (show 0 ≤ C by linarith only [cl]) sn]
  have bound := steep_linear c s p q cn order diagonal vertical
  dsimp [p,q] at bound
  nlinarith only [bound]

private theorem steep_III {c s C S : ℝ} (h : Normal C S)
    (cn : 0 ≤ c) (order : c ≤ s) :
    0 ≤ (c*C+s*S)*(1+C+(8/5)*S)+(s*C-c*S)*(1+C-(8/5)*S)
      -(47/20)*c-(33/20)*s := by
  obtain ⟨cl,cu,sn,su,sum,sumhi,prod⟩ := normal_coarse h
  let p := C-S+C^2+(3/5)*C*S+(8/5)*S^2-47/20
  let q := C+S+C^2-(3/5)*C*S+(8/5)*S^2-33/20
  have diagonal : 0 ≤ p+q := by
    have product := mul_nonneg (sub_nonneg.mpr cu)
      (show 0 ≤ (6/5)*C-4/5 by linarith only [cl])
    dsimp [p,q]
    nlinarith only [h.2.2,product]
  have vertical : 0 ≤ q := by
    dsimp [q]
    nlinarith only [h.2.2,sum,prod,sq_nonneg S]
  have bound := steep_linear c s p q cn order diagonal vertical
  dsimp [p,q] at bound
  nlinarith only [bound]

/-- The full actual southwest square extends beyond the southeast marker
in every strictly positive normal above the diagonal. -/
theorem steep_support (A : OpenSquare) (c s : ℝ)
    (hA : Normal A.c A.s) (cp : 0 < c) (order : c ≤ s)
    (side : 1 < A.side)
    (southwest : A.Inside (33/20) (33/20))
    (d : A.Inside 2 (87/50)) (q : A.Inside (87/50) 2)
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5)) :
    (47/20)*c+(33/20)*s < upper A c s := by
  have ba := normal_bounds hA
  have ap : 0 < A.c := by linarith only [ba.1]
  have sn : 0 ≤ s := cp.le.trans order
  let α := c*A.c+s*A.s
  let β := s*A.c-c*A.s
  have betaIdentity : -c*A.s+s*A.c = β := by dsimp [β]; ring
  have alpha : 0 < α := add_pos_of_pos_of_nonneg (mul_pos cp ap)
    (mul_nonneg sn hA.1)
  have beta : 0 ≤ β := by
    have first := mul_nonneg (sub_nonneg.mpr order) ap.le
    have second := mul_nonneg cp.le (sub_nonneg.mpr hA.2.1)
    dsimp [β]
    nlinarith only [first,second]
  have formula : upper A c s = α*(A.loU+A.side)+β*(A.loV+A.side) := by
    rw [upper_in_bands,betaIdentity]
    change α*(A.loU+A.side/2)+β*(A.loV+A.side/2)+
      A.side/2*(|α|+|β|)=α*(A.loU+A.side)+β*(A.loV+A.side)
    rw [abs_of_nonneg alpha.le,abs_of_nonneg beta]
    ring
  have wide := mul_pos alpha (sub_pos.mpr side)
  have extra := mul_nonneg beta (sub_nonneg.mpr side.le)
  rcases C868CentralSupport.modes A ap hA.1 hA.2.1 side southwest
      missingBottom missingLeft with branch | ⟨branch,shallow⟩ | ⟨u,v⟩
  · have up := mul_nonneg alpha.le (sub_nonneg.mpr branch)
    have vp := mul_nonneg beta (sub_nonneg.mpr q.2.2.2.le)
    have margin := steep_I hA cp.le order
    change 0 ≤ α*(1+(8/5)*A.c+A.s)+β*(2*A.c-(87/50)*A.s)
      -(47/20)*c-(33/20)*s at margin
    have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) margin)
    apply lt_of_lt_of_eq (lt_add_of_pos_right ((47/20)*c+(33/20)*s) positive)
    rw [formula]
    ring
  · have up := mul_pos alpha (sub_pos.mpr d.2.1)
    have vp := mul_nonneg beta (sub_nonneg.mpr branch)
    have margin := steep_II hA cp.le order shallow.le
    change 0 ≤ α*(2*A.c+(87/50)*A.s)+β*(1+(8/5)*A.c-A.s)
      -(47/20)*c-(33/20)*s at margin
    have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg up vp) extra) margin)
    apply lt_of_lt_of_eq (lt_add_of_pos_right ((47/20)*c+(33/20)*s) positive)
    rw [formula]
    ring
  · have up := mul_nonneg alpha.le (sub_nonneg.mpr u)
    have vp := mul_nonneg beta (sub_nonneg.mpr v)
    have margin := steep_III hA cp.le order
    change 0 ≤ α*(1+A.c+(8/5)*A.s)+β*(1+A.c-(8/5)*A.s)
      -(47/20)*c-(33/20)*s at margin
    have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) extra) margin)
    apply lt_of_lt_of_eq (lt_add_of_pos_right ((47/20)*c+(33/20)*s) positive)
    rw [formula]
    ring

end N12Compact.Completion.OtherCases.ThreeCentral
