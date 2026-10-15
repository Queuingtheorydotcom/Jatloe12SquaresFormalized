import Compact.Geometry.C868CentralSeparation

/-! The negative lower-left square has enough support in every nonnegative
canonical direction.  The proof uses its two distinct foreign low points,
and its genuine crosspoints; it does not assume that it owns the centre. -/
namespace N12Compact.C868.LowerNegative
open S12 S12Pilot C977CornerCubic C977NegativeCorner FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

/-- The exact transpose of the existing three-face classification. -/
theorem modes (A : OpenSquare) (hA : Normal A.c (-A.s)) (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (missingBottom : ¬A.Inside (8/5) 1)
    (missingLeft : ¬A.Inside 1 (8/5)) :
    (8/5)*A.c-A.s≤A.loV ∨
      ((8/5)*A.c+A.s≤A.loU ∧ 13*(-A.s)<A.c) ∨
      (A.c+(8/5)*A.s≤A.loU ∧ A.c-(8/5)*A.s≤A.loV) := by
  let q := turnFrame (turnFrame (turnFrame (pullSwap A)))
  have qc : q.c=A.c := by dsimp only [q,turnFrame,pullSwap]; ring
  have qs : q.s= -A.s := by dsimp only [q,turnFrame,pullSwap]; ring
  have qu : q.loU=A.loV := by dsimp only [q,turnFrame,pullSwap]; ring
  have qv : q.loV=A.loU := by dsimp only [q,turnFrame,pullSwap]; ring
  have qi (x y : ℝ) : q.Inside x y↔A.Inside y x := by
    simp only [q,turnFrame_inside,inside_pullSwap]
  have bounds := normal_bounds hA
  have cases := C868CentralSupport.modes q
    (by rw [qc]; linarith only [bounds.1]) (by simpa only [qs] using hA.1)
    (by simpa only [qc,qs] using hA.2.1) side
    ((qi _ _).mpr marker)
    (fun own => missingLeft ((qi _ _).mp own))
    (fun own => missingBottom ((qi _ _).mp own))
  rw [qc,qs,qu,qv] at cases
  rcases cases with first | second | third
  · exact Or.inl (by linarith only [first])
  · exact Or.inr (Or.inl ⟨by linarith only [second.1],second.2⟩)
  · exact Or.inr (Or.inr ⟨by linarith only [third.2],by linarith only [third.1]⟩)

/-- A continuous scalar support bound for all three lower-face modes.
The variables `u,v` are the two upper faces measured from `(2,2)`. -/
private theorem support_scalar (c s C t a u v : ℝ)
    (hn : Normal c s) (ha : Normal C t) (side : 1<a)
    (crosspoint : t/2<u) (near : -(13/50)*t<v)
    (cases : a-t-(2/5)*C≤v ∨
      (a-(2/5)*C+t≤u ∧ 13*t<C) ∨
      (a-C+(2/5)*t≤u ∧ a-C-(2/5)*t≤v)) :
    0<(c*C-s*t)*u+(s*C+c*t)*v := by
  have bn := normal_bounds hn
  have ba := normal_bounds ha
  have cp : 0<c := by linarith only [bn.1]
  have Cp : 0<C := by linarith only [ba.1]
  have ct : 0<c*C := mul_pos cp Cp
  let α := c*C-s*t
  let β := s*C+c*t
  have an : 0≤α := by
    have p := mul_nonneg (sub_nonneg.mpr hn.2.1) Cp.le
    have q := mul_nonneg hn.1 (sub_nonneg.mpr ha.2.1)
    dsimp [α]
    nlinarith only [p,q]
  have bn' : 0≤β := add_nonneg (mul_nonneg hn.1 Cp.le) (mul_nonneg cp.le ha.1)
  have sum : 0<α+β := by
    have p := mul_nonneg cp.le ha.1
    have q := mul_nonneg hn.1 (sub_nonneg.mpr ha.2.1)
    dsimp [α,β]
    nlinarith only [ct,p,q]
  change 0<α*u+β*v
  rcases cases with first | ⟨second,shallow⟩ | ⟨thirdU,thirdV⟩
  · have span : t+(2/5)*C≤1 := by
      nlinarith only [ba.2.2.2.2.2,ha.2.1]
    have up : 0<u := by linarith only [crosspoint,ha.1]
    have vp : 0<v := by linarith only [first,span,side]
    by_cases az : α=0
    · have bp : 0<β := by linarith only [sum,az]
      simpa only [az,zero_mul,zero_add] using mul_pos bp vp
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne an (Ne.symm az)) up)
        (mul_nonneg bn' vp.le)
  · have tsmall : t<1/13 := by linarith only [shallow,ba.2.1]
    have amin : (12/13)*(c*C)≤α := by
      have p := mul_nonneg cp.le (sub_nonneg.mpr shallow.le)
      have q := mul_nonneg ha.1 (sub_nonneg.mpr hn.2.1)
      dsimp [α]
      nlinarith only [p,q]
    have bmax : β≤2*(c*C) := by
      have p := mul_nonneg Cp.le (sub_nonneg.mpr hn.2.1)
      have q := mul_nonneg cp.le (sub_nonneg.mpr ha.2.1)
      dsimp [β]
      nlinarith only [p,q]
    have ap : 0<α := by linarith only [amin,ct]
    have ul : 3/5<u := by linarith only [second,side,ba.2.1,ha.1]
    have vl : -(1/50)<v := by linarith only [near,tsmall]
    have pu := mul_pos ap (sub_pos.mpr ul)
    have pv := mul_nonneg bn' (sub_nonneg.mpr vl.le)
    have margin : 0<(3/5)*α-(1/50)*β := by linarith only [amin,bmax,ct]
    nlinarith only [pu,pv,margin]
  · let f := (1-C)*(C+t)+(2/5)*t*(C-t)
    have fn : 0≤f := add_nonneg
      (mul_nonneg (sub_nonneg.mpr ba.2.1) (add_nonneg Cp.le ha.1))
      (mul_nonneg (mul_nonneg (by norm_num) ha.1) (sub_nonneg.mpr ha.2.1))
    have first := mul_nonneg (sub_nonneg.mpr hn.2.1) fn
    have second := mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hn.1)
        (sub_nonneg.mpr ba.2.1))
      (show 0≤(3/5)*C-2/5 by linarith only [ba.1])
    have identity : α*(1-C+(2/5)*t)+β*(1-C-(2/5)*t)=
        (c-s)*f+2*s*(1-C)*((3/5)*C-2/5) := by
      calc
        _ = (c-s)*f+2*s*(1-C)*((3/5)*C-2/5)
            -(4/5)*s*(C^2+t^2-1) := by dsimp [α,β,f]; ring
        _ = _ := by rw [ha.2.2]; ring
    have margin : 0≤α*(1-C+(2/5)*t)+β*(1-C-(2/5)*t) := by
      rw [identity]
      exact add_nonneg first second
    have pu := mul_nonneg an (sub_nonneg.mpr thirdU)
    have pv := mul_nonneg bn' (sub_nonneg.mpr thirdV)
    have width := mul_pos sum (sub_pos.mpr side)
    nlinarith only [pu,pv,width,margin]

/-- The actual negative lower square extends past the centre in every
nonnegative canonical support direction, without containing that point. -/
theorem support (A : OpenSquare) (c s : ℝ)
    (hn : Normal c s) (hA : Normal A.c (-A.s)) (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (below : A.Inside 2 (3/2)) (near : A.Inside (87/50) 2)
    (missingBottom : ¬A.Inside (8/5) 1)
    (missingLeft : ¬A.Inside 1 (8/5)) :
    2*(c+s)<upper A c s := by
  let C := A.c
  let t := -A.s
  let u := A.loU+A.side-2*A.c-2*A.s
  let v := A.loV+A.side+2*A.s-2*A.c
  have cases := modes A hA side marker missingBottom missingLeft
  have localCases : A.side-t-(2/5)*C≤v ∨
      (A.side-(2/5)*C+t≤u ∧ 13*t<C) ∨
      (A.side-C+(2/5)*t≤u ∧ A.side-C-(2/5)*t≤v) := by
    dsimp [C,t,u,v]
    rcases cases with first | second | third
    · exact Or.inl (by linarith only [first])
    · exact Or.inr (Or.inl ⟨by linarith only [second.1],second.2⟩)
    · exact Or.inr (Or.inr ⟨by linarith only [third.1],by linarith only [third.2]⟩)
  have positive := support_scalar c s C t A.side u v hn hA side
    (by dsimp [t,u]; linarith only [below.2.1])
    (by dsimp [t,v]; linarith only [near.2.2.2]) localCases
  have ba := normal_bounds hA
  have an : 0≤c*A.c+s*A.s := by
    have p := mul_nonneg (sub_nonneg.mpr hn.2.1) (le_trans (by norm_num) ba.1)
    have q := mul_nonneg hn.1 (sub_nonneg.mpr hA.2.1)
    nlinarith only [p,q]
  have bn : 0≤ -c*A.s+s*A.c := by
    have p := mul_nonneg (le_trans hn.1 hn.2.1) hA.1
    have q := mul_nonneg hn.1 (le_trans (by norm_num) ba.1)
    nlinarith only [p,q]
  have formula : upper A c s=2*(c+s)+(c*C-s*t)*u+(s*C+c*t)*v := by
    rw [upper_in_bands,abs_of_nonneg an,abs_of_nonneg bn]
    calc
      _ = 2*(c+s)*(A.c^2+A.s^2)+(c*C-s*t)*u+(s*C+c*t)*v := by
        dsimp [C,t,u,v]; ring
      _ = _ := by rw [A.unit_normal]; ring
  rw [formula]
  linarith only [positive]

/-- With the upper square's genuine centre, every separating normal except
the lower square's upward transverse normal is impossible. -/
theorem only_lower_normal (A H : OpenSquare)
    (hA : Normal A.c (-A.s)) (hH : Normal H.c H.s)
    (same : A.side=H.side) (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aQ : A.Inside (87/50) 2)
    (left : A.Inside (3/2) 2) (below : A.Inside 2 (3/2))
    (northwest : H.Inside (33/20) (47/20))
    (northeast : H.Inside (47/20) (47/20)) (center : H.Inside 2 2)
    (missingBottom : ¬A.Inside (8/5) 1)
    (missingLeft : ¬A.Inside 1 (8/5))
    (apart : ∀ x y,¬(A.Inside x y ∧ H.Inside x y)) :
    A.loV+A.side≤lower H (-A.s) A.c := by
  have ba := normal_bounds hA
  have bh := normal_bounds hH
  have ownSupport := strict_bounds A _ _ A.c A.s A.unit_normal below
  have otherSupport := support A H.c H.s hH hA side marker below aQ
    missingBottom missingLeft
  have alternatives := C868CentralSeparation.alternatives A H
    (by linarith only [ba.1]) (by linarith only [hA.2.1])
    (by linarith only [ba.1,hA.1])
    (by linarith only [bh.1]) (by linarith only [bh.1,hH.1]) hH.2.1
    same marker aD northwest northeast
    (by nlinarith only [ownSupport.2,ba.1,hA.1])
    (by nlinarith only [otherSupport,hH.2.1]) apart
  rcases alternatives with wrong | result
  · have projection := strict_bounds A _ _ (-H.s) H.c
      (by nlinarith only [H.unit_normal]) left
    exfalso
    nlinarith only [wrong,projection.2,center.2.2.1,hH.1]
  · exact result

#print axioms support
#print axioms only_lower_normal
end
end N12Compact.C868.LowerNegative
