import Compact.Completion.C1092.MPPMCrosspointBoundaryAligned

/-! A short algebraic proof of BOUNDARY-SCALARS Lemma 2. In the only
potentially increasing sector, the exact relative-normal remainder is
bounded by .008 j-.05 j². This replaces the chapter's differentiation
and Taylor estimates, including all aligned and zero-angle endpoints. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

theorem FE_low_cap (d t h r : ℝ) (en : Normal d t)
    (q : Quarter h r) (hh : 4/5≤h) (rr : r≤3/5) :
    FE d t h r≤h-(14/25)*r-1+1/3125 := by
  have bn : Normal h r := ⟨q.sine,by linarith only [hh,rr],q.unit⟩
  by_cases order : r≤t
  · have bound := FE_before_aligned_cap bn en order
    dsimp [E0] at bound
    linarith only [bound]
  have order : t≤r := (lt_of_not_ge order).le
  have eb := normal_bounds en
  have bb := normal_bounds bn
  let a := kE d t h r
  let j := deltaE d t h r
  let A := (3/5)*r-(11/25)*h
  let B := (3/5)*h+(11/25)*r
  have an : 0≤a := by
    dsimp [a,kE]
    exact add_nonneg (mul_nonneg (by linarith only [eb.1]) q.cosine)
      (mul_nonneg en.1 q.sine)
  have ah : a≤1 := by dsimp [a,kE]; exact dot_le_one en bn
  have jn : 0≤j := CommonCases.UnitCircleChord.cross_order
    (show 0≤d by linarith only [eb.1]) q.cosine en.2.2 q.unit en.1 q.sine order
  have alow : h≤a := by
    have chord := CommonCases.UnitCircleChord.linear_nonnegative
      (c:=1) (s:=0) (d:=h) (t:=r) (h:=d) (r:=t) (b:=-h) (A:=h) (B:=r)
      (by norm_num) q.cosine (show 0≤d by linarith only [eb.1])
      (by norm_num) q.unit en.2.2 en.1 order q.cosine
      (by ring_nf; exact le_rfl)
      (by nlinarith only [q.unit,bb.2.1])
    dsimp [a,kE]
    nlinarith only [chord]
  have unit : a^2+j^2=1 := by
    dsimp [a,j,kE,deltaE]
    linear_combination (h^2+r^2)*en.2.2+q.unit
  have gapProduct := mul_nonneg (show 0≤1-a by linarith only [ah])
    (show 0≤a-4/5 by linarith only [alow,hh])
  have gap : 1-a≤(5/9)*j^2 := by nlinarith only [unit,gapProduct]
  have chord : 1-r/3≤h := by
    have product := mul_nonneg q.sine
      (show 0≤(1+h)/3-r by linarith only [hh,rr])
    have identity : (1+h)*(h-1+r/3)=r*((1+h)/3-r) := by
      linear_combination q.unit
    have weighted : 0≤(1+h)*(h-1+r/3) := by rw [identity]; exact product
    have result := nonneg_of_mul_nonneg_right weighted (by linarith only [hh] : 0<1+h)
    linarith only [result]
  have Blow : 3/5≤B := by dsimp [B]; linarith only [chord,q.sine]
  have Ahi : A≤1/125 := by dsimp [A]; linarith only [hh,rr]
  have formula : FE d t h r-(h-(14/25)*r-1)=1-a+j*a*A-j^2*B := by
    have branch : 0≤deltaE d t h r := jn
    rw [FE,if_pos branch]
    dsimp [a,j,A,B,kE,deltaE,E0]
    linear_combination (h-(14/25)*r)*en.2.2-
      (d*r-t*h)*((3/5)*t-(11/25)*d)*q.unit
  by_cases sign : A≤0
  · have first := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg jn an) sign
    have last := mul_nonneg (sq_nonneg j)
      (show 0≤B-5/9 by linarith only [Blow])
    nlinarith only [formula,first,last,gap]
  · have sign : 0≤A := (lt_of_not_ge sign).le
    have rlow : 1/2≤r := by dsimp [A] at sign; linarith only [sign,hh]
    have Bstrong : 7/10≤B := by dsimp [B]; linarith only [hh,rlow]
    have first := mul_nonneg jn (show 0≤1/125-A by linarith only [Ahi])
    have second := mul_nonneg (mul_nonneg jn sign)
      (show 0≤1-a by linarith only [ah])
    have last := mul_nonneg (sq_nonneg j)
      (show 0≤B-(5/9+1/20) by linarith only [Bstrong])
    nlinarith only [formula,first,second,last,gap,sq_nonneg (j-2/25)]

end
end N12Compact.C1092MPPMCrosspointSupport
