import Compact.Completion.C1092.MPPMNegativeCrosspointG10Low

/-! NEGATIVE-WALL-SCALARS section 4 above the boundary diagonal.
The rational upper cap uses eta=.35 and the full closed coordinate
u=h/r in [0,1]. The two successor-relative orders meet at equality.
The final dispatcher includes both coordinate endpoints of the quarter
circle. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

def highCore (h r u : ℝ) : ℝ :=
  (1+u^2)*(h+r)-1-(3/2)*u^2-(7/20)*u

/-- The aligned expression on the complete small-u interval. The
circle identity supplies the square-root comparison without radicals. -/
theorem highCore_nonnegative (h r u : ℝ) (q : Quarter h r)
    (rp : 0<r) (ru : r≤1) (un : 0≤u) (small : u≤3/8) (hu : h=u*r) :
    0≤highCore h r u := by
  have radial : r^2*(1+u^2)=1 := by
    have unit := q.unit
    rw [hu] at unit
    nlinarith only [unit]
  have identity : r*((1+u^2)*(h+r)-(1+u))=(1+u)*(1-r) := by
    rw [hu]
    linear_combination (1+u)*radial
  have product := mul_nonneg (show 0≤1+u by linarith only [un])
    (show 0≤1-r by linarith only [ru])
  have base : 0≤(1+u^2)*(h+r)-(1+u) := by
    apply le_of_not_gt
    intro bad
    have negative := mul_neg_of_pos_of_neg rp bad
    linarith only [identity,product,negative]
  have remainder := mul_nonneg un
    (show 0≤13/20-(3/2)*u by linarith only [small])
  dsimp only [highCore]
  nlinarith only [base,remainder]

private theorem large_sum (h r u : ℝ) (q : Quarter h r)
    (high : h≤r) (large : 3/8≤u) (hu : h=u*r) : 32/25≤h+r := by
  have first : 0≤8*h-3*r := by
    have weighted := mul_nonneg q.sine (show 0≤8*u-3 by linarith only [large])
    rw [hu]
    nlinarith only [weighted]
  have last : 0≤8*r-3*h := by linarith only [high,q.sine]
  have product := mul_nonneg first last
  apply le_of_not_gt
  intro small
  have square := mul_pos (show 0<32/25-(h+r) by linarith only [small])
    (show 0<32/25+(h+r) by linarith only [q.cosine,q.sine])
  nlinarith only [product,q.unit,square]

theorem G10_after (c s d t h r : ℝ) (q : Quarter h r)
    (order : 0≤deltaE d t h r) :
    G10 c s d t h r=
      t*(1+h*r-2*h-FC c s h r-(13/50)*r)+d*r*(r-1) := by
  dsimp [G10]
  rw [abs_of_nonneg order]
  dsimp [kE,deltaE,E0]
  linear_combination (t/2)*q.unit

theorem G10_high_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (shallow : 8*t≤3*d) (q : Quarter h r) (high : h≤r) :
    0≤G10 c s d t h r := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have rp : 0<r := by
    apply lt_of_not_ge
    intro zero
    have rr : r=0 := le_antisymm zero q.sine
    have hh : h=0 := by linarith only [high,q.cosine,rr]
    nlinarith only [q.unit,rr,hh]
  have ru : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  let u := h/r
  have un : 0≤u := div_nonneg q.cosine rp.le
  have uu : u≤1 := (div_le_one rp).mpr high
  have hu : h=u*r := (div_mul_cancel₀ h rp.ne').symm
  let H := h+r
  have Hhigh : H≤3/2 := by
    dsimp only [H]
    nlinarith only [q.unit,sq_nonneg (h-r),sq_nonneg (h+r-3/2),q.cosine,q.sine]
  have cap := FC_high_cap c s h r cn q high
  have weighted := mul_le_mul_of_nonneg_left cap en.1
  by_cases before : deltaE d t h r≤0
  · have angle : t≤d*u := by
      apply le_of_not_gt
      intro bad
      have positive := mul_pos rp (sub_pos.mpr bad)
      dsimp only [deltaE] at before
      rw [hu] at before
      nlinarith only [before,positive]
    let A := u*(H-3/2)-7/20
    have An : A≤0 := by
      have product := mul_nonpos_of_nonneg_of_nonpos un
        (show H-3/2≤0 by linarith only [Hhigh])
      dsimp only [A]
      linarith only [product]
    have bound : r*(t*A+d*(H-1))≤G10 c s d t h r := by
      rw [G10_before c s d t h r en q before]
      dsimp only [A,H]
      rw [hu]
      rw [hu] at weighted
      nlinarith only [weighted]
    by_cases small : u≤3/8
    · have core := highCore_nonnegative h r u q rp ru un small hu
      have comparison := mul_nonneg (sub_nonneg.mpr angle) (neg_nonneg.mpr An)
      have comparisonR := mul_nonneg rp.le comparison
      have base := mul_nonneg (mul_nonneg dp.le rp.le) core
      have identity : r*(t*A+d*(H-1))-d*r*highCore h r u=
          r*(t-d*u)*A := by dsimp only [A,H,highCore]; ring
      nlinarith only [identity,comparisonR,base,bound]
    · have large : 3/8≤u := (lt_of_not_ge small).le
      have sum := large_sum h r u q high large hu
      change 32/25≤H at sum
      have sumWeight := mul_nonneg (sub_nonneg.mpr sum)
        (show 0≤1+(3/8)*u by linarith only [un])
      have positive : 0≤H-1+(3/8)*A := by
        dsimp only [A]
        nlinarith only [sumWeight,uu]
      have comparison := mul_nonneg
        (show 0≤3*d/8-t by linarith only [shallow]) (neg_nonneg.mpr An)
      have comparisonR := mul_nonneg rp.le comparison
      have base := mul_nonneg (mul_nonneg rp.le dp.le) positive
      have identity : r*(t*A+d*(H-1))-r*d*(H-1+(3/8)*A)=
          r*(t-3*d/8)*A := by ring
      nlinarith only [identity,comparisonR,base,bound]
  · have after : 0≤deltaE d t h r := (lt_of_not_ge before).le
    have angle : d*u≤t := by
      apply le_of_not_gt
      intro bad
      have positive := mul_pos rp (sub_pos.mpr bad)
      dsimp only [deltaE] at after
      rw [hu] at after
      nlinarith only [after,positive]
    have small : u≤3/8 := by
      apply le_of_not_gt
      intro bad
      have positive := mul_pos dp (show 0<u-3/8 by linarith only [bad])
      nlinarith only [positive,angle,shallow]
    have hh : h≤3/8 := by
      have product := mul_nonneg un (show 0≤1-r by linarith only [ru])
      rw [hu]
      nlinarith only [product,small]
    let A := 1+h*r-(3/2)*h-(7/20)*r
    have Ap : 0<A := by
      have product := mul_nonneg q.cosine q.sine
      dsimp only [A]
      nlinarith only [product,hh,ru]
    have bound : t*A+d*r*(r-1)≤G10 c s d t h r := by
      rw [G10_after c s d t h r q after]
      dsimp only [A]
      nlinarith only [weighted]
    have core := highCore_nonnegative h r u q rp ru un small hu
    have radial : r^2*(1+u^2)=1 := by
      have unit := q.unit
      rw [hu] at unit
      nlinarith only [unit]
    have identity : u*A+r*(r-1)=r*highCore h r u := by
      dsimp only [A,highCore]
      rw [hu]
      linear_combination -u*radial
    have comparison := mul_nonneg (sub_nonneg.mpr angle) Ap.le
    have base := mul_nonneg (mul_nonneg dp.le rp.le) core
    have scaledIdentity := congrArg (fun x : ℝ => d*x) identity
    nlinarith only [comparison,base,scaledIdentity,bound]

/-- Complete closed-quarter-circle dispatcher for G10. The threshold
r=3/5 belongs to the low branch and h=r to the high branch. -/
theorem G10_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (q : Quarter h r) : 0≤G10 c s d t h r := by
  by_cases high : h≤r
  · exact G10_high_nonnegative c s d t h r cn en shallow q high
  · have bn : Normal h r := ⟨q.sine,(lt_of_not_ge high).le,q.unit⟩
    by_cases low : r≤3/5
    · have hh : 4/5≤h := by
        apply le_of_not_gt
        intro small
        have first := mul_pos (show 0<4/5-h by linarith only [small])
          (show 0<4/5+h by linarith only [q.cosine])
        have last := mul_nonneg (show 0≤3/5-r by linarith only [low])
          (show 0≤3/5+r by linarith only [q.sine])
        nlinarith only [first,last,q.unit]
      exact G10_low_nonnegative c s d t h r cn steep en shallow q hh low
    · exact G10_middle_nonnegative c s d t h r cn steep en shallow bn
        (lt_of_not_ge low).le

end
#print axioms G10_high_nonnegative
#print axioms G10_nonnegative
end N12Compact.C1092MPPMNegativeCrosspointSupport
