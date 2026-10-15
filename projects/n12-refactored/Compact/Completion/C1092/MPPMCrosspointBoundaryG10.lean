import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Low

/-! The complete G10 boundary inequality. The upper-angle range is
simplified from section 8.2 to a uniform rational Cauchy bound. The only
external central inequality is the explicitly stated aligned G00 value. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic
set_option Elab.async false

theorem G10_high_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r)
    (order : h≤r) : 0≤G10 c s d t h r := by
  have eb := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds en
  have rp : 7/10<r := by
    have product := mul_nonneg (sub_nonneg.mpr order) (add_nonneg q.cosine q.sine)
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤7/10-r by linarith only [no])
      (show 0≤7/10+r by linarith only [q.sine])
    nlinarith only [product,square,q.unit]
  have rh : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  have first := mul_nonneg (sub_nonneg.mpr en.2.1) q.sine
  have last := mul_nonneg en.1 (sub_nonneg.mpr order)
  have branch : 0≤deltaE d t h r := by dsimp [deltaE]; nlinarith only [first,last]
  have cap := FC_high_cap c s h r cn steep q order
  have weighted := mul_le_mul_of_nonneg_right cap eb.1.le
  let P := 1+h*r-(1543/1000)*h-(1129/1000)*r
  let Q := r^2-(36/25)*r
  have formula := G10_upper_formula c s d t h r q branch
  have bound : P*d+Q*t+r≤G10 c s d t h r := by
    dsimp [P,Q]
    nlinarith only [formula,weighted]
  have qn : Q≤0 := by
    have product := mul_nonpos_of_nonneg_of_nonpos q.sine
      (show r-36/25≤0 by linarith only [rh])
    dsimp [Q]; nlinarith only [product]
  have chordProduct := mul_nonneg q.cosine (sub_nonneg.mpr order)
  have chord : 1≤r+(3/5)*h := by
    apply le_of_not_gt
    intro no
    have square := mul_pos (show 0<1-(r+(3/5)*h) by linarith only [no])
      (show 0<1+(r+(3/5)*h) by linarith only [q.cosine,q.sine])
    nlinarith only [square,chordProduct,q.unit,sq_nonneg h]
  have weightedChord := mul_nonneg q.cosine
    (show 0≤r+(3/5)*h-1 by linarith only [chord])
  have difference : 0<P-Q := by
    dsimp [P,Q]
    nlinarith only [weightedChord,sq_nonneg (h-543/800),rp,q.unit]
  have angleWeight := mul_nonneg difference.le (sub_nonneg.mpr en.2.1)
  by_cases sum : 0≤P+Q
  · have sumWeight := mul_nonneg sum (show 0≤d+t by linarith only [eb.1,en.1])
    nlinarith only [sumWeight,angleWeight,bound,q.sine]
  · have sum : P+Q≤0 := (lt_of_not_ge sum).le
    have sumWeight := mul_le_mul_of_nonpos_left eb.2.2.2.2.le sum
    have comparison : (71/100)*(P+Q)≤P*d+Q*t := by
      nlinarith only [sumWeight,angleWeight]
    have coarse : 71/50-(11/10)*h-(83/100)*r≤r+(71/100)*(P+Q) := by
      dsimp [P,Q]
      nlinarith only [chordProduct,q.unit,q.cosine,q.sine]
    have norm := C1092MPPMNonpositivePredecessor.norm_le (11/10) (83/100) h r (7/5)
      q.unit (by norm_num) (by norm_num)
    nlinarith only [bound,comparison,coarse,norm]

theorem G10_middle_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (bn : Normal h r) (bs : 3/5≤r)
    (aligned : 0≤G00 h r d t h r) : 0≤G10 c s d t h r := by
  have cap := FC_middle_cap c s h r cn steep bn bs
  have eb := normal_bounds en
  have weighted := mul_nonneg (show 0≤d by linarith only [eb.1])
    (show 0≤(543/500)*r-1-FC c s h r by linarith only [cap])
  have self : h*h+r*r=1 := by nlinarith only [bn.2.2]
  have zero : h*r-r*h=0 := by ring
  have identity : G10 c s d t h r-G00 h r d t h r=
      d*((543/500)*r-1-FC c s h r) := by
    dsimp [G10,G00,k,kC,deltaC,kE,C0]
    rw [self,zero,abs_zero]
    ring
  linarith only [identity,weighted,aligned]

/-- Every closed first-quadrant boundary orientation is covered. Only
the C-aligned member of the central scalar theorem is consumed here. -/
theorem G10_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r)
    (aligned : ∀ a b, Normal a b → 3/5≤b → 0≤G00 a b d t a b) :
    0≤G10 c s d t h r := by
  by_cases low : r≤3/5
  · have cosine : 4/5≤h := by
      have first := mul_nonneg (show 0≤3/5-r by linarith only [low])
        (show 0≤3/5+r by linarith only [q.sine])
      apply le_of_not_gt
      intro no
      have last := mul_pos (show 0<4/5-h by linarith only [no])
        (show 0<4/5+h by linarith only [q.cosine])
      nlinarith only [first,last,q.unit]
    exact G10_low_nonnegative c s d t h r cn steep en q cosine low
  · by_cases high : h≤r
    · exact G10_high_nonnegative c s d t h r cn steep en q high
    · have bn : Normal h r := ⟨q.sine,(lt_of_not_ge high).le,q.unit⟩
      have bs : 3/5≤r := (lt_of_not_ge low).le
      exact G10_middle_nonnegative c s d t h r cn steep en bn bs (aligned h r bn bs)

#print axioms G10_nonnegative
end N12Compact.C1092MPPMCrosspointSupport
