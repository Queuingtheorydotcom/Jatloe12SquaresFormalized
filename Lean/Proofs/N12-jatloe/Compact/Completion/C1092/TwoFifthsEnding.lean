import Compact.Completion.C1092.TwoFifthsSoutheastComparison
import Compact.Completion.C1092.TwoFifthsNortheastScalars

/-! The northeast square forbids both closed right-slope intervals at
most 2/5. Together with the southeast comparison this excludes the three
literal physical-square profiles, with arbitrary right orientation. -/
namespace N12Compact.C1092TwoFifths
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports Support Scalars
set_option Elab.async false
noncomputable section

private theorem north_normal (N : OpenSquare) (h : Northeast N) : Normal N.c N.s :=
  ⟨h.sine.le,h.canonical,N.unit_normal⟩

private theorem north_transverse (N : OpenSquare) :
    upper N N.s (-N.c)= -N.loV := by
  simpa only [neg_neg,(ownV N).1] using upper_neg N (-N.s) N.c

private theorem north_longitudinal_blocked (N R : OpenSquare)
    (h : Northeast N) (right : Right R) :
    ¬N.loU+N.side≤lower R N.c N.s := by
  intro sep
  have b := north_bounds N.c N.s (north_normal N h) h.cosine h.sine h.halfLow h.halfHigh
  have last := (strict_bounds R 1 (-13/50) N.c N.s N.unit_normal
    (right.bar _ (by norm_num) (by norm_num))).1
  nlinarith only [h.top.2.1,last,sep,b.ratioLow,h.cosine]

/-- Every closed canonical nonpositive slope through 2/5 is forbidden. -/
theorem northeast_negative_impossible (N R : OpenSquare) (r : ℝ)
    (h : Northeast N) (right : Right R) (same : N.side=R.side)
    (frame : R.s=-r) (normal : Normal R.c r) (small : r≤(2/5)*R.c)
    (apart : ∀ x y,¬(N.Inside x y ∧ R.Inside x y)) : False := by
  let b := N.c
  let t := N.s
  let d := R.c
  let k := b*d-t*r
  let q := t*d+b*r
  let C := b+t-(3/5)*b*t
  let D := b-t-1+(3/5)*t^2
  have nn := north_normal N h
  have nb := north_bounds b t nn h.cosine h.sine h.halfLow h.halfHigh
  have rb := normal_bounds normal
  have dp : 0<d := by dsimp [d]; linarith only [rb.1]
  have kp : 0<k := by
    have first := mul_pos dp
      (show 0<b-(2/5)*t by linarith only [nb.cosineLow,nb.sineHigh])
    have last := mul_nonneg h.sine.le (sub_nonneg.mpr small)
    dsimp [k,b,t,d] at *
    nlinarith only [first,last]
  have qp : 0<q := by
    have first := mul_pos h.sine dp
    have last := mul_nonneg h.cosine.le normal.1
    dsimp [q,b,t,d] at *
    nlinarith only [first,last]
  have L : R.loU<d-(2/5)*r := by
    have point := (right.bar (2/5) (by norm_num) (by norm_num)).1
    rw [frame] at point
    dsimp [d]
    nlinarith only [point]
  have K : R.loV<r-(13/50)*d := by
    have point := (right.bar (-13/50) (by norm_num) (by norm_num)).2.2.1
    rw [frame] at point
    dsimp [d]
    nlinarith only [point]
  have axes := negative_axes N R same h.cosine h.sine.le dp
    (by rw [frame]; linarith only [normal.1]) (7/20) (7/20) h.marker
    (right.bar _ (by norm_num) (by norm_num)) (by norm_num) apart
  rcases axes with own|transverse|wallU|wallV
  · exact north_longitudinal_blocked N R h right own
  · have width := negative_width b t d r nn normal small
    have wp : 0<(2*t+b)*d+b*r := by
      have first := mul_pos (show 0<2*t+b by linarith only [h.cosine,h.sine]) dp
      have last := mul_nonneg h.cosine.le normal.1
      nlinarith only [first,last]
    have wall := wall_lower R right dp.le t (-b) h.sine.le (by linarith only [h.cosine])
    have dot : t*R.c+(-b)*R.s=q := by rw [frame]; dsimp [q,d]; ring
    have cross : -t*R.s+(-b)*R.c= -k := by rw [frame]; dsimp [k,d]; ring
    rw [dot,cross,frame,abs_neg,abs_of_nonneg normal.1,abs_of_pos qp,
      abs_of_neg (neg_neg_of_pos kp)] at wall
    have bound : lower R t (-b)≤2*t-R.side*((2*t+b)*d+b*r)/2 := by
      dsimp [k,q,d] at wall
      nlinarith only [wall]
    have strict := mul_pos (sub_pos.mpr (show 1<R.side by simpa only [same] using h.side)) wp
    have above : R.side-b≤upper N t (-b) := by
      rw [show upper N t (-b)= -N.loV from north_transverse N,←same]
      linarith only [h.upperV]
    nlinarith only [transverse,above,bound,width,strict,nb.upperArc,h.side,same]
  · have formula : upper N R.c R.s=k*(N.loU+N.side)-q*N.loV := by
      have exactSupport := upper_pos_neg N R.c R.s k (-q)
        (by rw [frame]; dsimp [b,t,d,k]; ring)
        (by rw [frame]; dsimp [b,t,d,q]; ring) kp.le (by linarith only [qp])
      rw [exactSupport]
      ring
    have first := mul_nonneg kp.le
      (show 0≤N.loU-(2/5)*t by exact sub_nonneg.mpr h.lowerU)
    have last := mul_nonneg qp.le
      (show 0≤b-N.side-N.loV by linarith only [h.upperV])
    have strict := mul_pos (sub_pos.mpr h.side) (add_pos kp qp)
    have identity : k+q+(2/5)*t*k-b*q=d*C+r*D := by
      dsimp [k,q,C,D,b,t]
      linear_combination -r*N.unit_normal
    have firstGap := mul_pos dp (show 0<C-11/10 by exact sub_pos.mpr nb.coefficient)
    have lastGap := mul_nonneg normal.1
      (show 0≤D+2/5+23/125 by dsimp [D]; linarith only [nb.remainder])
    nlinarith only [wallU,L,formula,first,last,strict,identity,firstGap,lastGap,small,dp]
  · have unit : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
    have first := (strict_bounds N (2/5) 1 (-R.s) R.c unit h.top).2
    rw [frame] at first wallV
    simp only [neg_neg] at first wallV
    nlinarith only [first,wallV,K,small,dp]

/-- Every closed canonical nonnegative slope through 2/5 is forbidden. -/
theorem northeast_positive_impossible (N R : OpenSquare)
    (h : Northeast N) (right : Right R) (same : N.side=R.side)
    (normal : Normal R.c R.s) (small : R.s≤(2/5)*R.c)
    (apart : ∀ x y,¬(N.Inside x y ∧ R.Inside x y)) : False := by
  let b := N.c
  let t := N.s
  let d := R.c
  let r := R.s
  let k := b*d+t*r
  let q := t*d-b*r
  let C := b+t-(3/5)*b*t
  let D := 1+t-b-(3/5)*t^2
  have nn := north_normal N h
  have nb := north_bounds b t nn h.cosine h.sine h.halfLow h.halfHigh
  have rb := normal_bounds normal
  have dp : 0<d := by dsimp [d]; linarith only [rb.1]
  have kp : 0<k := by
    have first := mul_pos h.cosine dp
    have last := mul_nonneg h.sine.le normal.1
    dsimp [k,b,t,d,r] at *
    nlinarith only [first,last]
  have qp : 0<q := by
    have first := mul_pos dp
      (show 0<t-(2/5)*b by linarith only [nb.ratioLow,h.cosine])
    have last := mul_nonneg h.cosine.le (sub_nonneg.mpr small)
    dsimp [q,b,t,d,r] at *
    nlinarith only [first,last]
  have L : R.loU<d := by
    have point := (right.bar 0 (by norm_num) (by norm_num)).1
    dsimp [d]
    nlinarith only [point]
  have axes := positive_axes N R same h.cosine h.sine.le dp normal.1
    (7/20) (7/20) h.marker (right.bar _ (by norm_num) (by norm_num)) (by norm_num) apart
  rcases axes with own|transverse|wallU|wallV
  · exact north_longitudinal_blocked N R h right own
  · have width := positive_width b t d r nn nb normal small
    have wp : 0<(2*t+b)*d+(2*t-b)*r := by
      have first := mul_pos (show 0<2*t+b by linarith only [h.cosine,h.sine]) dp
      have last := mul_nonneg (show 0≤2*t-b by linarith only [nb.sineLow,nb.cosineHigh]) normal.1
      nlinarith only [first,last]
    have wall := wall_lower R right dp.le t (-b) h.sine.le (by linarith only [h.cosine])
    have dot : t*R.c+(-b)*R.s=q := by dsimp [q,d,r]; ring
    have cross : -t*R.s+(-b)*R.c= -k := by dsimp [k,d,r]; ring
    rw [dot,cross,abs_of_nonneg normal.1,abs_of_pos qp,
      abs_of_neg (neg_neg_of_pos kp)] at wall
    have bound : lower R t (-b)≤2*t-R.side*((2*t+b)*d+(2*t-b)*r)/2 := by
      dsimp [k,q,d,r] at wall
      nlinarith only [wall]
    have strict := mul_pos (sub_pos.mpr (show 1<R.side by simpa only [same] using h.side)) wp
    have above : R.side-b≤upper N t (-b) := by
      rw [show upper N t (-b)= -N.loV from north_transverse N,←same]
      linarith only [h.upperV]
    nlinarith only [transverse,above,bound,width,strict,h.side,same]
  · have formula : upper N R.c R.s=k*(N.loU+N.side)-q*N.loV := by
      have exactSupport := upper_pos_neg N R.c R.s k (-q)
        (by dsimp [b,t,d,r,k]; ring) (by dsimp [b,t,d,r,q]; ring)
        kp.le (by linarith only [qp])
      rw [exactSupport]
      ring
    have first := mul_nonneg kp.le
      (show 0≤N.loU-(2/5)*t by exact sub_nonneg.mpr h.lowerU)
    have last := mul_nonneg qp.le
      (show 0≤b-N.side-N.loV by linarith only [h.upperV])
    have strict := mul_pos (sub_pos.mpr h.side) (add_pos kp qp)
    have identity : k+q+(2/5)*t*k-b*q=d*C+r*D := by
      dsimp [k,q,C,D,b,t]
      linear_combination r*N.unit_normal
    have positive : 0<D := by
      have product := mul_pos h.sine
        (show 0<1-(3/5)*t by linarith only [nb.sineHigh])
      dsimp [D]
      nlinarith only [product,nb.cosineHigh]
    have firstGap := mul_pos dp (show 0<C-1 by dsimp [C]; linarith only [nb.coefficient])
    have lastGap := mul_nonneg normal.1 positive.le
    nlinarith only [wallU,L,formula,first,last,strict,identity,firstGap,lastGap]
  · have unit : r^2+(-d)^2=1 := by nlinarith only [R.unit_normal]
    have first := (strict_bounds N (47/100) (3/25) r (-d) unit h.sharp).2
    have last := (strict_bounds R 1 (2/5) r (-d) unit
      (right.bar _ (by norm_num) (by norm_num))).1
    have opposite : lower R r (-d)=-(R.loV+R.side) := by
      simpa only [neg_neg,(ownV R).2] using lower_neg R (-R.s) R.c
    nlinarith only [first,last,wallV,opposite,small,dp]

/-- Continuous three-square squeeze with one actual right square. The
right frame is reindexed once, and the same frame/center is used by both
comparisons. Neither E--N disjointness nor a common-side upper cap is used. -/
theorem impossible (E N R : OpenSquare) (h : Input E N R) : False := by
  obtain ⟨Q,cp,canonical,side,same,cy⟩ := canonical_right R
  have right := h.right.reframe same cy
  have sameE : E.side=Q.side := h.sameER.trans side.symm
  have sameN : N.side=Q.side := h.sameNR.trans side.symm
  have apartE : ∀ x y,¬(E.Inside x y ∧ Q.Inside x y) := by
    intro x y own
    exact h.apartER x y ⟨own.1,(same x y).mp own.2⟩
  have apartN : ∀ x y,¬(N.Inside x y ∧ Q.Inside x y) := by
    intro x y own
    exact h.apartNR x y ⟨own.1,(same x y).mp own.2⟩
  by_cases positive : 0≤Q.s
  · have normal : Normal Q.c Q.s :=
      ⟨positive,by simpa only [abs_of_nonneg positive] using canonical,Q.unit_normal⟩
    have small := southeast_positive_small E Q h.southeast right sameE normal apartE
    exact northeast_positive_impossible N Q h.northeast right sameN normal small.le apartN
  · have negative : Q.s≤0 := (lt_of_not_ge positive).le
    have normal : Normal Q.c (-Q.s) :=
      ⟨neg_nonneg.mpr negative,by simpa only [abs_of_nonpos negative] using canonical,
        by nlinarith only [Q.unit_normal]⟩
    have small := southeast_negative_small E Q (-Q.s) h.southeast right sameE
      (by ring) normal apartE
    exact northeast_negative_impossible N Q (-Q.s) h.northeast right sameN
      (by ring) normal small.le apartN

end
#print axioms northeast_negative_impossible
#print axioms northeast_positive_impossible
#print axioms impossible
end N12Compact.C1092TwoFifths
