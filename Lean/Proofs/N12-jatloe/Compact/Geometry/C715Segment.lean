import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! The continuous two-lower-points / upper-segment obstruction for C715.
The segment is genuinely excluded, including its endpoints. Both signed
canonical orientations and the zero-sine endpoint are retained. Source only:
compilation is deferred until the complete project has been assembled. -/
namespace N12Compact.C715Segment
open S12 S12Pilot
set_option Elab.async false

private theorem common_interval (a b c d e f : ℝ)
    (ad : a<d) (ae : a<e) (af : a<f)
    (bd : b<d) (be : b<e) (bf : b<f)
    (cd : c<d) (ce : c<e) (cf : c<f) :
    ∃ x, a<x ∧ b<x ∧ c<x ∧ x<d ∧ x<e ∧ x<f := by
  have gap : max a (max b c)<min d (min e f) := by
    exact lt_min (max_lt ad (max_lt bd cd))
      (lt_min (max_lt ae (max_lt be ce)) (max_lt af (max_lt bf cf)))
  obtain ⟨x,low,high⟩ := exists_between gap
  exact ⟨x,(le_max_left _ _).trans_lt low,
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt low,
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt low,
    high.trans_le (min_le_left _ _),
    high.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    high.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩

private theorem normal_margins {c t : ℝ} (cp : 0<c) (tn : 0≤t)
    (order : t≤c) (unit : c^2+t^2=1) :
    c≤1 ∧ 1≤c+t ∧ 1≤c+t-(3/5)*c*t ∧
      1≤c+(3/5)*t*(c+t) ∧ 1≤c+(13/20)*t*(c+t) := by
  have cn := cp.le
  have cu : c≤1 := by nlinarith only [unit,sq_nonneg t,sq_nonneg (c-1)]
  have tu : t≤1 := order.trans cu
  have ct := mul_nonneg cn tn
  have low : 1≤c+t := by nlinarith only [unit,ct,cn,tn]
  have high : c+t≤3/2 := by nlinarith only [unit,sq_nonneg (c-t),cn,tn]
  have strong : 1+(4/5)*c*t≤c+t := by
    nlinarith only [unit,mul_nonneg (sub_nonneg.mpr high) (sub_nonneg.mpr low)]
  have half : 1≤c+t/2 := by
    have product := mul_nonneg tn (show 0≤1+c-2*t by linarith only [tu,order])
    have identity : (1+c)*(c+t/2-1)=t*(1+c-2*t)/2 := by
      linear_combination unit
    have scaled : 0≤(1+c)*(c+t/2-1) := by nlinarith only [identity,product]
    have positive : 0<1+c := by linarith only [cp]
    have result := nonneg_of_mul_nonneg_right scaled positive
    linarith only [result]
  have product := mul_nonneg tn (sub_nonneg.mpr low)
  refine ⟨cu,low,?_,?_,?_⟩ <;> nlinarith only [strong,ct,half,product,tn]

/-- All horizontal-segment separating alternatives are obtained by intersecting
three intervals. There is no unproved separating-axis premise. -/
private theorem positive_segment_bound (q : OpenSquare)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (a : q.Inside (47/20) (13/20)) (b : q.Inside 3 (3/5))
    (avoid : ∀ x : ℝ, 12/5≤x → x≤3 → ¬q.Inside x 1) :
    q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 ∨
      q.loV+q.side≤q.c-3*q.s := by
  by_cases zero : q.s=0
  · have one : q.c=1 := by nlinarith only [q.unit_normal,zero,cp]
    left
    by_contra high
    apply avoid 3 (by norm_num) le_rfl
    have h : 1<q.loV+q.side := by simpa [zero,one] using lt_of_not_ge high
    have bb : q.loU<3 ∧ 3<q.loU+q.side ∧
        q.loV<3/5 ∧ 3/5<q.loV+q.side := by
      simpa [OpenSquare.Inside,InBands,zero,one] using b
    refine ⟨?_,?_,?_,?_⟩ <;>
      simp only [zero,one,zero_mul,one_mul,add_zero,neg_zero,zero_add] <;>
      linarith only [bb.1,bb.2.1,bb.2.2.1,h]
  have sp : 0<q.s := lt_of_le_of_ne sn (Ne.symm zero)
  by_contra both
  obtain ⟨ht,hv⟩ := not_or.mp both
  have top := lt_of_not_ge ht
  have vcap := lt_of_not_ge hv
  have lower : q.s*q.loU+q.c*q.loV<1 := by
    have hu := mul_lt_mul_of_pos_left b.1 sp
    have hv := mul_lt_mul_of_pos_left b.2.2.1 cp
    nlinarith only [hu,hv,q.unit_normal]
  have pU : 12/5<(q.loU+q.side-q.s)/q.c := by
    apply (lt_div_iff₀ cp).mpr
    linarith only [b.2.1,cp,order]
  have pV : 12/5<(q.c-q.loV)/q.s := by
    apply (lt_div_iff₀ sp).mpr
    linarith only [b.2.2.1,cp,sn]
  have uR : (q.loU-q.s)/q.c<3 := by
    apply (div_lt_iff₀ cp).mpr
    linarith only [a.1,cp,sn]
  have uu : (q.loU-q.s)/q.c<(q.loU+q.side-q.s)/q.c := by
    exact (div_lt_div_iff_of_pos_right cp).mpr (by linarith only [q.side_pos])
  have uv : (q.loU-q.s)/q.c<(q.c-q.loV)/q.s := by
    apply (div_lt_div_iff₀ cp sp).mpr
    nlinarith only [lower,q.unit_normal]
  have vR : (q.c-q.loV-q.side)/q.s<3 := by
    apply (div_lt_iff₀ sp).mpr
    linarith only [vcap]
  have vu : (q.c-q.loV-q.side)/q.s<(q.loU+q.side-q.s)/q.c := by
    apply (div_lt_div_iff₀ sp cp).mpr
    nlinarith only [top,q.unit_normal]
  have vv : (q.c-q.loV-q.side)/q.s<(q.c-q.loV)/q.s := by
    exact (div_lt_div_iff_of_pos_right sp).mpr (by linarith only [q.side_pos])
  obtain ⟨x,px,ux,vx,xr,xu,xv⟩ := common_interval (12/5)
    ((q.loU-q.s)/q.c) ((q.c-q.loV-q.side)/q.s) 3
    ((q.loU+q.side-q.s)/q.c) ((q.c-q.loV)/q.s)
    (by norm_num) pU pV uR uu uv vR vu vv
  apply avoid x px.le xr.le
  have ul := (div_lt_iff₀ cp).mp ux
  have uh := (lt_div_iff₀ cp).mp xu
  have vl := (lt_div_iff₀ sp).mp xv
  have vh := (div_lt_iff₀ sp).mp vx
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [ul,uh,vl,vh]

private theorem negative_segment_bound (q : OpenSquare) (t : ℝ)
    (cp : 0<q.c) (tp : 0<t) (order : t≤q.c) (signed : q.s=-t)
    (a : q.Inside (47/20) (13/20)) (b : q.Inside 3 (3/5))
    (avoid : ∀ x : ℝ, 12/5≤x → x≤3 → ¬q.Inside x 1) :
    -t*q.loU+q.c*(q.loV+q.side)≤1 ∨
      q.loV+q.side≤(12/5)*t+q.c := by
  dsimp [OpenSquare.Inside,InBands] at a b
  rw [signed] at a b
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  by_contra both
  obtain ⟨ht,hv⟩ := not_or.mp both
  have top := lt_of_not_ge ht
  have vcap := lt_of_not_ge hv
  have lower : -t*(q.loU+q.side)+q.c*q.loV<1 := by
    have hu := mul_lt_mul_of_pos_left b.2.1 tp
    have hv := mul_lt_mul_of_pos_left b.2.2.1 cp
    nlinarith only [hu,hv,unit]
  have pU : 12/5<(q.loU+q.side+t)/q.c := by
    apply (lt_div_iff₀ cp).mpr
    linarith only [b.2.1,cp,tp]
  have pV : 12/5<(q.loV+q.side-q.c)/t := by
    apply (lt_div_iff₀ tp).mpr
    linarith only [vcap]
  have uR : (q.loU+t)/q.c<3 := by
    apply (div_lt_iff₀ cp).mpr
    linarith only [a.1,cp,order]
  have uu : (q.loU+t)/q.c<(q.loU+q.side+t)/q.c := by
    exact (div_lt_div_iff_of_pos_right cp).mpr (by linarith only [q.side_pos])
  have uv : (q.loU+t)/q.c<(q.loV+q.side-q.c)/t := by
    apply (div_lt_div_iff₀ cp tp).mpr
    nlinarith only [top,unit]
  have vR : (q.loV-q.c)/t<3 := by
    apply (div_lt_iff₀ tp).mpr
    linarith only [b.2.2.1,cp]
  have vu : (q.loV-q.c)/t<(q.loU+q.side+t)/q.c := by
    apply (div_lt_div_iff₀ tp cp).mpr
    nlinarith only [lower,unit]
  have vv : (q.loV-q.c)/t<(q.loV+q.side-q.c)/t := by
    exact (div_lt_div_iff_of_pos_right tp).mpr (by linarith only [q.side_pos])
  obtain ⟨x,px,ux,vx,xr,xu,xv⟩ := common_interval (12/5)
    ((q.loU+t)/q.c) ((q.loV-q.c)/t) 3
    ((q.loU+q.side+t)/q.c) ((q.loV+q.side-q.c)/t)
    (by norm_num) pU pV uR uu uv vR vu vv
  apply avoid x px.le xr.le
  have ul := (div_lt_iff₀ cp).mp ux
  have uh := (lt_div_iff₀ cp).mp xu
  have vl := (div_lt_iff₀ tp).mp vx
  have vh := (lt_div_iff₀ tp).mp xv
  dsimp [OpenSquare.Inside,InBands]
  rw [signed]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [ul,uh,vl,vh]

private theorem positive_impossible (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (a : q.Inside (47/20) (13/20)) (b : q.Inside 3 (3/5))
    (p : ¬q.Inside (12/5) 0) (r : ¬q.Inside 3 0)
    (avoid : ∀ x : ℝ, 12/5≤x → x≤3 → ¬q.Inside x 1) : False := by
  obtain ⟨cu,sum,margin,half,_⟩ := normal_margins cp sn order q.unit_normal
  have rV : -3*q.s≤q.loV := by
    apply le_of_not_gt
    intro low
    apply r
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,b.2.1,b.2.2.2,cp,sn,order,low]
  have top : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 := by
    rcases positive_segment_bound q cp sn order a b avoid with top | cap
    · exact top
    · linarith only [cap,rV,side,cu]
  have choices : (12/5)*q.c≤q.loU ∨ -(12/5)*q.s≤q.loV := by
    by_cases low : (12/5)*q.c≤q.loU
    · exact Or.inl low
    · right
      apply le_of_not_gt
      intro vl
      apply p
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,vl,b.2.1,a.2.2.2,cp,sn]
  rcases choices with pu | pv
  · have u := mul_nonneg sn (sub_nonneg.mpr pu)
    have v := mul_nonneg cp.le (sub_nonneg.mpr rV)
    have excess := mul_pos (sub_pos.mpr side)
      (show 0<q.c+q.s by linarith only [sum])
    nlinarith only [u,v,excess,margin,top]
  · have u := mul_nonneg sn (sub_nonneg.mpr b.2.1.le)
    have v := mul_nonneg cp.le (sub_nonneg.mpr pv)
    have excess := mul_pos cp (sub_pos.mpr side)
    nlinarith only [u,v,excess,half,top]

private theorem negative_impossible (q : OpenSquare) (t : ℝ) (side : 1<q.side)
    (cp : 0<q.c) (tp : 0<t) (order : t≤q.c) (signed : q.s=-t)
    (a : q.Inside (47/20) (13/20)) (b : q.Inside 3 (3/5))
    (p : ¬q.Inside (12/5) 0) (r : ¬q.Inside 3 0)
    (avoid : ∀ x : ℝ, 12/5≤x → x≤3 → ¬q.Inside x 1) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  obtain ⟨cu,sum,margin,_,half⟩ := normal_margins cp tp.le order unit
  have asigned := a
  have bsigned := b
  dsimp [OpenSquare.Inside,InBands] at asigned bsigned
  rw [signed] at asigned bsigned
  have pV : (12/5)*t≤q.loV := by
    apply le_of_not_gt
    intro low
    apply p
    dsimp [OpenSquare.Inside,InBands]
    rw [signed]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [asigned.1,bsigned.2.1,bsigned.2.2.2,cp,tp,order,low]
  have top : -t*q.loU+q.c*(q.loV+q.side)≤1 := by
    rcases negative_segment_bound q t cp tp order signed a b avoid with top | cap
    · exact top
    · linarith only [cap,pV,side,cu]
  have choices : q.loU+q.side≤3*q.c ∨ 3*t≤q.loV := by
    by_cases high : q.loU+q.side≤3*q.c
    · exact Or.inl high
    · right
      apply le_of_not_gt
      intro vl
      apply r
      dsimp [OpenSquare.Inside,InBands]
      rw [signed]
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,vl,bsigned.1,bsigned.2.2.2,cp,tp]
  rcases choices with ru | rv
  · have u := mul_nonneg tp.le (sub_nonneg.mpr ru)
    have v := mul_nonneg cp.le (sub_nonneg.mpr pV)
    have excess := mul_pos (sub_pos.mpr side)
      (show 0<q.c+t by linarith only [sum])
    nlinarith only [u,v,excess,margin,top]
  · have u := mul_nonneg tp.le (sub_nonneg.mpr asigned.1.le)
    have v := mul_nonneg cp.le (sub_nonneg.mpr rv)
    have excess := mul_pos cp (sub_pos.mpr side)
    nlinarith only [u,v,excess,half,top]

/-- A square larger than one cannot contain the two C715 lower points while
missing the two lower exterior points and the entire upper segment. -/
theorem lower_points_upper_segment (q : OpenSquare) (side : 1<q.side)
    (a : q.Inside (47/20) (33/20)) (b : q.Inside 3 (8/5))
    (p : ¬q.Inside (12/5) 1) (r : ¬q.Inside 3 1)
    (avoid : ∀ x : ℝ, 12/5≤x → x≤3 → ¬q.Inside x 2) : False := by
  let shifted : OpenSquare :=
    ⟨q.c,q.s,q.loU-q.s,q.loV-q.c,q.side,q.unit_normal,q.side_pos⟩
  have equivalent (x y : ℝ) : shifted.Inside x y ↔ q.Inside x (y+1) := by
    dsimp [shifted,OpenSquare.Inside,InBands]
    constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
      refine ⟨?_,?_,?_,?_⟩ <;> linarith
  obtain ⟨w,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame shifted
  have sa : w.Inside (47/20) (13/20) :=
    (same _ _).mpr ((equivalent _ _).mpr (by norm_num; exact a))
  have sb : w.Inside 3 (3/5) :=
    (same _ _).mpr ((equivalent _ _).mpr (by norm_num; exact b))
  have sp : ¬w.Inside (12/5) 0 := by
    intro h
    exact p (by simpa using (equivalent _ _).mp ((same _ _).mp h))
  have sr : ¬w.Inside 3 0 := by
    intro h
    exact r (by simpa using (equivalent _ _).mp ((same _ _).mp h))
  have sj (x : ℝ) (low : 12/5≤x) (high : x≤3) : ¬w.Inside x 1 := by
    intro h
    exact avoid x low high (by simpa only [show (1:ℝ)+1=2 by norm_num]
      using (equivalent _ _).mp ((same _ _).mp h))
  have ss : 1<w.side := by simpa only [shape] using side
  by_cases nonnegative : 0≤w.s
  · exact positive_impossible w ss cp nonnegative
      (by simpa only [abs_of_nonneg nonnegative] using canonical) sa sb sp sr sj
  · exact negative_impossible w (-w.s) ss cp
      (by linarith only [nonnegative])
      (by simpa only [abs_of_neg (lt_of_not_ge nonnegative)] using canonical)
      (by ring) sa sb sp sr sj

/-- The segment is supplied by strict membership in one actual foreign square.
No independently fitted segment or approximate hull is substituted. -/
theorem lower_points_foreign_square (q w : OpenSquare) (side : 1<q.side)
    (a : q.Inside (47/20) (33/20)) (b : q.Inside 3 (8/5))
    (p : ¬q.Inside (12/5) 1) (r : ¬q.Inside 3 1)
    (left : w.Inside (113/50) 2) (right : w.Inside (1543/500) 2)
    (apart : ∀ x y, ¬(q.Inside x y ∧ w.Inside x y)) : False := by
  apply lower_points_upper_segment q side a b p r
  intro x low high own
  let t : ℝ := (x-113/50)/(413/500)
  have tn : 0≤t := by
    dsimp [t]
    exact div_nonneg (by linarith only [low]) (by norm_num)
  have tu : t≤1 := by dsimp [t]; apply (div_le_one (by norm_num)).mpr; linarith only [high]
  have foreign : w.Inside x 2 := by
    convert inside_segment w (113/50) 2 (1543/500) 2 t left right tn tu using 1
    · dsimp [t]; ring
    · ring
  exact apart x 2 ⟨own,foreign⟩

end N12Compact.C715Segment
