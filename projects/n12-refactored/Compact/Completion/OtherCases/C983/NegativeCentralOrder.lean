import Compact.Completion.OtherCases.C983.NegativeRightSeparation

/-! Exact scalar comparisons for the two actual central negative frames.
The two bottom alternatives are retained. These inequalities are ingredients
for the coupled three-square ending, not an exclusion by themselves. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeCentralOrder
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem first_bar_sine_lt (E : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (bar : (4/5)*t-E.c≤E.loV) : t<29/100 := by
  have unit : E.c^2+t^2=1 := by
    simpa only [profile.signed,neg_sq] using E.unit_normal
  have face : 40+11*t<45*E.c := by
    linarith only [bar,profile.sideLarge,profile.sharpUpperV]
  have positive := mul_pos (sub_pos.mpr face)
    (show 0<45*E.c+(40+11*t) by
      linarith only [profile.cosinePositive,profile.sinePositive])
  apply lt_of_not_ge
  intro large
  have square := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤t+29/100 by linarith only [profile.sinePositive])
  nlinarith only [unit,positive,square,large]

theorem north_sine_gt (N : OpenSquare) (side : 1<N.side)
    (profile : TopOnlyQuadrantProfile.Data N) : 29/100< -N.s := by
  let r := -N.s
  have rp : 0<r := by dsimp only [r]; linarith only [profile.sine_neg]
  have unit : N.c^2+r^2=1 := by simpa only [r,neg_sq] using N.unit_normal
  have width : 50*(1-r)<37*N.c := by
    dsimp only [r]
    linarith only [profile.lowerV,profile.upperV,side]
  apply lt_of_not_ge
  intro small
  have upper : r≤29/100 := small
  have one : 0<1-r := by linarith only [upper]
  have first := mul_pos (sub_pos.mpr width)
    (show 0<37*N.c+50*(1-r) by linarith only [profile.cosine_pos,one])
  have last := mul_pos one
    (show 0<1131-3869*r by linarith only [upper])
  nlinarith only [unit,first,last]

theorem upperV_gt_sum (E : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t) (large : 1/5≤t) :
    E.c+t-1<E.loV+E.side := by
  have unit : E.c^2+t^2=1 := by
    simpa only [profile.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t profile.cosinePositive
    profile.sinePositive.le profile.ordered unit
  rcases profile.bar with face | vertex
  · have product := mul_nonneg profile.sinePositive.le (sub_nonneg.mpr large)
    nlinarith only [unit,sq_nonneg (1-E.c),product,face,profile.sideLarge]
  · have first := mul_pos profile.cosinePositive (sub_pos.mpr profile.sideLarge)
    have last := mul_pos profile.sinePositive (sub_pos.mpr profile.upperU)
    have margin := mul_nonneg (sub_nonneg.mpr bounds.2.1)
      (show 0≤E.c+t-1 by linarith only [bounds.2.2.1])
    have scaled : E.c*(E.c+t-1)<E.c*(E.loV+E.side) := by
      nlinarith only [vertex,first,last,margin]
    exact (mul_lt_mul_left profile.cosinePositive).mp scaled

/-- Increasing the nonnegative canonical sine increases the sum, with the
corresponding opposite ordering of cosines. The final comparison controls
the mixed support coefficient without an approximate angle assumption. -/
theorem ordered_normals (c t d r : ℝ)
    (cp : 0<c) (tp : 0<t) (dp : 0<d) (rp : 0<r)
    (order : t≤c) (unit : c^2+t^2=1) (other : d^2+r^2=1)
    (sines : r≤t) : c≤d ∧ d+r≤c+t ∧ 0≤d*t-c*r ∧ c≤r*t+d*c := by
  have sineSquare := mul_nonneg (sub_nonneg.mpr sines)
    (show 0≤t+r by linarith only [tp,rp])
  have cosines : c≤d := by
    apply le_of_not_gt
    intro failure
    have product := mul_pos (sub_pos.mpr failure)
      (show 0<c+d by linarith only [cp,dp])
    nlinarith only [unit,other,sineSquare,product]
  have otherOrder : r≤d := by linarith only [sines,order,cosines]
  have sumProduct := mul_nonneg (sub_nonneg.mpr sines)
    (show 0≤c+d-t-r by linarith only [order,otherOrder])
  have sumIdentity : (c+t-d-r)*(c+d)=(t-r)*(c+d-t-r) := by
    linear_combination unit-other
  have sums : d+r≤c+t := by
    have scaled : 0≤(c+t-d-r)*(c+d) := by rw [sumIdentity]; exact sumProduct
    nlinarith only [scaled,cp,dp]
  have first := mul_nonneg dp.le (sub_nonneg.mpr sines)
  have last := mul_nonneg rp.le (sub_nonneg.mpr cosines)
  have cross : 0≤d*t-c*r := by nlinarith only [first,last]
  have dSmall : d≤1 := by nlinarith only [other,sq_nonneg r,dp]
  have mixedPositive : 0<r*t+d*c := by positivity
  have crossWeight := mul_nonneg rp.le cross
  have unitIdentity : (r*t+d*c)*d-c=r*(d*t-c*r) := by
    linear_combination c*other
  have extra := mul_nonneg mixedPositive.le (sub_nonneg.mpr dSmall)
  have mixed : c≤r*t+d*c := by nlinarith only [crossWeight,unitIdentity,extra]
  exact ⟨cosines,sums,cross,mixed⟩

/-- When E is at least as steep as N, N's two upper face bounds put its
entire lower support below the central sum level in E's transverse direction. -/
theorem north_lower_cap (E N : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) (n : TopOnlyQuadrantProfile.Data N)
    (side : 1<N.side) (order : -N.s≤t) :
    lower N t E.c≤E.c+t-1 := by
  let c := E.c
  let d := N.c
  let r := -N.s
  let A := t*d-c*r
  let B := t*r+c*d
  let P := d+r-(11/25)*d*r
  let Q := d-r+(11/25)*r^2
  have cp : 0<c := e.cosinePositive
  have dp : 0<d := n.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [n.sine_neg]
  have eu : c^2+t^2=1 := by simpa only [c,e.signed,neg_sq] using E.unit_normal
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have comparisons := ordered_normals c t d r cp e.sinePositive dp rp e.ordered eu nu order
  have dr : r≤d := by linarith only [order,e.ordered,comparisons.1]
  have an : 0≤A := by dsimp only [A]; nlinarith only [comparisons.2.2.1]
  have bp : 0<B := by dsimp only [B]; positivity
  have dSmall : d≤1 := by nlinarith only [nu,sq_nonneg r,dp]
  have rSmall : r≤1 := by nlinarith only [nu,sq_nonneg d,rp]
  have qn : 0≤Q := by dsimp only [Q]; nlinarith only [dr,sq_nonneg r]
  have pq : 0≤P-Q := by
    have product := mul_nonneg rp.le
      (show 0≤2-(11/25)*(d+r) by linarith only [dSmall,rSmall])
    dsimp only [P,Q]
    nlinarith only [product]
  have pn : 0≤P := by linarith only [pq,qn]
  have base : r*P+d*Q=1 := by
    dsimp only [P,Q]
    linear_combination nu
  have coefficient : 0≤P*(c+d)-Q*(t+r) := by
    have first := mul_nonneg pn
      (show 0≤c+d-t-r by linarith only [e.ordered,dr])
    have last := mul_nonneg pq
      (show 0≤t+r by linarith only [e.sinePositive,rp])
    nlinarith only [first,last]
  have product := mul_nonneg (sub_nonneg.mpr order) coefficient
  have identity : (c+d)*(t*P+c*Q-1)=
      (t-r)*(P*(c+d)-Q*(t+r)) := by
    linear_combination (c+d)*base+Q*eu-Q*nu
  have support : 1≤t*P+c*Q := by
    have scaled : 0≤(c+d)*(t*P+c*Q-1) := by rw [identity]; exact product
    nlinarith only [scaled,cp,dp]
  have loU : N.loU≤d-(14/25)*r-1 := by
    dsimp only [d,r]
    linarith only [n.upperU,side]
  have loV : N.loV≤d+r-1 := by
    dsimp only [d,r]
    linarith only [n.upperV,side]
  have first := mul_nonneg an (sub_nonneg.mpr loU)
  have last := mul_nonneg bp.le (sub_nonneg.mpr loV)
  have formula : lower N t c=A*N.loU+B*N.loV := by
    have h := C981CompletionSupportForms.lower_negative_pos N r t c
      (by dsimp only [r]; ring) an bp.le
    simpa only [A,B,d] using h
  have final : A*(d-(14/25)*r-1)+B*(d+r-1)=c+t-(t*P+c*Q) := by
    dsimp only [A,B,P,Q]
    linear_combination (c+t)*nu
  change lower N t c≤c+t-1
  rw [formula]
  nlinarith only [first,last,final,support]

/-- The second bottom alternative gives an opposite strict support bound
on N's transverse normal whenever E is at least as steep as N. -/
theorem southeast_upper_floor (E N : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) (n : TopOnlyQuadrantProfile.Data N)
    (bar : -1≤ -t*(E.loU+E.side)+E.c*E.loV) (order : -N.s≤t) :
    N.c-N.s-1<upper E (-N.s) N.c := by
  let c := E.c
  let d := N.c
  let r := -N.s
  let A := r*c-d*t
  let B := r*t+d*c
  let H := E.loV+E.side
  have cp : 0<c := e.cosinePositive
  have dp : 0<d := n.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [n.sine_neg]
  have eu : c^2+t^2=1 := by simpa only [c,e.signed,neg_sq] using E.unit_normal
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have comparisons := ordered_normals c t d r cp e.sinePositive dp rp e.ordered eu nu order
  have an : A≤0 := by dsimp only [A]; nlinarith only [comparisons.2.2.1]
  have bp : 0<B := by dsimp only [B]; positivity
  have formula : upper E r d=A*E.loU+B*H := by
    rw [C981CompletionSupportForms.upper_in_bands,e.signed]
    have first : r*E.c+d*(-t)=A := by dsimp only [A,c]; ring
    have last : -r*(-t)+d*E.c=B := by dsimp only [B,c]; ring
    rw [first,last,abs_of_nonpos an,abs_of_nonneg bp.le]
    dsimp only [H]
    ring
  have identity : c*(A*E.loU+B*H)=
      r*E.loU+B*(c*H-t*E.loU) := by
    dsimp only [A,B]
    linear_combination r*E.loU*eu
  have face : (c+t)*E.side-1≤c*H-t*E.loU := by
    dsimp only [c,H]
    linarith only [bar]
  have first := mul_nonneg bp.le (sub_nonneg.mpr face)
  have extra := mul_pos bp (mul_pos
    (show 0<c+t by linarith only [cp,e.sinePositive])
    (sub_pos.mpr e.sideLarge))
  have origin := mul_nonneg rp.le e.lowerU
  have sums := CommonCases.CanonicalScalars.bounds c t cp e.sinePositive.le e.ordered eu
  have mixed := mul_nonneg (sub_nonneg.mpr comparisons.2.2.2)
    (show 0≤c+t-1 by linarith only [sums.2.2.1])
  have monotone := mul_nonneg cp.le (sub_nonneg.mpr comparisons.2.1)
  have scaled : c*(d+r-1)<c*(A*E.loU+B*H) := by
    nlinarith only [identity,first,extra,origin,mixed,monotone]
  have result := (mul_lt_mul_left cp).mp scaled
  change d+r-1<upper E r d
  rwa [formula]

private theorem central_cone (E N : OpenSquare)
    (elbow : E.Inside (13/50) 0) (sharp : N.Inside (21/40) (1/8))
    (left : N.Inside 0 (31/50)) (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper E nx ny≤lower N nx ny) :
    0<ny ∧ 0<(53/200)*nx+(1/8)*ny := by
  have first := (strict_bounds E _ _ nx ny unit elbow).2
  have last := (strict_bounds N _ _ nx ny unit sharp).1
  have other := (strict_bounds N _ _ nx ny unit left).1
  constructor <;> linarith only [first,last,other,sep]

theorem central_separators (E N : OpenSquare) (t : ℝ) (same : E.side=N.side)
    (e : NegativeTripleFaces.Data E t) (n : TopOnlyQuadrantProfile.Data N)
    (elbow : E.Inside (13/50) 0) (sharp : N.Inside (21/40) (1/8))
    (left : N.Inside 0 (31/50))
    (apart : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)) :
    upper E (-E.s) E.c≤lower N (-E.s) E.c ∨
      upper E (-N.s) N.c≤lower N (-N.s) N.c := by
  have side : 1<N.side := by simpa only [←same] using e.sideLarge
  have bounds := TopOnlyQuadrantScalars.profile_bounds N side n
  have reverse (nx ny : ℝ) (sep : upper N nx ny≤lower E nx ny) :
      upper E (-nx) (-ny)≤lower N (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noU (q : OpenSquare) (cp : 0<q.c) (sn : q.s≤0) (ratio : -q.s≤2*q.c)
      (sep : upper E q.c q.s≤lower N q.c q.s ∨
        upper N q.c q.s≤lower E q.c q.s) : False := by
    rcases sep with forward | backward
    · have direction := central_cone E N elbow sharp left q.c q.s q.unit_normal forward
      linarith only [direction.1,sn]
    · have direction := central_cone E N elbow sharp left (-q.c) (-q.s)
        (by simpa only [neg_sq] using q.unit_normal) (reverse _ _ backward)
      linarith only [direction.2,cp,ratio]
  have noReverseV (q : OpenSquare) (cp : 0<q.c)
      (sep : upper N (-q.s) q.c≤lower E (-q.s) q.c) : False := by
    have opposite : upper E q.s (-q.c)≤lower N q.s (-q.c) := by
      simpa only [neg_neg] using reverse _ _ sep
    have direction := central_cone E N elbow sharp left q.s (-q.c)
      (by nlinarith only [q.unit_normal]) opposite
    linarith only [direction.1,cp]
  have es : E.s≤0 := by rw [e.signed]; linarith only [e.sinePositive]
  have er : -E.s≤2*E.c := by rw [e.signed]; linarith only [e.ordered,e.cosinePositive]
  have nr : -N.s≤2*N.c := by linarith only [bounds.2.2.1,bounds.2.2.2.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint E N same apart
  change pairRadius E N≤|E.c*(centerX N-centerX E)+E.s*(centerY N-centerY E)| ∨
    pairRadius E N≤|-E.s*(centerX N-centerX E)+E.c*(centerY N-centerY E)| ∨
    pairRadius N E≤|N.c*(centerX N-centerX E)+N.s*(centerY N-centerY E)| ∨
    pairRadius N E≤|-N.s*(centerX N-centerX E)+N.c*(centerY N-centerY E)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius E nx ny+supportRadius N nx ny=radius)
      (axis : radius≤|nx*(centerX N-centerX E)+ny*(centerY N-centerY E)|) :=
    separated E N nx ny (by rwa [eq])
  rcases axes with eu | ev | nu | nv
  · exact False.elim (noU E e.cosinePositive es er
      (separate _ _ _ (parallel_radius E N) eu))
  · rcases separate _ _ _ (transverse_radius E N) ev with forward | backward
    · exact Or.inl forward
    · exact False.elim (noReverseV E e.cosinePositive backward)
  · have radius : supportRadius E N.c N.s+supportRadius N N.c N.s=pairRadius N E := by
      rw [add_comm]
      exact parallel_radius N E
    exact False.elim (noU N n.cosine_pos n.sine_neg.le nr
      (separate _ _ _ radius nu))
  · have radius : supportRadius E (-N.s) N.c+supportRadius N (-N.s) N.c=pairRadius N E := by
      rw [add_comm]
      exact transverse_radius N E
    rcases separate _ _ _ radius nv with forward | backward
    · exact Or.inr forward
    · exact False.elim (noReverseV N n.cosine_pos backward)

/-- Actual central disjointness orders their physical negative normals.
The result retains both bottom alternatives and all northeast orientations. -/
theorem sine_lt (E N : OpenSquare) (t : ℝ) (same : E.side=N.side)
    (e : NegativeTripleFaces.Data E t) (n : TopOnlyQuadrantProfile.Data N)
    (elbow : E.Inside (13/50) 0) (sharp : N.Inside (21/40) (1/8))
    (left : N.Inside 0 (31/50))
    (apart : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)) : t< -N.s := by
  apply lt_of_not_ge
  intro order
  have side : 1<N.side := by simpa only [←same] using e.sideLarge
  have north := north_sine_gt N side n
  rcases e.bar with face | vertex
  · have south := first_bar_sine_lt E t e face
    linarith only [north,south,order]
  · rcases central_separators E N t same e n elbow sharp left apart with ev | nv
    · rw [(ownV E).2] at ev
      have separated : E.loV+E.side≤lower N t E.c := by
        simpa only [e.signed,neg_neg] using ev
      have cap := north_lower_cap E N t e n side order
      have gap := upperV_gt_sum E t e (by linarith only [north,order])
      linarith only [separated,cap,gap]
    · rw [(ownV N).1] at nv
      have floor := southeast_upper_floor E N t e n vertex order
      linarith only [floor,nv,n.upperV,side]

theorem cosine_gt_six_sevenths (E : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) : 6/7<E.c := by
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t e.cosinePositive
    e.sinePositive.le e.ordered unit
  rcases e.bar with face | vertex
  · linarith only [face,e.sideLarge,e.sharpUpperV,e.sinePositive]
  · apply lt_of_not_ge
    intro small
    have cSquare := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤6/7+E.c by linarith only [e.cosinePositive])
    have tHalf : 1/2<t := by nlinarith only [unit,cSquare,e.sinePositive]
    have inside := mul_pos (show 0<E.c-1/2 by linarith only [bounds.1])
      (sub_pos.mpr tHalf)
    have sum : 4/3<E.c+t := by
      apply lt_of_not_ge
      intro low
      have interval := mul_nonneg
        (show 0≤E.c+t-1 by linarith only [bounds.2.2.1])
        (show 0≤4/3-(E.c+t) by linarith only [low])
      nlinarith only [unit,inside,interval,low]
    have curve := mul_pos (sub_pos.mpr sum)
      (show 0<1-(21/80)*((E.c+t)+4/3) by
        linarith only [bounds.2.2.2.1])
    have margin : 0<E.c+t-1-(21/40)*E.c*t-(1/8)*E.c^2 := by
      nlinarith only [unit,curve,cSquare]
    have first := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    have last := mul_pos e.sinePositive (sub_pos.mpr e.upperU)
    have cap := mul_nonneg e.cosinePositive.le (sub_nonneg.mpr e.sharpUpperV)
    nlinarith only [vertex,first,last,cap,margin]

/-- The same physical upper-right vertex used by `southeast_vertex` is
never below this fixed rational level. The full bottom alternatives are used. -/
theorem upper_vertex_y_gt (E : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) :
    -1/7< -t*(E.loU+E.side)+E.c*(E.loV+E.side) := by
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t e.cosinePositive
    e.sinePositive.le e.ordered unit
  rcases e.bar with face | vertex
  · have small := first_bar_sine_lt E t e face
    have tSquare := mul_pos (sub_pos.mpr small)
      (show 0<29/100+t by linarith only [e.sinePositive])
    have cosine : 19/20<E.c := by nlinarith only [unit,tSquare,e.cosinePositive]
    have first := mul_pos e.sinePositive (sub_pos.mpr e.elbowLowerU)
    have last := mul_nonneg e.cosinePositive.le (sub_nonneg.mpr face)
    have side := mul_pos
      (show 0<E.c-t by linarith only [cosine,small])
      (sub_pos.mpr e.sideLarge)
    have cMargin := mul_nonneg e.cosinePositive.le (sub_nonneg.mpr bounds.2.1)
    have product := mul_pos e.sinePositive (sub_pos.mpr cosine)
    nlinarith only [first,last,side,cMargin,product,small]
  · have cosine := cosine_gt_six_sevenths E t e
    have extra := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    nlinarith only [vertex,cosine,extra]

theorem north_projection_lt (N : OpenSquare) (side : 1<N.side)
    (n : TopOnlyQuadrantProfile.Data N) : N.c+(-N.s)/7<1 := by
  let r := -N.s
  have rp : 0<r := by dsimp only [r]; linarith only [n.sine_neg]
  have unit : N.c^2+r^2=1 := by simpa only [r,neg_sq] using N.unit_normal
  have large : 29/100<r := north_sine_gt N side n
  have small : r≤1 := by nlinarith only [unit,sq_nonneg N.c,rp]
  apply lt_of_not_ge
  intro failure
  have product := mul_nonneg
    (show 0≤N.c-(1-r/7) by dsimp only [r]; linarith only [failure])
    (show 0≤N.c+(1-r/7) by linarith only [n.cosine_pos,small])
  have positive := mul_pos rp (show 0<50*r-14 by linarith only [large])
  nlinarith only [unit,product,positive]

#print axioms first_bar_sine_lt
#print axioms north_sine_gt
#print axioms upperV_gt_sum
#print axioms ordered_normals
#print axioms north_lower_cap
#print axioms southeast_upper_floor
#print axioms central_separators
#print axioms sine_lt
#print axioms upper_vertex_y_gt
#print axioms north_projection_lt
end N12Compact.Completion.OtherCases.C983.NegativeCentralOrder
