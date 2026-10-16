import Compact.Completion.C981.SupportForms
import Compact.Completion.CommonCases.OriginalOwners
import Compact.Geometry.ClosedFrames
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import S12.ShortCluster.Projections

/-! Translation of C983-F4-TOP-ONLY-8208-ENDING, Section 3, also used
unchanged by C983-F4-MIXED-NEGATIVE-8208-ENDING, Section 3. Coordinates are
translated by (-2,-2). The bottom midpoint is excluded directly from its
actual square; no strict owner is asserted for that midpoint. -/
namespace N12Compact.Completion.OtherCases.C983.F4BottomMidpoint
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

structure SoutheastData (E : OpenSquare) (t : ℝ) : Prop where
  signed : E.s= -t
  sideLarge : 1<E.side
  cosine : 19/20<E.c
  sinePositive : 0<t
  sineSmall : t<3/10
  upperV : E.loV+E.side≤t
  marker : E.Inside (7/20) (-7/20)
  elbow : E.Inside (13/50) 0
  outer : E.Inside 1 (-13/50)

private theorem upper_right_point (E : OpenSquare) (t : ℝ)
    (e : SoutheastData E t) (missing : ¬E.Inside 0 (-1/2)) :
    E.Inside 1 (-1/2) := by
  have m := e.marker
  have d := e.elbow
  have a := e.outer
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,
    mul_one,mul_neg,add_zero,zero_add] at m d a
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have cp : 0<E.c := by linarith only [e.cosine]
  have cu : E.c≤1 := by nlinarith only [unit,sq_nonneg t,cp]
  have lowV : E.loV< -E.c/2 := by
    linarith only [e.upperV,e.sideLarge,e.sineSmall,cu]
  have lowerU : t/2≤E.loU := by
    apply le_of_not_gt
    intro low
    apply missing
    simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,a.2.1,d.2.2.2,lowV,e.cosine,e.sinePositive,e.sineSmall]
  have highU : E.c+t/2<E.loU+E.side := by
    linarith only [lowerU,e.sideLarge,cu]
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_one]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [m.1,highU,a.2.2.2,e.upperV,e.sideLarge,cu,cp,e.sinePositive]

/-- The steep nonnegative bottom sector is excluded by its three genuine
omissions. This is the pair of width contradictions (23)--(26). -/
private theorem positive_bottom (B : OpenSquare) (side : 1<B.side)
    (cp : 0<B.c) (sn : 0≤B.s) (order : B.s≤B.c)
    (steep : (27/50)*B.c<B.s)
    (origin : B.Inside 0 0) (midpoint : B.Inside 0 (1/2))
    (last : B.Inside (4/5) 0)
    (missingMarker : ¬B.Inside (7/20) (13/20))
    (missingTop : ¬B.Inside 0 (37/50))
    (missingSeed : ¬B.Inside (-1/25) (-6/25)) : False := by
  have o := origin
  have m := midpoint
  have z := last
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero,zero_add] at o m z
  have upperU : B.loU+B.side≤(7/20)*B.c+(13/20)*B.s := by
    apply le_of_not_gt
    intro high
    apply missingMarker
    simp only [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,m.2.2.2,o.2.2.1,high,cp,sn,order,steep]
  have upperV : B.loV+B.side≤(37/50)*B.c := by
    apply le_of_not_gt
    intro high
    apply missingTop
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,m.2.2.1,z.2.1,high,cp,sn,order]
  have exits : -(1/25)*B.c-(6/25)*B.s≤B.loU ∨
      (1/25)*B.s-(6/25)*B.c≤B.loV := by
    by_cases first : -(1/25)*B.c-(6/25)*B.s≤B.loU
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro low
      apply missingSeed
      simp only [OpenSquare.Inside,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [first,low,o.2.1,o.2.2.2,cp,sn,order]
  rcases exits with u | v
  · have short := (short_projections B (39/100) (89/100) (by norm_num)).2.1
    linarith only [side,upperU,u,short]
  · have cu : B.c≤1 := by nlinarith only [B.unit_normal,sq_nonneg B.s,cp]
    linarith only [side,upperV,v,cu,sn]

private theorem negative_axis (E : OpenSquare) (t d r : ℝ)
    (e : SoutheastData E t) (dp : 0<d) (rn : 0≤r) (order : r≤d)
    (unit : d^2+r^2=1) : lower E r d< -d/2 := by
  let c := E.c
  let A := c*r-t*d
  let K := t*r+c*d
  have cp : 0<c := by dsimp only [c]; linarith only [e.cosine]
  have eu : c^2+t^2=1 := by simpa only [c,e.signed,neg_sq] using E.unit_normal
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg t,cp]
  have du : d≤1 := by nlinarith only [unit,sq_nonneg r,dp]
  have kp : 0<K := add_pos_of_nonneg_of_pos
    (mul_nonneg e.sinePositive.le rn) (mul_pos cp dp)
  have rotated : A^2+K^2=1 := by
    dsimp only [A,K]
    linear_combination (d^2+r^2)*eu+unit
  have dPoint := e.elbow
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,add_zero]
    at dPoint
  have vLow : E.loV<t-1 := by linarith only [e.upperV,e.sideLarge]
  have base : lower E r d=
      A*(E.loU+E.side/2)+K*(E.loV+E.side/2)-E.side/2*(|A|+K) := by
    rw [C981CompletionSupportForms.lower_in_bands,e.signed]
    have first : r*E.c+d*(-t)=A := by dsimp only [A,c]; ring
    have last : -r*(-t)+d*E.c=K := by dsimp only [K,c]; ring
    rw [first,last,abs_of_nonneg kp.le]
  by_cases an : 0≤A
  · have formula : lower E r d=A*E.loU+K*E.loV := by
      rw [base,abs_of_nonneg an]
      ring
    have first := mul_nonneg an (sub_nonneg.mpr dPoint.1.le)
    have last := mul_pos kp (sub_pos.mpr vLow)
    let X := 13/50+(37/50)*t^2-t
    let Y := 1/2+c*((37/50)*t-1)
    have factor := mul_nonneg (show 0≤3/10-t by linarith only [e.sineSmall])
      (show 0≤1-(37/50)*(t+3/10) by linarith only [e.sineSmall])
    have xn : 0≤X := by dsimp only [X]; nlinarith only [factor]
    have orderedWeight := mul_nonneg xn (sub_nonneg.mpr order)
    have cap := mul_pos (show 0<c-19/20 by exact sub_pos.mpr e.cosine)
      (show 0<1-(37/50)*t by linarith only [e.sineSmall])
    have tSquare := mul_nonneg (show 0≤3/10-t by linarith only [e.sineSmall])
      (show 0≤3/10+t by linarith only [e.sinePositive])
    have sum : X+Y<0 := by
      dsimp only [X,Y]
      nlinarith only [cap,tSquare,e.sinePositive]
    have negative := mul_pos dp (neg_pos.mpr sum)
    have identity : (13/50)*c*A+K*(t-1)+d/2=r*X+d*Y := by
      dsimp only [A,K,X,Y]
      linear_combination (13/50)*r*eu
    rw [formula]
    dsimp only [c] at identity
    nlinarith only [first,last,orderedWeight,negative,identity]
  · have am : A≤0 := le_of_not_ge an
    have formula : lower E r d=A*(E.loU+E.side)+K*E.loV := by
      rw [base,abs_of_nonpos am]
      ring
    have low : -t≤A := by
      have first := mul_nonneg e.sinePositive.le (sub_nonneg.mpr du)
      have last := mul_nonneg cp.le rn
      dsimp only [A]
      nlinarith only [first,last]
    have square := mul_nonneg (show 0≤t+A by linarith only [low])
      (show 0≤t-A by linarith only [e.sinePositive,am])
    have kLarge : c≤K := by
      apply le_of_not_gt
      intro bad
      have product := mul_pos (sub_pos.mpr bad)
        (show 0<c+K by linarith only [cp,kp])
      nlinarith only [eu,rotated,square,product]
    have upperPositive : 0<E.loU+E.side := by linarith only [dPoint.2.1,cp]
    have first := mul_nonneg (neg_nonneg.mpr am) upperPositive.le
    have last := mul_pos kp (sub_pos.mpr vLow)
    have cosineWeight := mul_nonneg (sub_nonneg.mpr kLarge)
      (show 0≤1-t by linarith only [e.sineSmall])
    have floor := mul_pos (sub_pos.mpr e.cosine)
      (show 0<1-t by linarith only [e.sineSmall])
    rw [formula]
    nlinarith only [first,last,cosineWeight,floor,e.sineSmall,du]

/-- Manuscript Theorem 2, with precisely its actual square and omission
premises. The first omitted point belongs to the merged F4 owner; the
second is the separately established Q0 seed. -/
theorem excluded (B E : OpenSquare) (t : ℝ) (same : B.side=E.side)
    (e : SoutheastData E t)
    (marker : B.Inside 0 (-543/500)) (bar : B.Inside (4/5) (-1))
    (missingF : ¬B.Inside 0 (-13/50))
    (missingSeed : ¬B.Inside (-1/25) (-31/25))
    (apart : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)) : ¬B.Inside 0 (-1/2) := by
  intro midpoint
  have missingE : ¬E.Inside 0 (-1/2) := fun h => apart _ _ ⟨midpoint,h⟩
  have outerPoint := upper_right_point E t e missingE
  obtain ⟨q,cp,range,shape,physical,_⟩ := ClosedFrames.canonical_frame B
  have bounds := abs_le.mp range
  have side : 1<q.side := by simpa only [shape,same] using e.sideLarge
  have same' : q.side=E.side := shape.trans same
  have m := (physical _ _).mpr marker
  have z := (physical _ _).mpr bar
  have cPoint := (physical _ _).mpr midpoint
  have o : q.Inside 0 (-1) := CommonCases.OriginalOwners.vertical_segment q 0
    (-543/500) (-1/2) (-1) m cPoint (by norm_num) (by norm_num) (by norm_num)
  have disjoint : ∀ x y,¬(q.Inside x y ∧ E.Inside x y) :=
    fun x y own => apart x y ⟨(physical _ _).mp own.1,own.2⟩
  have unitE : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have ep : 0<E.c := by linarith only [e.cosine]
  have eu : E.c≤1 := by nlinarith only [unitE,sq_nonneg t,ep]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper q nx ny≤lower E nx ny) : 0<nx := by
    have first := (strict_bounds q _ _ nx ny unit cPoint).2
    have last := (strict_bounds E _ _ nx ny unit outerPoint).1
    linarith only [first,last,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower q nx ny) :
      upper q (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noEU (sep : upper q E.c E.s≤lower E E.c E.s ∨
      upper E E.c E.s≤lower q E.c E.s) : False := by
    rcases sep with forward | backward
    · have first := (strict_bounds q _ _ E.c E.s E.unit_normal z).2
      have last := (strict_bounds E _ _ E.c E.s E.unit_normal e.elbow).1
      rw [e.signed] at first last forward
      linarith only [first,last,forward,ep,e.sinePositive]
    · have normal := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [normal,ep]
  have noEV (sep : upper q (-E.s) E.c≤lower E (-E.s) E.c ∨
      upper E (-E.s) E.c≤lower q (-E.s) E.c) : False := by
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    rcases sep with forward | backward
    · have first := (strict_bounds q _ _ (-E.s) E.c unit cPoint).2
      rw [(ownV E).1] at forward
      linarith only [first,forward,e.upperV,e.sideLarge,e.sineSmall,eu]
    · have opposite : upper q E.s (-E.c)≤lower E E.s (-E.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      have normal := cone E.s (-E.c) (by nlinarith only [E.unit_normal]) opposite
      rw [e.signed] at normal
      linarith only [normal,e.sinePositive]
  have noWU (sep : upper q q.c q.s≤lower E q.c q.s ∨
      upper E q.c q.s≤lower q q.c q.s) : False := by
    rcases sep with forward | backward
    · by_cases sign : 0≤q.s
      · by_cases shallow : q.s≤(27/50)*q.c
        · have first := (strict_bounds q _ _ q.c q.s q.unit_normal z).2
          have last := (strict_bounds E _ _ q.c q.s q.unit_normal e.elbow).1
          linarith only [first,last,forward,shallow]
        · apply positive_bottom (q.translated 0 (-1)) side cp sign bounds.2
            (lt_of_not_ge shallow)
          · norm_num [inside_translated_iff]; exact o
          · norm_num [inside_translated_iff]; simpa only [neg_div] using cPoint
          · norm_num [inside_translated_iff]; exact z
          · norm_num [inside_translated_iff]
            exact fun own => disjoint _ _ ⟨own,by simpa only [neg_div] using e.marker⟩
          · norm_num [inside_translated_iff]
            exact fun own => missingF ((physical _ _).mp (by simpa only [neg_div] using own))
          · norm_num [inside_translated_iff]
            exact fun own => missingSeed ((physical _ _).mp (by simpa only [neg_div] using own))
      · have first := (strict_bounds q _ _ q.c q.s q.unit_normal z).2
        have last := (strict_bounds E _ _ q.c q.s q.unit_normal e.elbow).1
        linarith only [first,last,forward,sign,cp]
    · have normal := cone (-q.c) (-q.s)
        (by simpa only [neg_sq] using q.unit_normal) (reverse _ _ backward)
      linarith only [normal,cp]
  have noWV (sep : upper q (-q.s) q.c≤lower E (-q.s) q.c ∨
      upper E (-q.s) q.c≤lower q (-q.s) q.c) : False := by
    have unit : (-q.s)^2+q.c^2=1 := by nlinarith only [q.unit_normal]
    rcases sep with forward | backward
    · by_cases sign : 0≤q.s
      · have normal := cone (-q.s) q.c unit forward
        linarith only [normal,sign]
      · have first := (strict_bounds q _ _ (-q.s) q.c unit cPoint).2
        have last := negative_axis E t q.c (-q.s) e cp
          (by linarith only [sign]) (by linarith only [bounds.1])
          (by simpa only [neg_sq] using q.unit_normal)
        linarith only [first,last,forward]
    · have opposite : upper q q.s (-q.c)≤lower E q.s (-q.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      by_cases sign : 0≤q.s
      · have normalUnit : q.s^2+(-q.c)^2=1 := by nlinarith only [q.unit_normal]
        have first := (strict_bounds q _ _ q.s (-q.c) normalUnit z).2
        have last := (strict_bounds E _ _ q.s (-q.c) normalUnit e.elbow).1
        linarith only [first,last,opposite,cp,sign]
      · have normal := cone q.s (-q.c) (by nlinarith only [q.unit_normal]) opposite
        linarith only [normal,sign]
  have axes := CongruentSAT.faceSeparation_of_disjoint q E same' disjoint
  change pairRadius q E≤|q.c*(centerX E-centerX q)+q.s*(centerY E-centerY q)| ∨
    pairRadius q E≤|-q.s*(centerX E-centerX q)+q.c*(centerY E-centerY q)| ∨
    pairRadius E q≤|E.c*(centerX E-centerX q)+E.s*(centerY E-centerY q)| ∨
    pairRadius E q≤|-E.s*(centerX E-centerX q)+E.c*(centerY E-centerY q)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius q nx ny+supportRadius E nx ny=radius)
      (axis : radius≤|nx*(centerX E-centerX q)+ny*(centerY E-centerY q)|) :=
    separated q E nx ny (by rwa [eq])
  rcases axes with wu | wv | eu | ev
  · exact noWU (separate _ _ _ (parallel_radius q E) wu)
  · exact noWV (separate _ _ _ (transverse_radius q E) wv)
  · have radius : supportRadius q E.c E.s+supportRadius E E.c E.s=pairRadius E q := by
      rw [add_comm]
      exact parallel_radius E q
    exact noEU (separate _ _ _ radius eu)
  · have radius : supportRadius q (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E q := by
      rw [add_comm]
      exact transverse_radius E q
    exact noEV (separate _ _ _ radius ev)

#print axioms excluded

end N12Compact.Completion.OtherCases.C983.F4BottomMidpoint
