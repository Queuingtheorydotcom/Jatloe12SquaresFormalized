import Compact.Completion.OtherCases.C983.NegativeCentralOrder
import Compact.Completion.OtherCases.C983.NegativeWallElimination

/-! Exact support bounds for the branch in which both separating normals
belong to the right square. All statements retain the genuine northeast
profile and the two southeast bottom alternatives. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeRightOwned
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

private theorem unit_sum (a b : ℝ) (ap : 0<a) (bn : 0≤b)
    (unit : a^2+b^2=1) : 1+(4/5)*a*b≤a+b := by
  rcases le_total b a with order | order
  · exact (CommonCases.CanonicalScalars.bounds a b ap bn order unit).2.2.2.2
  · have bp : 0<b := lt_of_lt_of_le ap order
    have other := CommonCases.CanonicalScalars.bounds b a bp ap.le order
      (by nlinarith only [unit])
    nlinarith only [other.2.2.2.2]

private theorem upper_pp (q : OpenSquare) (nx ny : ℝ)
    (u : 0≤nx*q.c+ny*q.s) (v : 0≤ -nx*q.s+ny*q.c) :
    upper q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonneg u,abs_of_nonneg v]
  ring

private theorem upper_pn (q : OpenSquare) (nx ny : ℝ)
    (u : 0≤nx*q.c+ny*q.s) (v : -nx*q.s+ny*q.c≤0) :
    upper q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*q.loV := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonneg u,abs_of_nonpos v]
  ring

/-- The northeast support in every surviving right parallel direction
strictly exceeds the parallel coordinate of the point `(1,1)`. -/
theorem north_floor (N : OpenSquare) (side : 1<N.side)
    (profile : TopOnlyQuadrantProfile.Data N) (h k : ℝ)
    (hp : 0<h) (kn : 0≤k) (ku : k<3/4) (unit : h^2+k^2=1) :
    1-k<upper N h (-k) := by
  let d := N.c
  let r := -N.s
  let A := h*d+k*r
  let B := h*r-k*d
  have dp : 0<d := profile.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [profile.sine_neg]
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have ap : 0<A := by dsimp only [A]; positivity
  have hu : h≤1 := by nlinarith only [unit,sq_nonneg k,hp]
  have ru : r≤1 := by nlinarith only [nu,sq_nonneg d,rp]
  have rotated : A^2+B^2=1 := by
    dsimp only [A,B]
    linear_combination (h^2+k^2)*nu+unit
  have highU : 1-r<N.loU+N.side := by
    dsimp only [r]
    linarith only [profile.lowerU,side]
  by_cases bn : 0≤B
  · have highV : 1+(13/50)*d<N.loV+N.side := by
      dsimp only [d]
      linarith only [profile.lowerV,side]
    have formula : upper N h (-k)=A*(N.loU+N.side)+B*(N.loV+N.side) := by
      have result := upper_pp N h (-k)
        (by dsimp only [A,d,r] at ap; nlinarith only [ap])
        (by dsimp only [B,d,r] at bn; nlinarith only [bn])
      simpa only [A,B,d,r,mul_neg,neg_mul,neg_neg,sub_eq_add_neg] using result
    have lowB : B≤r := by
      have first := mul_nonneg rp.le (sub_nonneg.mpr hu)
      have last := mul_nonneg kn dp.le
      dsimp only [B]
      nlinarith only [first,last]
    have order : d≤A := by
      have square := mul_nonneg (sub_nonneg.mpr lowB)
        (show 0≤r+B by linarith only [rp,bn])
      apply le_of_not_gt
      intro bad
      have other := mul_pos (sub_pos.mpr bad)
        (show 0<d+A by linarith only [dp,ap])
      nlinarith only [nu,rotated,square,other]
    have sum := unit_sum A B ap bn rotated
    have margin := mul_nonneg bn
      (show 0≤(4/5)*A-(37/50)*d by linarith only [order,dp])
    have first := mul_pos ap (sub_pos.mpr highU)
    have last := mul_nonneg bn (sub_nonneg.mpr highV.le)
    have identity : A*(1-r)+B*(1+(13/50)*d)-(1-k)=
        A+B-1-(37/50)*d*B := by
      dsimp only [A,B]
      linear_combination -k*nu
    rw [formula]
    nlinarith only [identity,sum,margin,first,last]
  · have bp : 0< -B := by linarith only [bn]
    have lowV : N.loV≤d+r-1 := by
      dsimp only [d,r]
      linarith only [profile.upperV,side]
    have formula : upper N h (-k)=A*(N.loU+N.side)+B*N.loV := by
      have result := upper_pn N h (-k)
        (by dsimp only [A,d,r] at ap; nlinarith only [ap])
        (by dsimp only [B,d,r] at bn; nlinarith only [bn])
      simpa only [A,B,d,r,mul_neg,neg_mul,neg_neg,sub_eq_add_neg] using result
    have sum := unit_sum A (-B) ap bp.le (by nlinarith only [rotated])
    have identity : k*A-r=h*(-B) := by
      dsimp only [A,B]
      linear_combination r*unit
    have product := mul_nonneg hp.le bp.le
    have ratio := mul_pos ap (sub_pos.mpr ku)
    have margin := mul_nonneg bp.le
      (show 0≤(4/5)*A-r by nlinarith only [identity,product,ratio,ap])
    have first := mul_pos ap (sub_pos.mpr highU)
    have last := mul_nonneg bp.le (sub_nonneg.mpr lowV)
    have supportIdentity : A*(1-r)+B*(d+r-1)-(1-k)=A-B-1+B*r := by
      dsimp only [A,B]
      linear_combination -k*nu
    rw [formula]
    nlinarith only [supportIdentity,sum,margin,first,last]

/-- A quantitative northeast margin for the shallow right directions.
The true two-width profile supplies the fixed `26/25` horizontal bound. -/
theorem north_shallow_floor (N : OpenSquare) (side : 1<N.side)
    (profile : TopOnlyQuadrantProfile.Data N) (h k : ℝ)
    (hp : 0<h) (kn : 0≤k) (ku : k≤9/41) (unit : h^2+k^2=1) :
    (26/25)*h-k<upper N h (-k) := by
  let d := N.c
  let r := -N.s
  let A := h*d+k*r
  let B := h*r-k*d
  let M := d+r-(37/50)*d*r
  let Y := d-r+13/50+(37/50)*r^2
  have dp : 0<d := profile.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [profile.sine_neg]
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have data := TopOnlyQuadrantScalars.profile_bounds N side profile
  have sumLower : 31/25≤d+r := by
    dsimp only [d,r]
    linarith only [data.2.2.2.2.1]
  have sumUpper : d+r≤10/7 := by
    dsimp only [d,r]
    linarith only [data.2.2.2.2.2.1]
  have interval := mul_nonneg (sub_nonneg.mpr sumLower) (sub_nonneg.mpr sumUpper)
  have mLower : 26/25<M := by
    dsimp only [M]
    nlinarith only [interval,nu,sumLower]
  have width : 1<(37/50)*d+r := by
    dsimp only [d,r]
    linarith only [profile.lowerV,profile.upperV,side]
  have du : d≤1 := by nlinarith only [nu,sq_nonneg r,dp]
  have yMargin := mul_nonneg (sub_nonneg.mpr du)
    (show 0≤1-(37/50)*d by linarith only [du])
  have yUpper : Y<1 := by
    dsimp only [Y]
    nlinarith only [width,yMargin,nu]
  have rLarge : 29/100<r :=
    NegativeCentralOrder.north_sine_gt N side profile
  have hLarge : 40/41≤h := by
    have square := mul_nonneg (sub_nonneg.mpr ku)
      (show 0≤9/41+k by linarith only [kn])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<40/41+h by linarith only [hp])
    nlinarith only [unit,square,other]
  have ap : 0<A := by dsimp only [A]; positivity
  have bp : 0<B := by
    have first := mul_pos (sub_pos.mpr rLarge) hp
    have second := mul_nonneg kn (sub_nonneg.mpr du)
    dsimp only [B]
    nlinarith only [first,second,hLarge,ku]
  have highU : 1-r<N.loU+N.side := by
    dsimp only [r]
    linarith only [profile.lowerU,side]
  have highV : 1+(13/50)*d<N.loV+N.side := by
    dsimp only [d]
    linarith only [profile.lowerV,side]
  have formula : upper N h (-k)=A*(N.loU+N.side)+B*(N.loV+N.side) := by
    have result := upper_pp N h (-k)
      (by dsimp only [A,d,r] at ap; nlinarith only [ap])
      (by dsimp only [B,d,r] at bp; nlinarith only [bp])
    simpa only [A,B,d,r,mul_neg,neg_mul,neg_neg,sub_eq_add_neg] using result
  have first := mul_pos ap (sub_pos.mpr highU)
  have last := mul_nonneg bp.le (sub_nonneg.mpr highV.le)
  have xWeight := mul_pos hp (sub_pos.mpr mLower)
  have yWeight := mul_nonneg kn (sub_nonneg.mpr yUpper.le)
  have identity : A*(1-r)+B*(1+(13/50)*d)=h*M-k*Y := by
    dsimp only [A,B,M,Y]
    linear_combination -(13/50)*k*nu
  rw [formula]
  nlinarith only [first,last,xWeight,yWeight,identity]

private theorem southeast_first_minorant (E : OpenSquare) (t h k : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (bar : (4/5)*t-E.c≤E.loV) (hp : 0<h) (kn : 0≤k) :
    let P := k*E.c-h*t
    let Q := k*t+h*E.c
    (0≤P → P+Q*(1+(4/5)*t-E.c)<upper E k h) ∧
    (P≤0 → (13/50)*E.c*P+Q*(1+(4/5)*t-E.c)<upper E k h) := by
  dsimp only
  have qp : 0<k*t+h*E.c :=
    add_pos_of_nonneg_of_pos (mul_nonneg kn profile.sinePositive.le)
      (mul_pos hp profile.cosinePositive)
  have highV : 1+(4/5)*t-E.c<E.loV+E.side := by
    linarith only [bar,profile.sideLarge]
  have last := mul_pos qp (sub_pos.mpr highV)
  constructor
  · intro pn
    have first := mul_nonneg pn (sub_nonneg.mpr profile.upperU.le)
    have formula : upper E k h=(k*E.c-h*t)*(E.loU+E.side)+
        (k*t+h*E.c)*(E.loV+E.side) := by
      rw [C981CompletionSupportForms.upper_in_bands,profile.signed]
      have a : k*E.c+h*(-t)=k*E.c-h*t := by ring
      have b : -k*(-t)+h*E.c=k*t+h*E.c := by ring
      rw [a,b,abs_of_nonneg pn,abs_of_nonneg qp.le]
      ring
    rw [formula]
    nlinarith only [first,last]
  · intro pn
    have first := mul_nonneg (neg_nonneg.mpr pn)
      (sub_nonneg.mpr profile.elbowLowerU.le)
    have formula : upper E k h=(k*E.c-h*t)*E.loU+
        (k*t+h*E.c)*(E.loV+E.side) := by
      rw [C981CompletionSupportForms.upper_in_bands,profile.signed]
      have a : k*E.c+h*(-t)=k*E.c-h*t := by ring
      have b : -k*(-t)+h*E.c=k*t+h*E.c := by ring
      rw [a,b,abs_of_nonpos pn,abs_of_nonneg qp.le]
      ring
    rw [formula]
    nlinarith only [first,last]

/-- First-bar support when E is steeper than the right frame. The retained
`13/50` lower-U bound is essential in the negative support coefficient. -/
private theorem first_steeper (c t h k : ℝ)
    (cp : 0<c) (tp : 0<t) (hp : 0<h) (kn : 0≤k)
    (eu : c^2+t^2=1) (ru : h^2+k^2=1)
    (order : k*c-h*t≤0) :
    1+(4/5)*k-h≤(13/50)*c*(k*c-h*t)+
      (k*t+h*c)*(1+(4/5)*t-c) := by
  let b := h*t-k*c
  let Q := h*c+k*t
  have bn : 0≤b := by dsimp only [b]; linarith only [order]
  have qp : 0<Q := by
    dsimp only [Q]
    positivity
  have rotated : Q^2+b^2=1 := by
    dsimp only [Q,b]
    linear_combination (h^2+k^2)*eu+ru
  have qu : Q≤1 := by nlinarith only [rotated,sq_nonneg b,qp]
  have hu : h≤1 := by nlinarith only [ru,sq_nonneg k,hp]
  have bu : b≤t := by
    have first := mul_nonneg tp.le (sub_nonneg.mpr hu)
    have last := mul_nonneg kn cp.le
    dsimp only [b]
    nlinarith only [first,last]
  have identity : (13/50)*c*(k*c-h*t)+(k*t+h*c)*(1+(4/5)*t-c)-
      (1+(4/5)*k-h)=b*((27/50)*c+t)-(1-Q) := by
    dsimp only [b,Q]
    linear_combination ((4/5)*k-h)*eu
  have first := mul_nonneg bn (sub_nonneg.mpr bu)
  have last := mul_nonneg qp.le (sub_nonneg.mpr qu)
  have extra := mul_nonneg bn cp.le
  nlinarith only [identity,rotated,first,last,extra]

/-- A shallow right frame always receives the exact first-bar minorant,
including the change of supporting vertex when E is steeper. -/
theorem southeast_first_shallow (E : OpenSquare) (t h k : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (bar : (4/5)*t-E.c≤E.loV) (hp : 0<h) (kn : 0≤k)
    (ku : k≤9/41) (unit : h^2+k^2=1) :
    1+(4/5)*k-h<upper E k h := by
  let c := E.c
  let P := k*c-h*t
  let Q := h*c+k*t
  have cp : 0<c := profile.cosinePositive
  have eu : c^2+t^2=1 := by simpa only [c,profile.signed,neg_sq] using E.unit_normal
  have minor := southeast_first_minorant E t h k profile bar hp kn
  have qp : 0<Q := by
    have tp := profile.sinePositive
    dsimp only [Q]
    positivity
  have rotated : P^2+Q^2=1 := by
    dsimp only [P,Q]
    linear_combination (h^2+k^2)*eu+unit
  have qu : Q≤1 := by nlinarith only [rotated,sq_nonneg P,qp]
  have hLarge : 40/41≤h := by
    have square := mul_nonneg (sub_nonneg.mpr ku)
      (show 0≤9/41+k by linarith only [kn])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<40/41+h by linarith only [hp])
    nlinarith only [unit,square,other]
  by_cases pn : 0≤P
  · have sineIdentity : k*Q-h*P=t := by
      dsimp only [P,Q]
      linear_combination t*unit
    have first := mul_nonneg kn (sub_nonneg.mpr qu)
    have last := mul_nonneg hp.le pn
    have tk : t≤k := by nlinarith only [sineIdentity,first,last]
    have tu : t≤9/41 := le_trans tk ku
    have cLarge : 40/41≤c := by
      have square := mul_nonneg (sub_nonneg.mpr tu)
        (show 0≤9/41+t by linarith only [profile.sinePositive])
      apply le_of_not_gt
      intro bad
      have other := mul_pos (sub_pos.mpr bad)
        (show 0<40/41+c by linarith only [cp])
      nlinarith only [eu,square,other]
    have delta : c-40/41≤(9/40)*(9/41-t) := by
      have first := mul_nonneg (sub_nonneg.mpr cLarge)
        (show 0≤c+40/41-80/41 by linarith only [cLarge])
      have last := mul_nonneg (sub_nonneg.mpr tu)
        (show 0≤18/41-(9/41+t) by linarith only [tu])
      nlinarith only [first,last,eu]
    have coefficient : (41/50)*(9/41-t)≤1-(4/5)*c-t := by
      linarith only [delta]
    have gap : 0≤9/41-t := sub_nonneg.mpr tu
    have scaled := mul_nonneg gap
      (show 0≤h+c-80/41 by linarith only [hLarge,cLarge])
    have margin : 0≤(h+c)*(1-(4/5)*c-t)-(k-t) := by
      have weight := mul_nonneg (show 0≤h+c by linarith only [hp,cp])
        (sub_nonneg.mpr coefficient)
      nlinarith only [weight,scaled,ku,tu]
    have halfIdentity : (1-Q)*(h+c)=P*(k-t) := by
      dsimp only [P,Q]
      linear_combination -h*eu-c*unit
    have weight := mul_nonneg pn margin
    have difference : 0≤P*(1-(4/5)*c-t)-(1-Q) := by
      have scaled : 0≤(h+c)*(P*(1-(4/5)*c-t)-(1-Q)) := by
        nlinarith only [weight,halfIdentity]
      nlinarith only [scaled,hp,cp]
    have identity : P+Q*(1+(4/5)*t-c)-(1+(4/5)*k-h)=
        P*(1-(4/5)*c-t)-(1-Q) := by
      dsimp only [P,Q]
      linear_combination ((4/5)*k-h)*eu
    have support := minor.1 pn
    dsimp only [P,Q,c] at identity difference ⊢
    nlinarith only [identity,difference,support]
  · have support := minor.2 (le_of_not_ge pn)
    have floor := first_steeper c t h k cp profile.sinePositive hp kn eu unit
      (by dsimp only [P] at pn; linarith only [pn])
    dsimp only [c] at floor
    linarith only [support,floor]

/-- The shallow first-bar subcase already contradicts the real right wall. -/
theorem first_bar_shallow_impossible (E N R : OpenSquare)
    (input : RightTripleData.Input E N R)
    (bar : (4/5)*(-E.s)-E.c≤E.loV)
    (shallow : -R.s≤9/41)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  let h := R.c
  let k := -R.s
  have hp : 0<h := input.rightFaces.cosinePositive
  have kn : 0≤k := by dsimp only [k]; linarith only [input.rightFaces.sineNonpositive]
  have unit : h^2+k^2=1 := by simpa only [h,k,neg_sq] using R.unit_normal
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have sideR : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
  have nFloor := north_shallow_floor N sideN input.northeastFaces h k hp kn shallow unit
  have eFloor := southeast_first_shallow E (-E.s) h k input.southeastFaces bar hp kn shallow unit
  rw [(ownU R).1] at north
  rw [(ownV R).1] at south
  have nFace : (26/25)*h-k<R.loU := by
    dsimp only [h,k] at nFloor
    simp only [neg_neg] at nFloor
    exact lt_of_lt_of_le nFloor north
  have eFace : 1+(4/5)*k-h<R.loV := lt_of_lt_of_le eFloor south
  have wall : h*(R.loU+R.side)+k*(R.loV+R.side)≤2 := by
    dsimp only [h,k]
    nlinarith only [input.rightFaces.realWall]
  exact NegativeWallElimination.shallow_impossible h k R.loU R.loV R.side
    hp kn unit sideR shallow nFace eFace wall

/-- The unit-side second-bar support, for either sign of the relative
parallel coefficient. This is a scalar statement and introduces no square. -/
private theorem second_scalar (c t h k : ℝ)
    (cp : 0<c) (tp : 0<t) (order : t≤c) (hp : 0<h) (kn : 0≤k)
    (eu : c^2+t^2=1) (ru : h^2+k^2=1) :
    let P := k*c-h*t
    let Q := k*t+h*c
    (0≤P → 1-(1-k)/h≤P+Q*(1-(1-t)/c)) ∧
    (P≤0 → 1-(1-k)/h≤Q*(1-(1-t)/c)) := by
  let P := k*c-h*t
  let Q := k*t+h*c
  let e := (1-t)/c
  let r := (1-k)/h
  have qp : 0<Q := by
    dsimp only [Q]
    positivity
  have rotated : P^2+Q^2=1 := by
    dsimp only [P,Q]
    linear_combination (h^2+k^2)*eu+ru
  have qu : Q≤1 := by nlinarith only [rotated,sq_nonneg P,qp]
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg t,cp]
  have tu : t≤1 := le_trans order cu
  have hu : h≤1 := by nlinarith only [ru,sq_nonneg k,hp]
  have ku : k≤1 := by nlinarith only [ru,sq_nonneg h,kn]
  have en : 0≤e := by dsimp only [e]; exact div_nonneg (sub_nonneg.mpr tu) cp.le
  have rn : 0≤r := by dsimp only [r]; exact div_nonneg (sub_nonneg.mpr ku) hp.le
  have ec : c*e=1-t := by dsimp only [e]; field_simp [ne_of_gt cp]
  have es : (1+t)*e=c := by
    dsimp only [e]
    apply (mul_right_cancel₀ (ne_of_gt cp))
    field_simp [ne_of_gt cp]
    nlinarith only [eu]
  have rh : h*r=1-k := by dsimp only [r]; field_simp [ne_of_gt hp]
  have rs : (1+k)*r=h := by
    dsimp only [r]
    apply (mul_right_cancel₀ (ne_of_gt hp))
    field_simp [ne_of_gt hp]
    nlinarith only [ru]
  change (0≤P → 1-r≤P+Q*(1-e)) ∧ (P≤0 → 1-r≤Q*(1-e))
  constructor
  · intro pn
    have sineIdentity : k*Q-h*P=t := by
      dsimp only [P,Q]
      linear_combination t*ru
    have cosineIdentity : h*Q+k*P=c := by
      dsimp only [P,Q]
      linear_combination c*ru
    have first := mul_nonneg kn (sub_nonneg.mpr qu)
    have last := mul_nonneg hp.le pn
    have tk : t≤k := by nlinarith only [sineIdentity,first,last]
    have square := mul_nonneg (sub_nonneg.mpr tk)
      (show 0≤t+k by linarith only [tp,kn])
    have hc : h≤c := by
      apply le_of_not_gt
      intro bad
      have other := mul_pos (sub_pos.mpr bad)
        (show 0<h+c by linarith only [hp,cp])
      nlinarith only [eu,ru,square,other]
    have firstGap := mul_nonneg hp.le (sub_nonneg.mpr qu)
    have lastGap := mul_nonneg pn (sub_nonneg.mpr ku)
    have gapIdentity : c*h*(e-r)=h-c+P := by
      dsimp only [e,r,P]
      field_simp [ne_of_gt cp,ne_of_gt hp]
      ring
    have gap : 0≤e-r := by
      have scaled : 0≤c*h*(e-r) := by
        nlinarith only [gapIdentity,cosineIdentity,firstGap,lastGap]
      nlinarith only [scaled,mul_pos cp hp]
    have supportIdentity : P+Q*(1-e)=k+(1-c)*(k*e-h) := by
      calc
        _ = k+(1-c)*(k*e-h)+
            k*(c+t-1-(1+t)*e+c*e)+h*(1-t-c*e) := by
              dsimp only [P,Q]
              ring
        _ = _ := by rw [ec,es]; ring
    have targetIdentity : 1-r=k-(1-h)*r := by nlinarith only [rh]
    have decomposition : P+Q*(1-e)-(1-r)=
        (c-h)*r+(1-c)*k*(e-r) := by
      rw [supportIdentity,targetIdentity]
      calc
        _ = (c-h)*r+(1-c)*k*(e-r)+(1-c)*((1+k)*r-h) := by ring
        _ = _ := by rw [rs]; ring
    have a := mul_nonneg (sub_nonneg.mpr hc) rn
    have b := mul_nonneg (mul_nonneg (sub_nonneg.mpr cu) kn) gap
    nlinarith only [decomposition,a,b]
  · intro pn
    have bn : 0≤ -P := neg_nonneg.mpr pn
    have sum := unit_sum Q (-P) qp bn (by nlinarith only [rotated])
    have eSmall : e≤1 := by
      have csum := CommonCases.CanonicalScalars.bounds c t cp tp.le order eu
      nlinarith only [ec,cp,csum.2.2.1]
    have productBound : (1+t)*(1-e)≤1 := by nlinarith only [es,order]
    have identity : (1+t)*(r-e)= -P+r*(1-Q) := by
      calc
        _ = -P+r*(1-Q)+r*(t+Q)-(c-P) := by nlinarith only [es]
        _ = -P+r*(1-Q)+c*(h*r-(1-k))+t*((1+k)*r-h) := by
          dsimp only [P,Q]
          ring
        _ = _ := by rw [rh,rs]; ring
    have first := mul_nonneg rn (sub_nonneg.mpr qu)
    have last := mul_nonneg (sub_nonneg.mpr qu) (sub_nonneg.mpr productBound)
    have scaled : 0≤(1+t)*(Q*(1-e)-(1-r)) := by
      nlinarith only [identity,sum,first,last,mul_nonneg qp.le bn]
    nlinarith only [scaled,tp]

/-- The true second bottom alternative gives the universal southeast
support bound needed by the right wall, with no orientation ordering. -/
theorem southeast_second_floor (E : OpenSquare) (t h k : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (bar : -1≤ -t*(E.loU+E.side)+E.c*E.loV)
    (hp : 0<h) (kn : 0≤k) (unit : h^2+k^2=1) :
    1-(1-k)/h<upper E k h := by
  let c := E.c
  let P := k*c-h*t
  let Q := k*t+h*c
  have cp : 0<c := profile.cosinePositive
  have eu : c^2+t^2=1 := by simpa only [c,profile.signed,neg_sq] using E.unit_normal
  have qp : 0<Q := by
    have tp := profile.sinePositive
    dsimp only [Q]
    positivity
  have comparison := second_scalar c t h k cp profile.sinePositive
    profile.ordered hp kn eu unit
  have face : 0≤1-t*(E.loU+E.side)+c*E.loV := by
    dsimp only [c]
    linarith only [bar]
  have weight := mul_nonneg qp.le face
  have uWeight := mul_nonneg kn profile.lowerU
  by_cases pn : 0≤P
  · have formula : upper E k h=P*(E.loU+E.side)+Q*(E.loV+E.side) := by
      rw [C981CompletionSupportForms.upper_in_bands,profile.signed]
      have a : k*E.c+h*(-t)=P := by dsimp only [P,c]; ring
      have b : -k*(-t)+h*E.c=Q := by dsimp only [Q,c]; ring
      rw [a,b,abs_of_nonneg pn,abs_of_nonneg qp.le]
      ring
    have sideWeight := mul_pos
      (show 0<k+c*Q by have q := mul_pos cp qp; linarith only [q,kn])
      (sub_pos.mpr profile.sideLarge)
    have supportIdentity : c*(P*(E.loU+E.side)+Q*(E.loV+E.side))=
        k*E.loU+(k+c*Q)*E.side-Q+
        Q*(1-t*(E.loU+E.side)+c*E.loV) := by
      dsimp only [P,Q]
      linear_combination k*(E.loU+E.side)*eu
    have minorIdentity : c*(P+Q*(1-(1-t)/c))=k+c*Q-Q := by
      have cancellation : c*((1-t)/c)=1-t := by field_simp [ne_of_gt cp]
      calc
        _ = c*P+c*Q-Q*(c*((1-t)/c)) := by ring
        _ = _ := by
          rw [cancellation]
          dsimp only [P,Q]
          linear_combination k*eu
    have strict : P+Q*(1-(1-t)/c)<upper E k h := by
      rw [formula]
      have scaled : c*(P+Q*(1-(1-t)/c))<
          c*(P*(E.loU+E.side)+Q*(E.loV+E.side)) := by
        nlinarith only [supportIdentity,minorIdentity,weight,uWeight,sideWeight]
      exact (mul_lt_mul_iff_right₀ cp).mp scaled
    exact lt_of_le_of_lt (comparison.1 pn) strict
  · have formula : upper E k h=P*E.loU+Q*(E.loV+E.side) := by
      rw [C981CompletionSupportForms.upper_in_bands,profile.signed]
      have a : k*E.c+h*(-t)=P := by dsimp only [P,c]; ring
      have b : -k*(-t)+h*E.c=Q := by dsimp only [Q,c]; ring
      rw [a,b,abs_of_nonpos (le_of_not_ge pn),abs_of_nonneg qp.le]
      ring
    have sideWeight := mul_pos (mul_pos qp (show 0<c+t by linarith only [cp,profile.sinePositive]))
      (sub_pos.mpr profile.sideLarge)
    have supportIdentity : c*(P*E.loU+Q*(E.loV+E.side))=
        k*E.loU+Q*((c+t)*E.side-1)+
        Q*(1-t*(E.loU+E.side)+c*E.loV) := by
      dsimp only [P,Q]
      linear_combination k*E.loU*eu
    have minorIdentity : c*(Q*(1-(1-t)/c))=Q*(c+t-1) := by
      have cancellation : c*((1-t)/c)=1-t := by field_simp [ne_of_gt cp]
      calc
        _ = c*Q-Q*(c*((1-t)/c)) := by ring
        _ = _ := by rw [cancellation]; ring
    have strict : Q*(1-(1-t)/c)<upper E k h := by
      rw [formula]
      have scaled : c*(Q*(1-(1-t)/c))<c*(P*E.loU+Q*(E.loV+E.side)) := by
        nlinarith only [supportIdentity,minorIdentity,weight,uWeight,sideWeight]
      exact (mul_lt_mul_iff_right₀ cp).mp scaled
    exact lt_of_le_of_lt (comparison.2 (le_of_not_ge pn)) strict

/-- The two universal support floors contradict the real right wall. -/
private theorem wall_of_floors (N E R : OpenSquare) (side : 1<R.side)
    (right : RightTripleData.RightProfile R)
    (nFloor : 1-(-R.s)<upper N R.c R.s)
    (eFloor : 1-(1-(-R.s))/R.c<upper E (-R.s) R.c)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  let h := R.c
  let k := -R.s
  have hp : 0<h := right.cosinePositive
  have kn : 0≤k := by dsimp only [k]; linarith only [right.sineNonpositive]
  have unit : h^2+k^2=1 := by simpa only [h,k,neg_sq] using R.unit_normal
  rw [(ownU R).1] at north
  rw [(ownV R).1] at south
  have nFace : 1-k<R.loU := lt_of_lt_of_le nFloor north
  have eFace : 1-(1-k)/h<R.loV := lt_of_lt_of_le eFloor south
  have eScaled : h+k-1<h*R.loV := by
    have weighted := mul_lt_mul_of_pos_left eFace hp
    have identity : h*(1-(1-k)/h)=h+k-1 := by
      field_simp [ne_of_gt hp]
      ring
    rwa [identity] at weighted
  have wall : h*(R.loU+R.side)+k*(R.loV+R.side)≤2 := by
    dsimp only [h,k]
    nlinarith only [right.realWall]
  exact NegativeWallElimination.universal_impossible h k R.loU R.loV R.side
    hp kn unit side nFace eScaled wall

private theorem threshold_phase (h k : ℝ) (hp : 0<h) (kn : 0≤k)
    (unit : h^2+k^2=1) (large : 9/41≤k) : 1≤k+(4/5)*h := by
  have ku : k≤1 := by nlinarith only [unit,sq_nonneg h,kn]
  have product := mul_nonneg
    (show 0≤41*k-9 by linarith only [large]) (sub_nonneg.mpr ku)
  apply le_of_not_gt
  intro bad
  have square := mul_pos (sub_pos.mpr bad)
    (show 0<1-k+(4/5)*h by linarith only [hp,ku])
  nlinarith only [product,square,unit]

private theorem threshold_floors (h k : ℝ) (hp : 0<h) (kn : 0≤k)
    (unit : h^2+k^2=1) (large : 9/41≤k) :
    1-(1-k)/h≤1+(4/5)*k-h ∧ 1-(1-k)/h≤k-h/50 := by
  let r := (1-k)/h
  have rh : h*r=1-k := by dsimp only [r]; field_simp [ne_of_gt hp]
  have ku : k≤1 := by nlinarith only [unit,sq_nonneg h,kn]
  have hu : h≤40/41 := by
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤k+9/41 by linarith only [kn])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<h+40/41 by linarith only [hp])
    nlinarith only [unit,square,other]
  have phase := threshold_phase h k hp kn unit large
  constructor
  · change 1-r≤1+(4/5)*k-h
    have product := mul_nonneg kn (sub_nonneg.mpr phase)
    have identity : h*((1+(4/5)*k-h)-(1-r))=k*(k+(4/5)*h-1) := by
      linear_combination rh-unit
    nlinarith only [product,identity,hp]
  · change 1-r≤k-h/50
    have first := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤50*(k+9/41)-(1+40/41) by linarith only [large])
    have last := mul_nonneg (show 0≤1+k by linarith only [kn])
      (sub_nonneg.mpr hu)
    have base : 0≤50*k^2-(1+k)*(1+h) := by nlinarith only [first,last]
    have product := mul_nonneg (sq_nonneg h) base
    have identity : (1+k)*(1+h)*(50*(1-h)*(1-k)-h^2)=
        h^2*(50*k^2-(1+k)*(1+h)) := by
      linear_combination -50*unit
    have denominator : 0<(1+k)*(1+h) := by positivity
    have margin : 0≤50*(1-h)*(1-k)-h^2 := by
      nlinarith only [product,identity,denominator]
    have finalIdentity : h*(k-h/50-(1-r))=(1-h)*(1-k)-h^2/50 := by
      linear_combination rh
    nlinarith only [margin,finalIdentity,hp]

/-- The shallow southeast first-bar boundary is supported by the fixed
rational normal `(9/41,40/41)`. The ideal vertex is used only after its
actual right-normal coefficients have been shown nonnegative. -/
private theorem first_fixed_vertex (c t : ℝ) (cp : 0<c) (tp : 0<t)
    (order : t≤c) (unit : c^2+t^2=1) (small : t≤9/41) :
    let H := 1+(4/5)*t-c
    let X := c+t*H
    let Y := -t+c*H
    1≤X ∧ 1/5≤(9/41)*X+(40/41)*Y := by
  let H := 1+(4/5)*t-c
  let X := c+t*H
  let Y := -t+c*H
  let Q := (40*c+9*t)/41
  let b := (40*t-9*c)/41
  have data := CommonCases.CanonicalScalars.bounds c t cp tp.le order unit
  have cLarge : 40/41≤c := by
    have square := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤9/41+t by linarith only [tp])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<40/41+c by linarith only [cp])
    nlinarith only [unit,square,other]
  have bn : b≤0 := by dsimp only [b]; linarith only [small,cLarge]
  have qp : 1/4≤Q := by dsimp only [Q]; linarith only [cLarge,tp]
  have rotated : Q^2+b^2=1 := by
    dsimp only [Q,b]
    linear_combination unit
  have qu : Q≤1 := by nlinarith only [rotated,sq_nonneg b,qp]
  have coefficient : 0≤(4/5)*Q-1/5-b := by linarith only [qp,bn]
  have product := mul_nonneg (sub_nonneg.mpr qu) coefficient
  have identity : (9/41)*X+(40/41)*Y-1/5=
      (1-Q)*((4/5)*Q-1/5-b) := by
    dsimp only [X,Y,H,Q,b]
    ring
  have xProduct := mul_nonneg (sub_nonneg.mpr data.2.1)
    (show 0≤(4/5)*c+t-1/5 by linarith only [data.1,tp])
  have xIdentity : X-1=(1-c)*((4/5)*c+t-1/5) := by
    dsimp only [X,H]
    linear_combination (4/5)*unit
  change 1 ≤ X ∧ 1/5 ≤ (9/41)*X+(40/41)*Y
  exact ⟨by nlinarith only [xProduct,xIdentity],by nlinarith only [identity,product]⟩

/-- Above the rational angle threshold, the first bottom bar has the same
universal support floor as the second bar. Both signs of the relative
parallel coefficient are retained. -/
theorem southeast_first_steep (E : OpenSquare) (t h k : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (bar : (4/5)*t-E.c≤E.loV) (hp : 0<h) (kn : 0≤k)
    (large : 9/41≤k) (unit : h^2+k^2=1) :
    1-(1-k)/h<upper E k h := by
  let c := E.c
  let P := k*c-h*t
  let Q := k*t+h*c
  let H := 1+(4/5)*t-c
  have cp : 0<c := profile.cosinePositive
  have eu : c^2+t^2=1 := by simpa only [c,profile.signed,neg_sq] using E.unit_normal
  have qp : 0<Q := by
    have tp := profile.sinePositive
    dsimp only [Q]
    positivity
  have minor := southeast_first_minorant E t h k profile bar hp kn
  have floors := threshold_floors h k hp kn unit large
  by_cases pn : 0≤P
  · have support : P+Q*H<upper E k h := minor.1 pn
    by_cases small : t≤9/41
    · let X := c+t*H
      let Y := -t+c*H
      have vertex := first_fixed_vertex c t cp profile.sinePositive profile.ordered eu small
      have xLower : 1≤X := vertex.1
      have fixed : 1/5≤(9/41)*X+(40/41)*Y := vertex.2
      have hu : h≤40/41 := by
        have square := mul_nonneg (sub_nonneg.mpr large)
          (show 0≤k+9/41 by linarith only [kn])
        apply le_of_not_gt
        intro bad
        have other := mul_pos (sub_pos.mpr bad)
          (show 0<h+40/41 by linarith only [hp])
        nlinarith only [unit,square,other]
      have coefficient : 0≤k-(9/40)*h := by linarith only [large,hu]
      have first := mul_nonneg coefficient (sub_nonneg.mpr xLower)
      have last := mul_nonneg hp.le (sub_nonneg.mpr fixed)
      have identity : P+Q*H=k*X+h*Y := by dsimp only [P,Q,X,Y]; ring
      have lower : k-h/50≤P+Q*H := by nlinarith only [first,last,identity]
      exact lt_of_le_of_lt floors.2 (lt_of_le_of_lt lower support)
    · have phase := threshold_phase c t cp profile.sinePositive.le eu (le_of_not_ge small)
      have product := mul_nonneg profile.sinePositive.le (sub_nonneg.mpr phase)
      have cancellation : c*((1-t)/c)=1-t := by field_simp [ne_of_gt cp]
      have identity : c*(H-(1-(1-t)/c))=t*(t+(4/5)*c-1) := by
        dsimp only [H]
        linear_combination -eu+cancellation
      have compare : 1-(1-t)/c≤H := by nlinarith only [identity,product,cp]
      have weight := mul_nonneg qp.le (sub_nonneg.mpr compare)
      have second := (second_scalar c t h k cp profile.sinePositive profile.ordered hp kn eu unit).1 pn
      have lower : 1-(1-k)/h≤P+Q*H := by nlinarith only [second,weight]
      exact lt_of_le_of_lt lower support
  · have support := minor.2 (le_of_not_ge pn)
    have lower := first_steeper c t h k cp profile.sinePositive hp kn eu unit
      (by dsimp only [P] at pn; linarith only [pn])
    exact lt_of_le_of_lt floors.1 (lt_of_le_of_lt lower support)

theorem second_bar_impossible (E N R : OpenSquare)
    (input : RightTripleData.Input E N R)
    (bar : -1≤ -(-E.s)*(E.loU+E.side)+E.c*E.loV)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have sideR : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
  have axis := NegativeTripleNorthSeparation.right_axis_bounds N R input.rightFaces
    input.northeastSharp input.northeastTop north
  have nonnegative : 0≤ -R.s := by linarith only [input.rightFaces.sineNonpositive]
  have unit : R.c^2+(-R.s)^2=1 := by simpa only [neg_sq] using R.unit_normal
  have nFloor := north_floor N sideN input.northeastFaces R.c (-R.s)
    input.rightFaces.cosinePositive nonnegative axis.2.2 unit
  have eFloor := southeast_second_floor E (-E.s) R.c (-R.s)
    input.southeastFaces bar input.rightFaces.cosinePositive nonnegative unit
  apply wall_of_floors N E R sideR input.rightFaces _ eFloor north south
  simpa only [neg_neg] using nFloor

/-- Both right-owned separating faces are impossible for the genuine
three-square entrance. No E/N separation assumption is needed in this branch. -/
theorem impossible (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  rcases input.southeastFaces.bar with first | second
  · by_cases shallow : -R.s≤9/41
    · exact first_bar_shallow_impossible E N R input first shallow north south
    · have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
      have sideR : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
      have axis := NegativeTripleNorthSeparation.right_axis_bounds N R input.rightFaces
        input.northeastSharp input.northeastTop north
      have nonnegative : 0≤ -R.s := by linarith only [input.rightFaces.sineNonpositive]
      have unit : R.c^2+(-R.s)^2=1 := by simpa only [neg_sq] using R.unit_normal
      have nFloor := north_floor N sideN input.northeastFaces R.c (-R.s)
        input.rightFaces.cosinePositive nonnegative axis.2.2 unit
      have eFloor := southeast_first_steep E (-E.s) R.c (-R.s)
        input.southeastFaces first input.rightFaces.cosinePositive nonnegative
        (le_of_not_ge shallow) unit
      apply wall_of_floors N E R sideR input.rightFaces _ eFloor north south
      simpa only [neg_neg] using nFloor
  · exact second_bar_impossible E N R input second north south

#print axioms north_floor
#print axioms north_shallow_floor
#print axioms southeast_first_shallow
#print axioms first_bar_shallow_impossible
#print axioms southeast_second_floor
#print axioms second_bar_impossible
#print axioms southeast_first_steep
#print axioms impossible
end N12Compact.Completion.OtherCases.C983.NegativeRightOwned
