import Compact.Completion.OtherCases.C983.NegativeCentralOrder

/-! The branch in which the southeast and northeast separating faces
belong to those two squares. A unit-circle chord bound reduces the right
square's continuously varying angle to four endpoints. No angle grid or
additional incidence assumption is used. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeForeignFaces
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

private theorem arc_lower (x y z w a b p q m : ℝ)
    (first : x^2+y^2=1) (last : z^2+w^2=1) (unit : a^2+b^2=1)
    (det : 0<x*w-y*z) (left : 0≤a*w-b*z) (right : 0≤x*b-y*a)
    (mn : 0≤m) (start : m≤p*x+q*y) (finish : m≤p*z+q*w) :
    m≤p*a+q*b := by
  let A := a*w-b*z
  let B := x*b-y*a
  let D := x*w-y*z
  have an : 0≤A := left
  have bn : 0≤B := right
  have dp : 0<D := det
  have dot : x*z+y*w≤1 := by
    nlinarith only [first,last,sq_nonneg (x-z),sq_nonneg (y-w)]
  have norm : D^2=(A+B)^2-2*A*B*(1-(x*z+y*w)) := by
    dsimp only [A,B,D]
    linear_combination (a*w-b*z)^2*first+(x*b-y*a)^2*last-
      (x*w-y*z)^2*unit
  have product := mul_nonneg (mul_nonneg an bn) (sub_nonneg.mpr dot)
  have span : D≤A+B := by nlinarith only [norm,product,dp,an,bn]
  have firstWeight := mul_nonneg an (sub_nonneg.mpr start)
  have lastWeight := mul_nonneg bn (sub_nonneg.mpr finish)
  have extra := mul_nonneg mn (sub_nonneg.mpr span)
  have identity : D*(p*a+q*b)=A*(p*x+q*y)+B*(p*z+q*w) := by
    dsimp only [A,B,D]
    ring
  have scaled : D*m≤D*(p*a+q*b) := by
    nlinarith only [firstWeight,lastWeight,extra,identity]
  exact (mul_le_mul_left dp).mp scaled

private theorem ordered (c t d r : ℝ) (cp : 0<c) (tp : 0<t)
    (dp : 0<d) (rp : 0<r) (eu : c^2+t^2=1) (nu : d^2+r^2=1)
    (sines : t<r) : d<c ∧ 0<c*r-d*t ∧ c*d+t*r≤1 := by
  have square := mul_pos (sub_pos.mpr sines)
    (show 0<r+t by linarith only [tp,rp])
  have cosines : d<c := by nlinarith only [eu,nu,square,cp,dp]
  have identity : (c*r-d*t)*(c*r+d*t)=r^2-t^2 := by
    linear_combination r^2*eu-t^2*nu
  have factor : 0<c*r+d*t := by positivity
  have cross : 0<c*r-d*t := by nlinarith only [identity,square,factor]
  have dot : c*d+t*r≤1 := by
    nlinarith only [eu,nu,sq_nonneg (c-d),sq_nonneg (t-r)]
  exact ⟨cosines,cross,dot⟩

private theorem angle_floor (c t d r a b : ℝ)
    (cp : 0<c) (tp : 0<t) (dp : 0<d) (rp : 0<r) (ap : 0<a) (bn : 0≤b)
    (eu : c^2+t^2=1) (nu : d^2+r^2=1) (ru : a^2+b^2=1)
    (order : 0<c*r-d*t) (gap : r≤c) :
    min ((c*d+t*r)+c*r) (c*(c*d+t*r)+r)≤
      (c*d+t*r)*(a+b)-r*min (a*t-b*c) 0-c*min (b*d-a*r) 0 := by
  let J := c*d+t*r
  let m := min (J+c*r) (c*J+r)
  have jp : 0<J := by dsimp only [J]; positivity
  have ju : J≤1 := by
    dsimp only [J]
    nlinarith only [eu,nu,sq_nonneg (c-d),sq_nonneg (t-r)]
  have mn : 0≤m := by dsimp only [m]; positivity
  have start : m≤J+c*r := min_le_left _ _
  have middle : m≤c*J+r := min_le_right _ _
  have other : m≤c+r*J := by
    have product := mul_nonneg (sub_nonneg.mpr gap) (sub_nonneg.mpr ju)
    nlinarith only [middle,product]
  change m≤J*(a+b)-r*min (a*t-b*c) 0-c*min (b*d-a*r) 0
  by_cases early : 0≤a*t-b*c
  · have relation : c*(a*r-b*d)=a*(c*r-d*t)+d*(a*t-b*c) := by ring
    have first := mul_pos ap order
    have last := mul_nonneg dp.le early
    have north : b*d-a*r≤0 := by nlinarith only [relation,first,last,cp]
    rw [min_eq_right early,min_eq_left north]
    have finish : m≤(J+c*r)*c+(r*t)*t := by
      have eq : (J+c*r)*c+(r*t)*t=c*J+r := by
        linear_combination r*eu
      rwa [eq]
    have floor := arc_lower 1 0 c t a b (J+c*r) (r*t) m
      (by norm_num) eu ru (by simpa using tp) early (by simpa using bn) mn
      (by simpa using start) finish
    dsimp only [J] at floor ⊢
    nlinarith only [floor]
  · have south : a*t-b*c≤0 := le_of_lt (lt_of_not_ge early)
    by_cases late : 0≤b*d-a*r
    · rw [min_eq_left south,min_eq_right late]
      have begin : m≤(c*d)*d+(J+c*r)*r := by
        have eq : (c*d)*d+(J+c*r)*r=c+r*J := by
          linear_combination c*nu
        rwa [eq]
      have floor := arc_lower d r 0 1 a b (c*d) (J+c*r) m nu (by norm_num) ru
        (by simpa using dp) (by simpa using ap.le) (by nlinarith only [late]) mn begin
        (by simpa using start)
      dsimp only [J] at floor ⊢
      nlinarith only [floor]
    · have north : b*d-a*r≤0 := le_of_lt (lt_of_not_ge late)
      rw [min_eq_left south,min_eq_left north]
      have begin : m≤(c*(d+r))*c+(r*(c+t))*t := by
        have eq : (c*(d+r))*c+(r*(c+t))*t=c*J+r := by
          dsimp only [J]
          linear_combination r*eu
        rwa [eq]
      have finish : m≤(c*(d+r))*d+(r*(c+t))*r := by
        have eq : (c*(d+r))*d+(r*(c+t))*r=c+r*J := by
          dsimp only [J]
          linear_combination c*nu
        rwa [eq]
      have floor := arc_lower c t d r a b (c*(d+r)) (r*(c+t)) m eu nu ru
        order (by linarith only [north]) (by linarith only [south]) mn begin finish
      dsimp only [J] at floor ⊢
      nlinarith only [floor]

private theorem second_margins (c t d r H : ℝ)
    (cp : 3/4<c) (tp : 0<t) (dp : 0<d) (rp : 0<r)
    (eu : c^2+t^2=1) (nu : d^2+r^2=1) (order : t<r)
    (height : c+t-1<c*H) :
    0<r*H+c-r*c+(c*d+t*r+c*r)-2*(c*d+t*r) ∧
    0<r*H+c-r*c+(c*(c*d+t*r)+r)-2*(c*d+t*r) := by
  have cpos : 0<c := by linarith only [cp]
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg t,cpos]
  have tu : t<1 := by nlinarith only [eu,sq_pos_of_pos cpos,tp]
  have du : d<1 := by nlinarith only [nu,sq_pos_of_pos rp,dp]
  have data := ordered c t d r cpos tp dp rp eu nu order
  let K := c*r-d*t
  let J := c*d+t*r
  have kp : 0<K := data.2.1
  have jp : 0<J := by dsimp only [J]; positivity
  have ju : J≤1 := data.2.2
  have halfIdentity : K^2-(r-t)^2=2*t*r*(1-J) := by
    dsimp only [K,J]
    linear_combination r^2*eu+t^2*nu
  have halfProduct := mul_nonneg (mul_nonneg tp.le rp.le) (sub_nonneg.mpr ju)
  have half : r*(1-c)≤t*(1-d) := by
    have size : r-t≤K := by
      nlinarith only [halfIdentity,halfProduct,kp,order]
    dsimp only [K] at size
    linarith only [size]
  have first := mul_nonneg (show 0≤1-t by linarith only [tu])
    (sub_nonneg.mpr half)
  have margin := mul_pos (show 0<1-t by linarith only [tu])
    (show 0<1-d by linarith only [du])
  have identity : c^2*(1-d)-t*(1-t)*(1-d)=(1-t)*(1-d) := by
    linear_combination (1-d)*eu
  have firstMargin : 0<c^2*(1-d)-r*(1-t)*(1-c) := by
    nlinarith only [first,margin,identity]
  let Q := (1-t)*(1-c)^2
  have qn : 0≤Q := by dsimp only [Q]; positivity
  have sum : 1<c+t := by
    have product := mul_pos cpos tp
    nlinarith only [eu,product,cpos,tp]
  have cSmall : 0≤1-c := sub_nonneg.mpr cu
  have oneSmall : 1-c≤t := by linarith only [sum]
  have firstQ := mul_nonneg cSmall (sub_nonneg.mpr oneSmall)
  have secondQ := mul_nonneg tp.le (show 0≤1/4-(1-c) by linarith only [cp])
  have finalQ := mul_nonneg tp.le (sq_nonneg (1-c))
  have qBound : Q≤t/4 := by dsimp only [Q]; nlinarith only [firstQ,secondQ,finalQ]
  have cSquare := mul_pos (sub_pos.mpr cp)
    (show 0<c+3/4 by linarith only [cpos])
  have coefficient : 1/2≤(2-c)*c^2 := by
    have extra := mul_nonneg (sub_nonneg.mpr cu) (sq_nonneg c)
    nlinarith only [cSquare,extra]
  have leftProduct := mul_nonneg (sub_nonneg.mpr coefficient)
    (show 0≤r+t by linarith only [rp,tp])
  have qProduct := mul_nonneg (sub_nonneg.mpr qBound)
    (show 0≤c+d by linarith only [cpos,dp])
  have rightProduct := mul_nonneg tp.le (show 0≤2-(c+d) by linarith only [cu,du])
  have scalar : 0≤(2-c)*c^2*(r+t)-Q*(c+d) := by
    nlinarith only [leftProduct,qProduct,rightProduct,order,tp]
  have shifted : (c+d)*(c^2-(2-c)*c^2*d-r*Q-Q)=
      (r-t)*((2-c)*c^2*(r+t)-Q*(c+d)) := by
    dsimp only [Q]
    linear_combination ((2-c)*c^2+(1-c)^2*(c+d))*eu-
      ((2-c)*c^2)*nu
  have shiftedProduct := mul_nonneg (sub_nonneg.mpr order.le) scalar
  have secondMargin : 0≤c^2-(2-c)*c^2*d-r*Q := by
    nlinarith only [shifted,shiftedProduct,qn,cpos,dp]
  have heightWeight := mul_pos rp (sub_pos.mpr height)
  constructor
  · apply (mul_lt_mul_left cpos).mp
    nlinarith only [heightWeight,firstMargin]
  · apply (mul_lt_mul_left cpos).mp
    dsimp only [Q] at secondMargin
    nlinarith only [heightWeight,secondMargin]

private theorem first_shallow_margins (c t d r H : ℝ)
    (cp : 0<c) (tp : 0<t) (dp : 0<d) (rp : 29/100<r) (ru : r<3/4)
    (eu : c^2+t^2=1) (nu : d^2+r^2=1) (shallow : t≤9/41)
    (height : 1+(4/5)*t-c<H) :
    0<r*H+c-r*c+(c*d+t*r+c*r)-2*(c*d+t*r) ∧
    0<r*H+c-r*c+(c*(c*d+t*r)+r)-2*(c*d+t*r) := by
  have rpos : 0<r := by linarith only [rp]
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg t,cp]
  have tu : t<1 := by linarith only [shallow]
  have tSquare := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0≤9/41+t by linarith only [tp])
  have cl : 40/41≤c := by nlinarith only [eu,tSquare,cp]
  have rSquare := mul_pos (sub_pos.mpr rp)
    (show 0<r+29/100 by linarith only [rpos])
  have du : d<24/25 := by nlinarith only [nu,rSquare,dp]
  have gap : 0<1-d := by linarith only [du]
  have ratioProduct := mul_pos gap (show 0<7*r-(1+d) by linarith only [rp,du])
  have ratio : r≤7*(1-d) := by nlinarith only [ratioProduct,nu,rpos]
  have heightWeight := mul_pos rpos (sub_pos.mpr height)
  have first := mul_nonneg (sub_nonneg.mpr cl) gap.le
  have last := mul_nonneg rpos.le (sub_nonneg.mpr cu)
  have rtFirst := mul_nonneg rpos.le (sub_nonneg.mpr shallow)
  have rtLast : r*(9/41)≤(3/4)*(9/41) := by linarith only [ru]
  have firstMargin : 0<c*(1-d)+r*(1-c-t/5) := by
    nlinarith only [first,last,rtFirst,rtLast,du]
  let A := c*(2-c)
  have cGap : 0≤1-c := sub_nonneg.mpr cu
  have square := mul_nonneg (show 0≤1/41-(1-c) by linarith only [cl])
    (show 0≤1/41+(1-c) by linarith only [cu])
  have coefficient : 2/3≤A-(7/5)*t := by
    dsimp only [A]
    nlinarith only [square,shallow]
  have cProduct := mul_nonneg cGap (sub_nonneg.mpr cu)
  have cFloor : c*(1-c)≤1/41 := by nlinarith only [cProduct,cl]
  have heightExtra := mul_nonneg (mul_nonneg rpos.le cGap)
    (show 0≤2-t by linarith only [tu])
  have ratioWeight := mul_nonneg tp.le (sub_nonneg.mpr ratio)
  have coefficientWeight := mul_nonneg (sub_nonneg.mpr coefficient) gap.le
  have secondMargin : 0< -c*(1-c)+A*(1-d)+r*(1-c)*(2-t)-r*t/5 := by
    nlinarith only [cFloor,heightExtra,ratioWeight,coefficientWeight,du]
  constructor
  · nlinarith only [heightWeight,firstMargin]
  · dsimp only [A] at secondMargin
    nlinarith only [heightWeight,secondMargin]

private theorem endpoint_margins (E N : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) (n : TopOnlyQuadrantProfile.Data N)
    (side : 1<N.side) (order : t< -N.s) :
    0<(-N.s)*(E.loV+E.side)+E.c-(-N.s)*E.c+
      (E.c*N.c+t*(-N.s)+E.c*(-N.s))-2*(E.c*N.c+t*(-N.s)) ∧
    0<(-N.s)*(E.loV+E.side)+E.c-(-N.s)*E.c+
      (E.c*(E.c*N.c+t*(-N.s))+(-N.s))-2*(E.c*N.c+t*(-N.s)) := by
  have eu : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have nu : N.c^2+(-N.s)^2=1 := by simpa only [neg_sq] using N.unit_normal
  have cp := NegativeCentralOrder.cosine_gt_six_sevenths E t e
  have rp := NegativeCentralOrder.north_sine_gt N side n
  have data := TopOnlyQuadrantScalars.profile_bounds N side n
  rcases e.bar with face | vertex
  · have height : 1+(4/5)*t-E.c<E.loV+E.side := by
      linarith only [face,e.sideLarge]
    by_cases shallow : t≤9/41
    · exact first_shallow_margins E.c t N.c (-N.s) (E.loV+E.side)
        e.cosinePositive e.sinePositive n.cosine_pos rp data.2.2.2.1 eu nu shallow height
    · have small : t<1 := by
        nlinarith only [eu,sq_pos_of_pos e.cosinePositive,e.sinePositive]
      have phase : 1≤t+(4/5)*E.c := by
        apply le_of_not_gt
        intro failure
        have positive := mul_pos (sub_pos.mpr failure)
          (show 0<1-t+(4/5)*E.c by linarith only [small,e.cosinePositive])
        have interval := mul_nonneg
          (show 0≤41*t-9 by linarith only [shallow])
          (show 0≤1-t by linarith only [small])
        nlinarith only [positive,interval,eu]
      have extra := mul_nonneg e.sinePositive.le (sub_nonneg.mpr phase)
      have strict := mul_pos e.cosinePositive (sub_pos.mpr height)
      have scaled : E.c+t-1<E.c*(E.loV+E.side) := by
        nlinarith only [extra,strict,eu]
      exact second_margins E.c t N.c (-N.s) (E.loV+E.side)
        (by linarith only [cp]) e.sinePositive n.cosine_pos
        (by linarith only [rp]) eu nu order scaled
  · have sideWeight := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    have upperWeight := mul_pos e.sinePositive (sub_pos.mpr e.upperU)
    have height : E.c+t-1<E.c*(E.loV+E.side) := by
      nlinarith only [vertex,sideWeight,upperWeight]
    exact second_margins E.c t N.c (-N.s) (E.loV+E.side)
      (by linarith only [cp]) e.sinePositive n.cosine_pos
      (by linarith only [rp]) eu nu order height

private theorem lower_min (q : OpenSquare) (nx ny : ℝ) :
    lower q nx ny=(nx*q.c+ny*q.s)*q.loU+(-nx*q.s+ny*q.c)*q.loV+
      q.side*(min (nx*q.c+ny*q.s) 0+min (-nx*q.s+ny*q.c) 0) := by
  rw [C981CompletionSupportForms.lower_in_bands]
  by_cases first : 0≤nx*q.c+ny*q.s
  · rw [abs_of_nonneg first,min_eq_right first]
    by_cases last : 0≤ -nx*q.s+ny*q.c
    · rw [abs_of_nonneg last,min_eq_right last]; ring
    · rw [abs_of_nonpos (le_of_not_ge last),min_eq_left (le_of_not_ge last)]; ring
  · rw [abs_of_nonpos (le_of_not_ge first),min_eq_left (le_of_not_ge first)]
    by_cases last : 0≤ -nx*q.s+ny*q.c
    · rw [abs_of_nonneg last,min_eq_right last]; ring
    · rw [abs_of_nonpos (le_of_not_ge last),min_eq_left (le_of_not_ge last)]; ring

/-- The two foreign separating faces cannot coexist with the actual
right wall. Central disjointness is used only to establish their angle order. -/
theorem impossible (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (apartEN : ∀ x y,¬(E.Inside x y ∧ N.Inside x y))
    (north : upper N N.c N.s≤lower R N.c N.s)
    (south : upper E (-E.s) E.c≤lower R (-E.s) E.c) : False := by
  let c := E.c
  let t := -E.s
  let d := N.c
  let r := -N.s
  let a := R.c
  let b := -R.s
  let H := E.loV+E.side
  let J := c*d+t*r
  let F := J*(a+b)-r*min (a*t-b*c) 0-c*min (b*d-a*r) 0
  let m := min (J+c*r) (c*J+r)
  have cp : 0<c := input.southeastFaces.cosinePositive
  have tp : 0<t := input.southeastFaces.sinePositive
  have dp : 0<d := input.northeastFaces.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [input.northeastFaces.sine_neg]
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have eu : c^2+t^2=1 := by simpa only [c,t,neg_sq] using E.unit_normal
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have ru : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have sideR : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
  have sines : t<r := NegativeCentralOrder.sine_lt E N t input.sameEN
    input.southeastFaces input.northeastFaces input.southeastElbow
    input.northeastSharp input.northeastLeft apartEN
  have orientations := ordered c t d r cp tp dp rp eu nu sines
  have cLarge : 6/7<c :=
    NegativeCentralOrder.cosine_gt_six_sevenths E t input.southeastFaces
  have northData := TopOnlyQuadrantScalars.profile_bounds N sideN input.northeastFaces
  have gap : r≤c := by linarith only [cLarge,northData.2.2.2.1]
  have floor : m≤F := angle_floor c t d r a b cp tp dp rp ap bn eu nu ru
    orientations.2.1 gap
  have jp : 0<J := by dsimp only [J]; positivity
  have mn : 0≤m := by dsimp only [m]; positivity
  have fn : 0≤F := le_trans mn floor
  have length := mul_nonneg fn (sub_nonneg.mpr sideR.le)
  have lowerLength : m≤R.side*F := by nlinarith only [length,floor]
  have qPositive : 0<b*t+a*c := by positivity
  have aPositive : 0<d*a+r*b := by positivity
  have eFormula : lower R t c=(a*t-b*c)*R.loU+(b*t+a*c)*R.loV+
      R.side*min (a*t-b*c) 0 := by
    rw [lower_min]
    have first : t*R.c+c*R.s=a*t-b*c := by dsimp only [a,b]; ring
    have last : -t*R.s+c*R.c=b*t+a*c := by dsimp only [a,b]; ring
    rw [first,last,min_eq_right qPositive.le]
    ring
  have nFormula : lower R d (-r)=(d*a+r*b)*R.loU+(b*d-a*r)*R.loV+
      R.side*min (b*d-a*r) 0 := by
    rw [lower_min]
    have first : d*R.c+(-r)*R.s=d*a+r*b := by dsimp only [a,b]; ring
    have last : -d*R.s+(-r)*R.c=b*d-a*r := by dsimp only [a,b]; ring
    rw [first,last,min_eq_right aPositive.le]
    ring
  rw [(ownV E).2] at south
  have eFace : H≤(a*t-b*c)*R.loU+(b*t+a*c)*R.loV+
      R.side*min (a*t-b*c) 0 := by
    have normalized : H≤lower R t c := south
    rwa [eFormula] at normalized
  rw [(ownU N).2] at north
  have nFace : N.loU+N.side≤(d*a+r*b)*R.loU+(b*d-a*r)*R.loV+
      R.side*min (b*d-a*r) 0 := by
    have normalized : N.loU+N.side≤lower R d (-r) := by
      simpa only [d,r,neg_neg] using north
    rwa [nFormula] at normalized
  have wall : a*(R.loU+R.side)+b*(R.loV+R.side)≤2 := by
    dsimp only [a,b]
    nlinarith only [input.rightFaces.realWall]
  have eWeight := mul_nonneg rp.le (sub_nonneg.mpr eFace)
  have nWeight := mul_nonneg cp.le (sub_nonneg.mpr nFace)
  have wallWeight := mul_nonneg jp.le (sub_nonneg.mpr wall)
  have identity : J*(a*(R.loU+R.side)+b*(R.loV+R.side))-
      r*((a*t-b*c)*R.loU+(b*t+a*c)*R.loV+R.side*min (a*t-b*c) 0)-
      c*((d*a+r*b)*R.loU+(b*d-a*r)*R.loV+R.side*min (b*d-a*r) 0)=
      R.side*F := by
    dsimp only [J,F]
    ring
  have bound : r*H+c*(N.loU+N.side)+m≤2*J := by
    nlinarith only [eWeight,nWeight,wallWeight,identity,lowerLength]
  have northWidth : 1-r<N.loU+N.side := by
    dsimp only [r]
    linarith only [input.northeastFaces.lowerU,sideN]
  have northExtra := mul_pos cp (sub_pos.mpr northWidth)
  have endpoints := endpoint_margins E N t input.southeastFaces input.northeastFaces sideN sines
  have impossible : 2*J<r*H+c*(1-r)+m := by
    dsimp only [m]
    rcases le_total (J+c*r) (c*J+r) with first | last
    · rw [min_eq_left first]
      have endpoint : 0<r*H+c-r*c+(J+c*r)-2*J := endpoints.1
      linarith only [endpoint]
    · rw [min_eq_right last]
      have endpoint : 0<r*H+c-r*c+(c*J+r)-2*J := endpoints.2
      linarith only [endpoint]
  nlinarith only [bound,northExtra,impossible]

#print axioms impossible

end N12Compact.Completion.OtherCases.C983.NegativeForeignFaces
