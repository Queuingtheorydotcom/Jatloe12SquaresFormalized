import Compact.Completion.OtherCases.C983.NegativeMixedScalars

/-! The southeast-owned transverse / right-owned parallel separation.
The proof keeps both genuine bottom alternatives. A shallow right frame
uses one square identity; the remaining ordered interval uses one exact
polynomial identity. No additional point or orientation is assumed. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeMixedSouth
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

private theorem height_floor (E : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) : (4/5)*t<E.loV+E.side := by
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t e.cosinePositive
    e.sinePositive.le e.ordered unit
  rcases e.bar with first | second
  · linarith only [first,e.sideLarge,bounds.2.1]
  · have first := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    have last := mul_pos e.sinePositive (sub_pos.mpr e.upperU)
    have sum := bounds.2.2.2.2
    have scaled : E.c*((E.loV+E.side)-(4/5)*t)>0 := by
      nlinarith only [second,first,last,sum]
    have gap := (mul_pos_iff_of_pos_left e.cosinePositive).mp scaled
    linarith only [gap]

private theorem second_floor (E : OpenSquare) (t : ℝ)
    (e : NegativeTripleFaces.Data E t) (large : 9/41≤t) :
    1-(1-t)/E.c<E.loV+E.side := by
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t e.cosinePositive
    e.sinePositive.le e.ordered unit
  have cancel : E.c*((1-t)/E.c)=1-t := by field_simp [ne_of_gt e.cosinePositive]
  rcases e.bar with first | second
  · have phase : 1≤t+(4/5)*E.c := by
      have tu : t≤1 := by linarith only [e.ordered,bounds.2.1]
      have product := mul_nonneg (show 0≤41*t-9 by linarith only [large])
        (sub_nonneg.mpr tu)
      apply le_of_not_gt
      intro bad
      have square := mul_pos (sub_pos.mpr bad)
        (show 0<1-t+(4/5)*E.c by linarith only [tu,e.cosinePositive])
      nlinarith only [unit,product,square]
    have extra := mul_nonneg e.sinePositive.le (sub_nonneg.mpr phase)
    have width := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    have face := mul_nonneg e.cosinePositive.le (sub_nonneg.mpr first)
    have scaled : 0<E.c*((E.loV+E.side)-(1-(1-t)/E.c)) := by
      nlinarith only [extra,width,face,unit,cancel]
    have gap := (mul_pos_iff_of_pos_left e.cosinePositive).mp scaled
    linarith only [gap]
  · have width := mul_pos e.cosinePositive (sub_pos.mpr e.sideLarge)
    have long := mul_pos e.sinePositive (sub_pos.mpr e.upperU)
    have scaled : 0<E.c*((E.loV+E.side)-(1-(1-t)/E.c)) := by
      nlinarith only [width,long,second,cancel]
    have gap := (mul_pos_iff_of_pos_left e.cosinePositive).mp scaled
    linarith only [gap]

/-- A positive support residual contradicts the actual right wall. The
lower-left vertex bounds the right square's lower support for either
sign of the relative transverse coefficient. -/
private theorem wall (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-E.s) E.c≤lower R (-E.s) E.c)
    (U : ℝ) (floor : U<upper N R.c R.s)
    (margin : 0≤E.c*U+(-R.s)*(E.loV+E.side)-
      (R.c*E.c+(-R.s)*(-E.s))*(2-R.c-(-R.s))) : False := by
  let c := E.c
  let t := -E.s
  let a := R.c
  let b := -R.s
  let P := a*t-b*c
  let Q := a*c+b*t
  have cp : 0<c := input.southeastFaces.cosinePositive
  have tp : 0<t := input.southeastFaces.sinePositive
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have qp : 0<Q := by dsimp only [Q]; positivity
  have side : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
  rw [(ownU R).1] at north
  have uFloor : U<R.loU := lt_of_lt_of_le floor north
  have closed := WallProfile.vertex R R.loU R.loV
    ⟨le_rfl,by linarith only [R.side_pos]⟩
    ⟨le_rfl,by linarith only [R.side_pos]⟩
  have vertex := (closed_bounds R _ _ t c closed).1
  have bound : lower R t c≤P*R.loU+Q*R.loV := by
    convert vertex using 1 <;> dsimp only [P,Q,a,b,c,t] <;> ring
  rw [(ownV E).2] at south
  have cut : E.loV+E.side≤P*R.loU+Q*R.loV := le_trans south bound
  have weight := mul_nonneg bn (sub_nonneg.mpr cut)
  have wallBound : a*(R.loU+R.side)+b*(R.loV+R.side)≤2 := by
    dsimp only [a,b]
    nlinarith only [input.rightFaces.realWall]
  have wallWeight := mul_nonneg qp.le (sub_nonneg.mpr wallBound)
  have first := mul_pos cp (sub_pos.mpr uFloor)
  have last := mul_pos (mul_pos qp (show 0<a+b by linarith only [ap,bn]))
    (sub_pos.mpr side)
  have unit : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have identity : b*P-a*Q= -c := by
    dsimp only [P,Q]
    linear_combination -c*unit
  have combined : c*R.loU+b*(E.loV+E.side)+Q*(a+b)*R.side≤2*Q := by
    have algebra : b*(P*R.loU+Q*R.loV-(E.loV+E.side))+
        Q*(2-(a*(R.loU+R.side)+b*(R.loV+R.side)))=
        2*Q-(c*R.loU+b*(E.loV+E.side)+Q*(a+b)*R.side) := by
      linear_combination R.loU*identity
    nlinarith only [weight,wallWeight,algebra]
  change 0≤c*U+b*(E.loV+E.side)-Q*(2-a-b) at margin
  nlinarith only [combined,first,last,margin]

/-- If the right normal is steeper, the E-owned separator also gives the
right-owned transverse separator. This is a comparison of actual faces. -/
private theorem steeper (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-E.s) E.c≤lower R (-E.s) E.c)
    (order : R.c*(-E.s)-(-R.s)*E.c≤0) : False := by
  let c := E.c
  let t := -E.s
  let a := R.c
  let b := -R.s
  let P := a*t-b*c
  let Q := a*c+b*t
  let H := E.loV+E.side
  let V := E.loU+E.side
  have cp : 0<c := input.southeastFaces.cosinePositive
  have tp : 0<t := input.southeastFaces.sinePositive
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have pn : P≤0 := order
  have qp : 0<Q := by dsimp only [Q]; positivity
  have eu : c^2+t^2=1 := by simpa only [c,t,neg_sq] using E.unit_normal
  have ru : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have rotated : P^2+Q^2=1 := by
    dsimp only [P,Q]
    linear_combination (a^2+b^2)*eu+ru
  have qu : Q≤1 := by nlinarith only [rotated,sq_nonneg P,qp]
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg t,cp]
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have axis := NegativeTripleNorthSeparation.right_axis_bounds N R input.rightFaces
    input.northeastSharp input.northeastTop north
  have bu : b<3/4 := axis.2.2
  have nf := NegativeRightOwned.north_floor N sideN input.northeastFaces a b ap bn bu ru
  rw [(ownU R).1] at north
  have ul : 1-b<R.loU := lt_of_lt_of_le nf north
  have dotBound : 2*c*Q≤1+a := by
    have identity : (b*c-(1+a)*t)^2=(1+a)*(1+a-2*c*Q) := by
      dsimp only [Q]
      linear_combination (1+a)^2*eu+c^2*ru
    have square := sq_nonneg (b*c-(1+a)*t)
    have denom : 0<1+a := by linarith only [ap]
    have nonnegative : 0≤1+a-2*c*Q := by
      have product : 0≤(1+a)*(1+a-2*c*Q) := by rw [←identity]; exact square
      exact nonneg_of_mul_nonneg_right product denom
    linarith only [nonnegative]
  have small : (13/50)*c*Q<R.loU := by
    by_cases low : b≤2/3
    · have product := mul_nonneg cp.le (sub_nonneg.mpr qu)
      nlinarith only [product,cu,ul,low]
    · have aSmall : a<3/4 := by
        have square := mul_pos (show 0<b-2/3 by linarith only [low])
          (show 0<b+2/3 by linarith only [bn])
        apply lt_of_not_ge
        intro bad
        have other := mul_nonneg (sub_nonneg.mpr bad)
          (show 0≤a+3/4 by linarith only [ap])
        nlinarith only [ru,square,other]
      linarith only [dotBound,ul,bu,aSmall]
  have hp : 0<H := by
    have floor := height_floor E t input.southeastFaces
    dsimp only [H]
    linarith only [floor,tp]
  have first := mul_pos qp (sub_pos.mpr input.southeastFaces.elbowLowerU)
  have width := mul_nonneg (sub_nonneg.mpr qu) E.side_pos.le
  have hWeight := mul_nonneg (neg_nonneg.mpr pn) hp.le
  have cap : Q*V+P*H<R.loU+R.side := by
    dsimp only [V,H] at hWeight ⊢
    rw [←input.sameER]
    nlinarith only [first,width,hWeight,small]
  have closed := WallProfile.vertex R (R.loU+R.side) R.loV
    ⟨by linarith only [R.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [R.side_pos]⟩
  have vertex := (closed_bounds R _ _ t c closed).1
  have bound : lower R t c≤P*(R.loU+R.side)+Q*R.loV := by
    convert vertex using 1 <;> dsimp only [P,Q,a,b,c,t] <;> ring
  rw [(ownV E).2] at south
  have cut : H≤P*(R.loU+R.side)+Q*R.loV := le_trans south bound
  have weight := mul_nonneg (neg_nonneg.mpr pn) (sub_nonneg.mpr cap.le)
  have support : upper E b a= -P*V+Q*H := by
    rw [C981CompletionSupportForms.upper_in_bands]
    have pform : b*E.c+a*E.s= -P := by dsimp only [P,a,b,c,t]; ring
    have qform : -b*E.s+a*E.c=Q := by dsimp only [Q,a,b,c,t]; ring
    rw [pform,qform,abs_of_nonneg (neg_nonneg.mpr pn),abs_of_nonneg qp.le]
    dsimp only [V,H]
    ring
  have identity : H-P*(Q*V+P*H)-Q*R.loV=
      Q*((-P*V+Q*H)-R.loV) := by
    linear_combination -H*rotated
  have scaled : Q*((-P*V+Q*H)-R.loV)≤0 := by
    nlinarith only [cut,weight,identity]
  have transverse : upper E (-R.s) R.c≤lower R (-R.s) R.c := by
    rw [(ownV R).1]
    change upper E b a≤R.loV
    rw [support]
    have comparison : Q*(-P*V+Q*H)≤Q*R.loV := by nlinarith only [scaled]
    exact (mul_le_mul_left qp).mp comparison
  apply NegativeRightOwned.impossible E N R input _ transverse
  simpa only [(ownU R).1] using north

theorem impossible (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (north : upper N R.c R.s≤lower R R.c R.s)
    (south : upper E (-E.s) E.c≤lower R (-E.s) E.c) : False := by
  let c := E.c
  let t := -E.s
  let a := R.c
  let b := -R.s
  have cp : 0<c := input.southeastFaces.cosinePositive
  have tp : 0<t := input.southeastFaces.sinePositive
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have eu : c^2+t^2=1 := by simpa only [c,t,neg_sq] using E.unit_normal
  have ru : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  by_cases shallow : b≤9/41
  · have floor := NegativeRightOwned.north_shallow_floor N sideN input.northeastFaces
      a b ap bn shallow ru
    have height := height_floor E t input.southeastFaces
    have margin := NegativeMixedShallow.scalar c t a b (E.loV+E.side) cp tp
      input.southeastFaces.ordered ap bn eu ru shallow height.le
    exact wall E N R input north south ((26/25)*a-b) floor margin
  · by_cases order : a*t-b*c≤0
    · exact steeper E N R input north south order
    · have relation : b≤t := by
        have dot := mul_pos (show 0<a*t-b*c by linarith only [order])
          (show 0<a*t+b*c by positivity)
        apply le_of_not_gt
        intro bad
        have other := mul_pos (sub_pos.mpr bad) (show 0<b+t by linarith only [bn,tp])
        have identity : (a*t-b*c)*(a*t+b*c)=t^2-b^2 := by
          linear_combination t^2*ru-b^2*eu
        nlinarith only [dot,other,identity]
      have large : 9/41≤t := le_trans (le_of_not_ge shallow) relation
      have hFloor := second_floor E t input.southeastFaces large
      have axis := NegativeTripleNorthSeparation.right_axis_bounds N R input.rightFaces
        input.northeastSharp input.northeastTop north
      have nFloor := NegativeRightOwned.north_floor N sideN input.northeastFaces
        a b ap bn axis.2.2 ru
      have cLarge := NegativeCentralOrder.cosine_gt_six_sevenths E t input.southeastFaces
      have margin := NegativeMixedScalars.large c t a b cp tp ap bn eu ru cLarge
        (le_of_not_ge shallow) (by linarith only [order])
      have weight := mul_nonneg bn (sub_nonneg.mpr hFloor.le)
      apply wall E N R input north south (1-b) nFloor
      change 0≤c*(1-b)+b*(E.loV+E.side)-(a*c+b*t)*(2-a-b)
      nlinarith only [margin,weight]

#print axioms impossible
end N12Compact.Completion.OtherCases.C983.NegativeMixedSouth
