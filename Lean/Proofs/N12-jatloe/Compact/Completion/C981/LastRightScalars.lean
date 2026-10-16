import Compact.Completion.C981.OppositeSupport
import Compact.Completion.C981.LastWallPolynomials

/-! Scalar comparisons for the actual right-wall exclusion in the final
C981 cycles. This file uses no derivatives; its two-normal minimum is an
exact divided difference in the two real half-angle parameters. -/
namespace N12Compact.C981CompletionLastRightScalars

open C977CornerCubic
set_option Elab.async false

noncomputable def half (c s : ℝ) : ℝ := s/(1+c)

theorem half_data (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) (unit : c^2+s^2=1) :
    0 ≤ half c s ∧ half c s ≤ 1 ∧ half c s*(1+c)=s ∧
      half c s*s+c=1 ∧ (1+(half c s)^2)*c=1-(half c s)^2 ∧
      (1+(half c s)^2)*s=2*half c s := by
  let z := half c s
  have denominator : 0 < 1+c := by linarith only [hc]
  have zn : 0 ≤ z := div_nonneg hs denominator.le
  have sOne : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  have zh : z ≤ 1 := (div_le_iff₀ denominator).mpr (by linarith only [sOne,hc])
  have relation : z*(1+c)=s := div_mul_cancel₀ _ denominator.ne'
  have sineRelation : z*s+c=1 := by
    apply (mul_right_cancel₀ denominator.ne')
    linear_combination s*relation+unit
  have squared := congrArg (fun x : ℝ => x^2) relation
  have cosine : (1+z^2)*c=1-z^2 := by
    have identity : (1+c)*((1+z^2)*c-(1-z^2))=
        c^2+z^2*(1+c)^2-1 := by ring
    have zero : (1+c)*((1+z^2)*c-(1-z^2))=0 := by nlinarith only [identity,squared,unit]
    have vanishes := (mul_eq_zero.mp zero).resolve_left denominator.ne'
    linarith only [vanishes]
  have sine : (1+z^2)*s=2*z := by
    linear_combination z*sineRelation-relation
  exact ⟨zn,zh,relation,sineRelation,cosine,sine⟩

structure Minor (b t : ℝ) : Prop where
  bLow : 43/50 < b
  bHigh : b < 883/1000
  tLow : 47/100 < t
  tHigh : t ≤ 1/2
  hLow : 1/4 < half b t
  hHigh : half b t ≤ 27/100
  kLow : 1/10 ≤ b+t-1-(3/5)*b*t

theorem minor {b t : ℝ} (bn : Normal b t) (span : 1 < t+(3/5)*b)
    (small : t ≤ 1/2) : Minor b t := by
  have bounds := normal_bounds bn
  have bp : 0 < b := by linarith only [bounds.1]
  have hp := C981CompletionHalfAngle.quarter_lt b t bp.le bn.1 bn.2.1 bn.2.2 span
  change 1/4 < half b t at hp
  have hd := half_data b t bp bn.1 bn.2.2
  have relation := hd.2.2.1
  have sine : 8/17 < t := by
    apply lt_of_not_ge
    intro no
    have cosine : b < 15/17 := by
      have product := mul_pos (show 0 < half b t-1/4 by linarith only [hp])
        (show 0 < 1+b by linarith only [bp])
      nlinarith only [product,relation,no]
    have first := mul_pos (show 0 < 15/17-b by linarith only [cosine])
      (show 0 < 15/17+b by linarith only [bp])
    have last := mul_nonneg (sub_nonneg.mpr no) (show 0 ≤ 8/17+t by linarith only [bn.1])
    nlinarith only [first,last,bn.2.2]
  have sineSquare := mul_pos (show 0 < t-8/17 by linarith only [sine])
    (show 0 < t+8/17 by linarith only [bn.1])
  have cosine : b < 883/1000 := by
    nlinarith only [sineSquare,bn.2.2,sq_nonneg (b-883/1000)]
  have smallSquare := mul_nonneg (sub_nonneg.mpr small)
    (show 0 ≤ 1/2+t by linarith only [bn.1])
  have bLow : 43/50 < b := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonneg (sub_nonneg.mpr no) (show 0 ≤ 43/50+b by linarith only [bp])
    nlinarith only [product,smallSquare,bn.2.2]
  have hWeight := mul_nonneg hd.1 (show 0 ≤ b-43/50 by linarith only [bLow])
  have hHigh : half b t ≤ 27/100 := by nlinarith only [hWeight,relation,small]
  have hLow : 23/17 < b+t := by
    apply lt_of_not_ge
    intro no
    have tHigh : t ≤ 23/34 := by linarith only [no,bn.2.1]
    have comparison := mul_nonneg
      (show 0 ≤ 23/17-t-b by linarith only [no])
      (show 0 ≤ 23/17-t+b by linarith only [tHigh,bp])
    have interval := mul_pos (show 0 < t-8/17 by linarith only [sine])
      (show 0 < 15/17-t by linarith only [tHigh])
    nlinarith only [comparison,interval,bn.2.2]
  have kWeight := mul_nonneg (show 0 ≤ b+t-23/17 by linarith only [hLow])
    (show 0 ≤ 1-(3/10)*(b+t+23/17) by linarith only [bounds.2.2.2.2.2])
  have kLow : 1/10 ≤ b+t-1-(3/5)*b*t := by nlinarith only [kWeight,bn.2.2]
  exact ⟨bLow,cosine,by linarith only [sine],small,hp,hHigh,kLow⟩

private theorem half_order (c s b t : ℝ) (rn : c^2+s^2=1) (hc : 0 < c) (hs : 0 ≤ s)
    (bn : Normal b t) (order : b*s-t*c ≤ 0) : half c s ≤ half b t := by
  have bp : 0 < b := by linarith only [(normal_bounds bn).1]
  have coords := C981CompletionOppositeSupport.cross_order b t c s bp bn.1 hc hs bn.2.2 rn
    (by linarith only [order])
  have rd := half_data c s hc hs rn
  have bd := half_data b t bp bn.1 bn.2.2
  have product := mul_nonneg rd.1 (sub_nonneg.mpr coords.1)
  have gap : (half c s-half b t)*(1+b) ≤ 0 := by
    nlinarith only [product,rd.2.2.1,bd.2.2.1,coords.2]
  apply le_of_not_gt
  intro no
  have positive := mul_pos (sub_pos.mpr no) (show 0 < 1+b by linarith only [bp])
  linarith only [positive,gap]

theorem bu_negative (c s b t : ℝ) (rn : c^2+s^2=1) (hc : 0 < c) (hs : 0 < s)
    (bn : Normal b t) (small : Minor b t) (order : b*s-t*c ≤ 0)
    (cut : 0 < 2*(b*c+t*s)-b*c+(7/5)*b*s-s-(b*c+t*s)*(c+s)) : False := by
  let z := half c s
  have rd := half_data c s hc hs.le rn
  have zn : 0 ≤ z := rd.1
  have zh : z ≤ 27/100 := le_trans (half_order c s b t rn hc hs.le bn order) small.hHigh
  let A := 2/5+z+(12/5)*z^2-z^3
  let B := 1-2*z+3*z^2
  have aPositive : 0 ≤ A := by
    have product := mul_nonneg (sq_nonneg z) (show 0 ≤ 12/5-z by linarith only [zh])
    dsimp [A]
    nlinarith only [product,zn]
  have bPositive : 0 ≤ B := by dsimp [B]; nlinarith only [sq_nonneg (z-1/3)]
  have first := mul_nonneg aPositive (show 0 ≤ 883/1000-b by linarith only [small.bHigh])
  have last := mul_nonneg bPositive (sub_nonneg.mpr small.tHigh)
  have middle : b*A+t*B-1-z^2 < 0 := by
    have polynomial := C981CompletionLastWallPolynomials.first z zn zh
    dsimp [A,B] at first last ⊢
    nlinarith only [first,last,polynomial]
  have identity : (1+z^2)*(2*(b*c+t*s)-b*c+(7/5)*b*s-s-(b*c+t*s)*(c+s))=
      s*(b*A+t*B-1-z^2) := by
    have hzs := rd.2.2.2.1
    have cosine := rd.2.2.2.2.1
    have sine := rd.2.2.2.2.2
    calc
      _ = s*(b*((7/5)*(1+z^2)+(z-1)*((1+z^2)*c))+
          t*(2*(1+z^2)-(1+z^2)*c-(1+z^2)*s)-(1+z^2)) := by
        linear_combination -b*c*(1+z^2)*hzs
      _ = _ := by rw [cosine,sine]; dsimp [A,B]; ring
  have positive := mul_pos (show 0 < 1+z^2 by nlinarith only [sq_nonneg z]) cut
  have negative := mul_neg_of_pos_of_neg hs middle
  rw [identity] at positive
  exact (not_lt_of_ge positive.le) negative

theorem bu_positive (c s b t : ℝ) (rn : c^2+s^2=1) (hc : 0 < c) (hs : 0 < s)
    (bn : Normal b t) (small : Minor b t) (order : 0 ≤ b*s-t*c)
    (cut : 0 < 2*(b*c+t*s)-b*c+(7/5)*b*s-s-(b*c+t*s)*(c+s)-s*(b*s-t*c)) : False := by
  let z := half c s
  have rd := half_data c s hc hs.le rn
  have bp : 0 < b := by linarith only [small.bLow]
  have coords := C981CompletionOppositeSupport.cross_order c s b t hc hs.le bp bn.1 rn bn.2.2
    (by linarith only [order])
  have bData := half_data b t bp bn.1 bn.2.2
  have zWeight := mul_nonneg bData.1 (sub_nonneg.mpr coords.1)
  have gap : (half b t-z)*(1+c) ≤ 0 := by
    nlinarith only [zWeight,bData.2.2.1,rd.2.2.1,coords.2]
  have ordered : half b t ≤ z := by
    apply le_of_not_gt
    intro no
    have positive := mul_pos (sub_pos.mpr no) (show 0 < 1+c by linarith only [hc])
    linarith only [positive,gap]
  have zLow : 1/4 ≤ z := le_trans small.hLow.le ordered
  have cOne : c ≤ 1 := by nlinarith only [rn,sq_nonneg s,sq_nonneg (c-1)]
  have sOne : s ≤ 1 := by nlinarith only [rn,sq_nonneg c,sq_nonneg (s-1)]
  let A := 7/5-s-c*(1-z)
  let D := 2-s
  have zProduct := mul_nonneg rd.1 (sub_nonneg.mpr sOne)
  have cProduct := mul_nonneg hc.le (show 0 ≤ z+c-1 by nlinarith only [zProduct,rd.2.2.2.1])
  have aLower : 3/20 ≤ A := by dsimp [A]; nlinarith only [cProduct,rn,sq_nonneg (s-1/2)]
  have aUpper : A ≤ 2/5 := by
    dsimp [A]
    nlinarith only [zProduct,rd.2.2.1,rd.2.2.2.1]
  have dLower : 1 ≤ D := by dsimp [D]; linarith only [sOne]
  have cosineBound : b ≤ 117/100-(3/5)*t := by
    apply le_of_not_gt
    intro no
    have comparison := mul_pos (show 0 < b-(117/100-(3/5)*t) by linarith only [no])
      (show 0 < b+(117/100-(3/5)*t) by linarith only [bp,small.tHigh])
    have chord := mul_nonneg (sub_nonneg.mpr small.tHigh)
      (show 0 ≤ 351/250-(34/25)*(t+1/2) by linarith only [small.tHigh])
    nlinarith only [comparison,chord,bn.2.2]
  have aNonnegative : 0 ≤ A := le_trans (by norm_num : (0:ℝ) ≤ 3/20) aLower
  have weightedUpper : (3/5)*A ≤ 6/25 := by
    calc
      _ ≤ (3/5)*(2/5) := mul_le_mul_of_nonneg_left aUpper (by norm_num)
      _ = _ := by norm_num
  have gapNonnegative : 0 ≤ D-(3/5)*A :=
    sub_nonneg.mpr (le_trans weightedUpper
      (le_trans (by norm_num : (6/25:ℝ) ≤ 1) dLower))
  have endpoint : b*A+t*D ≤ (87/100)*A+D/2 := by
    calc
      _ ≤ (117/100-(3/5)*t)*A+t*D :=
        by linarith only [mul_le_mul_of_nonneg_right cosineBound aNonnegative]
      _ = (117/100)*A+t*(D-(3/5)*A) := by ring
      _ ≤ (117/100)*A+(1/2)*(D-(3/5)*A) :=
        by linarith only [mul_le_mul_of_nonneg_right small.tHigh gapNonnegative]
      _ = _ := by ring
  have polynomial := C981CompletionLastWallPolynomials.second z zLow
  have negative : (1+z^2)*(b*A+t*D-1) < 0 := by
    have identity : (1+z^2)*((87/100)*A+D/2-1)=
        87/250-(187/100)*z+(261/125)*z^2-(87/100)*z^3 := by
      dsimp [A,D]
      calc
        _ = (87/100)*((7/5)*(1+z^2)-(1+z^2)*s-(1-z)*((1+z^2)*c))+
            ((2*(1+z^2)-(1+z^2)*s)/2)-(1+z^2) := by ring
        _ = _ := by rw [rd.2.2.2.2.1,rd.2.2.2.2.2]; ring
    calc
      _ ≤ (1+z^2)*((87/100)*A+D/2-1) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right endpoint 1)
          (add_nonneg (by norm_num) (sq_nonneg z))
      _ = _ := identity
      _ < 0 := polynomial
  have identity : 2*(b*c+t*s)-b*c+(7/5)*b*s-s-(b*c+t*s)*(c+s)-s*(b*s-t*c)=s*(b*A+t*D-1) := by
    dsimp [A,D]
    linear_combination -b*c*rd.2.2.2.1
  have product : 0 < (1+z^2)*(b*A+t*D-1) := by
    have inner := pos_of_mul_pos_right (by rwa [identity] at cut) hs.le
    exact mul_pos (by nlinarith only [sq_nonneg z]) inner
  linarith only [product,negative]

theorem ru_negative (c s b t : ℝ) (rn : c^2+s^2=1) (hc : 0 < c) (hs : 0 < s)
    (bn : Normal b t) (small : Minor b t) (order : b*s-t*c ≤ 0) :
    0 < s*((b*c+t*s)*(1-b)+(b*s-t*c)*(b+t-1))+
      c^2-(2/5)*c*s+c+s-2 := by
  let z := half c s
  let h := half b t
  let A := b+t-7/5-b*t
  let B := t-b-t^2
  have bp : 0 < b := by linarith only [small.bLow]
  have tp : 0 < t := by linarith only [small.tLow]
  have rd := half_data c s hc hs.le rn
  have bd := half_data b t bp bn.1 bn.2.2
  have zn : 0 ≤ z := rd.1
  have hn : 0 ≤ h := bd.1
  have zh : z ≤ h := half_order c s b t rn hc hs.le bn order
  have hh : h ≤ 27/100 := small.hHigh
  have zHigh : z ≤ 27/100 := le_trans zh hh
  have bounds := normal_bounds bn
  have btUpper := mul_nonneg (sub_nonneg.mpr bounds.2.1) bn.1
  have aLower : -(9/10) ≤ A := by
    dsimp [A]
    nlinarith only [bounds.2.2.2.2.1,btUpper,small.tHigh]
  have bUpper : B ≤ 0 := by dsimp [B]; nlinarith only [bn.2.1,sq_nonneg t]
  have zhProduct := mul_nonneg (sub_nonneg.mpr zh) hn
  have hSquare := mul_nonneg hn (sub_nonneg.mpr hh)
  have oneMinus : 0 ≤ 1-z*h := by nlinarith only [zhProduct,hSquare,hh]
  have dLower : 1 ≤ (1+z^2)*(1+h^2) := by
    have product := mul_nonneg (sq_nonneg z) (sq_nonneg h)
    nlinarith only [sq_nonneg z,sq_nonneg h,product]
  have bWeight := mul_nonneg (neg_nonneg.mpr bUpper) oneMinus
  have bracket : 0 ≤ (1+z^2)*(1+h^2)+2*A*(h+z)-2*B*(1-z*h) := by
    have span : h+z ≤ 27/50 := by
      calc
        _ ≤ 27/100+27/100 := add_le_add hh zHigh
        _ = _ := by norm_num
    have aBound : -(9/5)*(h+z) ≤ 2*A*(h+z) := by
      calc
        _ = 2*((-(9/10))*(h+z)) := by ring
        _ ≤ 2*(A*(h+z)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right aLower (add_nonneg hn zn)) (by norm_num)
        _ = _ := by ring
    have lower : 0 ≤ 1-(9/5)*(h+z) :=
      sub_nonneg.mpr (le_trans
        (mul_le_mul_of_nonneg_left span (by norm_num : (0:ℝ) ≤ 9/5)) (by norm_num))
    have middle : 0 ≤ (1+z^2)*(1+h^2)+2*A*(h+z) := by
      calc
        0 ≤ 1-(9/5)*(h+z) := lower
        _ = 1+(-(9/5)*(h+z)) := by ring
        _ ≤ _ := add_le_add dLower aBound
    convert add_nonneg middle (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) bWeight) using 1 <;> ring
  have difference := mul_nonneg (sub_nonneg.mpr zh) bracket
  have divided : (1+z^2)*(1+h^2)*
      ((1-z+c*A+s*B)-(1-h+b*A+t*B)) =
      (h-z)*((1+z^2)*(1+h^2)+2*A*(h+z)-2*B*(1-z*h)) := by
    calc
      _ = (1+z^2)*(1+h^2)*(h-z)+
          A*((1+h^2)*((1+z^2)*c)-(1+z^2)*((1+h^2)*b))+
          B*((1+h^2)*((1+z^2)*s)-(1+z^2)*((1+h^2)*t)) := by ring
      _ = _ := by
        rw [rd.2.2.2.2.1,rd.2.2.2.2.2,bd.2.2.2.2.1,bd.2.2.2.2.2]
        ring
  have ordered : 1-h+b*A+t*B ≤ 1-z+c*A+s*B := by
    have positive : 0 < (1+z^2)*(1+h^2) :=
      mul_pos (by nlinarith only [sq_nonneg z]) (by nlinarith only [sq_nonneg h])
    apply le_of_not_gt
    intro no
    have negative := mul_neg_of_pos_of_neg positive
      (show (1-z+c*A+s*B)-(1-h+b*A+t*B) < 0 by linarith only [no])
    nlinarith only [difference,divided,negative]
  let f := 1+t^2+(7/5)*b*t-b-2*t
  have fWeight := mul_nonneg (show 0 ≤ b-43/50 by linarith only [small.bLow])
    (show 0 ≤ 1-(7/5)*t by linarith only [small.tHigh])
  have chord := mul_nonneg (show 0 ≤ t-47/100 by linarith only [small.tLow])
    (sub_nonneg.mpr small.tHigh)
  have fNegative : f < 0 := by
    dsimp [f]
    nlinarith only [fWeight,chord,small.tHigh]
  have endpoint : t*(1-h+b*A+t*B) = -f := by
    dsimp [A,B,f]
    linear_combination t*(1-t)*bn.2.2-bd.2.2.2.1
  have endpointPositive : 0 < 1-h+b*A+t*B :=
    pos_of_mul_pos_right (by linarith only [endpoint,fNegative]) tp.le
  have insidePositive : 0 < 1-z+c*A+s*B := lt_of_lt_of_le endpointPositive ordered
  have identity : s*((b*c+t*s)*(1-b)+(b*s-t*c)*(b+t-1))+
      c^2-(2/5)*c*s+c+s-2 = s*(1-z+c*A+s*B) := by
    dsimp [A,B]
    linear_combination s*(s-c)*bn.2.2+rn+rd.2.2.2.1
  rw [identity]
  exact mul_pos hs insidePositive

theorem ru_positive (c s b t : ℝ) (rn : c^2+s^2=1) (hc : 0 < c) (hs : 0 < s)
    (bn : Normal b t) (small : Minor b t) :
    0 < s*((b*c+t*s)*(1-b)+(b*s-t*c)*(1+(2/5)*t))+
      c^2-(2/5)*c*s+c+s-2 := by
  let z := half c s
  let C := 7/5-b+t-(3/5)*t^2
  let K := b+t-1-(3/5)*b*t
  have rd := half_data c s hc hs.le rn
  have bLower : 433/500 < b := by
    apply lt_of_not_ge
    intro no
    have bSquare := mul_nonneg (sub_nonneg.mpr no)
      (show 0 ≤ 433/500+b by linarith only [small.bLow])
    have tSquare := mul_nonneg (sub_nonneg.mpr small.tHigh)
      (show 0 ≤ 1/2+t by linarith only [bn.1])
    nlinarith only [bSquare,tSquare,bn.2.2]
  have chord := mul_nonneg (sub_nonneg.mpr small.tHigh)
    (show 0 ≤ 7/10-(3/5)*t by linarith only [small.tHigh])
  have cUpper : C ≤ 221/250 := by dsimp [C]; nlinarith only [bLower,chord]
  have kLower : 1/10 ≤ K := small.kLow
  have cWeight := mul_nonneg hc.le (sub_nonneg.mpr cUpper)
  have kWeight := mul_nonneg hs.le (sub_nonneg.mpr kLower)
  have endpoint : 1-z-(221/250)*c+s/10 ≤ 1-z-c*C+s*K := by
    nlinarith only [cWeight,kWeight]
  have polynomial := C981CompletionLastWallPolynomials.third z rd.1 rd.2.1
  have identity : (1+z^2)*(1-z-(221/250)*c+s/10)=
      29/250-(4/5)*z+(471/250)*z^2-z^3 := by
    calc
      _ = (1+z^2)*(1-z)-(221/250)*((1+z^2)*c)+((1+z^2)*s)/10 := by ring
      _ = _ := by rw [rd.2.2.2.2.1,rd.2.2.2.2.2]; ring
  have productPositive : 0 < (1+z^2)*(1-z-(221/250)*c+s/10) := by
    rw [identity]
    exact polynomial
  have lowerPositive : 0 < 1-z-(221/250)*c+s/10 :=
    pos_of_mul_pos_right productPositive (add_nonneg (by norm_num) (sq_nonneg z))
  have insidePositive : 0 < 1-z-c*C+s*K := lt_of_lt_of_le lowerPositive endpoint
  have formula : s*((b*c+t*s)*(1-b)+(b*s-t*c)*(1+(2/5)*t))+
      c^2-(2/5)*c*s+c+s-2 = s*(1-z-c*C+s*K) := by
    dsimp [C,K]
    linear_combination -s*c*bn.2.2+rn+rd.2.2.2.1
  rw [formula]
  exact mul_pos hs insidePositive

#print axioms bu_negative
#print axioms bu_positive
#print axioms ru_negative
#print axioms ru_positive
end N12Compact.C981CompletionLastRightScalars
