import Compact.Completion.C1092.MPPMOnePositiveMissingEnding

/-! ONE-POSITIVE-CONTINUOUS-ENDING Lemma 3.1.  The next retaining
negative owner's slope is below one half.  The proof keeps the same
two actual squares and both directed normal sources; a finite quadratic
difference replaces the manuscript's ratio monotonicity argument. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports Completion.OtherCases
set_option Elab.async false
noncomputable section

structure RetainingPairInput (C E : OpenSquare) : Prop where
  source : C1092MPPMAllNonpositive.Core C
  same : C.side=E.side
  close : 97/100<C.c
  small : 4*(-C.s)<C.c
  height : C.loV+C.side<43/500
  recipient : Normal E.c (-E.s)
  marker : E.Inside (7/20) (-7/20)
  ordinary : E.Inside (13/50) (-1)
  forward : E.Inside 0 (-13/50)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

private theorem retaining_pair_axes (C E : OpenSquare) (h : RetainingPairInput C E) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
  have cb := normal_bounds h.source.normal
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [cb.1]
  have dp : 0<E.c := by linarith only [eb.1]
  have small : -C.s<1/4 := by linarith only [h.small,cb.2.1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx ∧ 0<(61/100)*nx-(13/20)*ny := by
    have a := (strict_bounds C _ _ nx ny unit h.source.marker).2
    have b := (strict_bounds E _ _ nx ny unit h.marker).1
    have c := (strict_bounds E _ _ nx ny unit h.ordinary).1
    constructor <;> linarith only [a,b,c,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C E h.same h.apart
      with a|b|c|d|e|f|g|j
  · exact Or.inl (by simpa only [(ownU C).2] using a)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) b).1
    exact False.elim (by linarith only [no,cp])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) c).2
    exact False.elim (by linarith only [no,h.close,small])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) d).1
    exact False.elim (by linarith only [no,h.source.normal.1])
  · exact Or.inr (by simpa only [(ownU E).1] using e)
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) f).1
    exact False.elim (by linarith only [no,dp])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) g).2
    exact False.elim (by linarith only [no,h.recipient.2.1,dp])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) j).1
    exact False.elim (by linarith only [no,h.recipient.1])

private theorem steep_retaining_support (c s d t : ℝ) (cn : Normal c s)
    (close : 97/100<c) (small : 4*s<c) (en : Normal d t) (steep : d≤2*t) :
    (c*d+s*t)*(13/50)*t+(c*t-s*d)*((13/50)*t-d)<0 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [close]
  have dp : 0<d := by linarith only [eb.1]
  have tp : 0<t := by linarith only [dp,steep]
  let Q := (1/4)*d^2-(161/200)*d*t+(13/40)*t^2
  let R := d^2+(13/50)*t^2-(13/50)*d*t
  have dt : 0≤d*(d-t) := mul_nonneg dp.le (sub_nonneg.mpr en.2.1)
  have rp : 0<R := by
    dsimp [R]
    nlinarith only [dt,sq_pos_of_pos dp,sq_nonneg t]
  have first := mul_pos (show 0<c/4-s by linarith only [small]) rp
  have diff := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤t-d/2 by linarith only [steep])
    (show (13/40)*t-(257/400)*d≤0 by linarith only [en.2.1,dp])
  have cap : Q≤-(57/800)*d^2 := by
    dsimp [Q]
    nlinarith only [diff]
  have bound := mul_le_mul_of_nonneg_left cap cp.le
  have negative := mul_pos cp (sq_pos_of_pos dp)
  dsimp [Q,R] at *
  nlinarith only [first,bound,negative]

/-- The full two-normal argument, with a weak hypothesized half-slope
endpoint. No clearance of E is assumed in this angle reduction. -/
theorem retaining_successor_half_slope (C E : OpenSquare) (h : RetainingPairInput C E) :
    2*(-E.s)<E.c := by
  apply lt_of_not_ge
  intro steep
  have f := C1092MPPMAllNonpositive.faces C h.source
  have cb := normal_bounds h.source.normal
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [h.close]
  have sp : 0< -C.s := by linarith only [f.negative]
  have dp : 0<E.c := by linarith only [eb.1]
  have tp : 0< -E.s := by linarith only [dp,steep]
  let k := C.c*E.c+C.s*E.s
  let delta := -C.c*E.s+C.s*E.c
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_pos sp tp
    dsimp [k]
    nlinarith only [first,last]
  have delta_bound : (97/200)*(-E.s)<delta := by
    have a := mul_pos (show 0<C.c-97/100 by linarith only [h.close]) tp
    have b := mul_pos (show 0<C.c+4*C.s by linarith only [h.small]) tp
    have c := mul_nonneg sp.le (show 0≤-2*E.s-E.c by linarith only [steep])
    dsimp [delta]
    nlinarith only [a,b,c]
  have positive : 0<delta := by nlinarith only [delta_bound,tp]
  rcases retaining_pair_axes C E h with current|next
  · have formula := lower_nn E C.c C.s k delta
      (by dsimp [k]) (by dsimp [delta]) kp.le positive.le
    have first := mul_pos kp (show 0<(13/50)*(-E.s)-E.loU by
      linarith only [h.forward.1])
    have last := mul_pos positive (show 0<(13/50)*(-E.s)-E.c-E.loV by
      linarith only [h.ordinary.2.2.1])
    have scalar := steep_retaining_support C.c (-C.s) E.c (-E.s)
      h.source.normal h.close h.small h.recipient steep
    dsimp [k,delta] at formula first last
    nlinarith only [formula,first,last,scalar,current,f.lowerU,h.source.side,cb.2.1]
  · have formula := C1092TwoFifths.Support.upper_pos_neg C E.c E.s k (-delta)
      (by dsimp [k]; ring) (by dsimp [delta]; ring) kp.le (by linarith only [positive])
    have first := mul_nonneg kp.le (show 0≤C.loU+C.c by linarith only [f.lowerU])
    have last := mul_pos positive (show 0<43/500-C.loV-C.side by
      linarith only [h.height])
    have excess := mul_pos (sub_pos.mpr h.source.side) (add_pos kp positive)
    have radial := mul_nonneg kp.le (show 0≤1-C.c by linarith only [cb.2.1])
    dsimp [k,delta] at formula first last excess radial delta_bound
    nlinarith only [formula,first,last,excess,radial,delta_bound,h.forward.1,next,tp]

theorem retaining_successor_bounds (C E : OpenSquare) (h : RetainingPairInput C E) :
    89/100<E.c ∧ -E.s<9/20 := by
  have slope := retaining_successor_half_slope C E h
  have eb := normal_bounds h.recipient
  have product := mul_pos (show 0<E.c+2*E.s by linarith only [slope])
    (show 0<E.c-2*E.s by linarith only [eb.1,h.recipient.1])
  constructor
  · apply lt_of_not_ge
    intro low
    have square := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤E.c+89/100 by linarith only [eb.1])
      (show E.c-89/100≤0 by linarith only [low])
    nlinarith only [product,square,E.unit_normal]
  · apply lt_of_not_ge
    intro high
    have square := mul_nonneg (show 0≤-E.s-9/20 by linarith only [high])
      (show 0≤-E.s+9/20 by linarith only [h.recipient.1])
    nlinarith only [product,square,E.unit_normal]

end
#print axioms retaining_successor_half_slope
#print axioms retaining_successor_bounds
end N12Compact.C1092MPPMOnePositive
