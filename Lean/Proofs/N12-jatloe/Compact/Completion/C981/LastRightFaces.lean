import Compact.Completion.C981.LastRightScalars
import Compact.Completion.C981.CornerAdvance

/-! Actual support faces in the final C981 right-wall comparison. -/
namespace N12Compact.C981CompletionLastRightFaces

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977ChainBridge C981CompletionLastRightScalars
open C981CompletionSupportForms
set_option Elab.async false

theorem faces (B : OpenSquare) (bn : Normal B.c B.s) (side : 1 < B.side)
    (marker : B.Inside (-(7/20)) (7/20))
    (low : B.Inside (-1) (13/50)) (high : B.Inside (-1) (2/5))
    (missingLow : ¬ B.Inside (-1) 0) (missingInner : ¬ B.Inside (-(2/5)) 0)
    (missingCorner : ¬ B.Inside (-1) 1) (missingTop : ¬ B.Inside (-(2/5)) 1) :
    -B.c ≤ B.loU ∧ (2/5)*B.s ≤ B.loV ∧
      B.loU+B.side ≤ B.s-(2/5)*B.c ∧ B.loV+B.side ≤ B.c+B.s := by
  let Q := B.translated (-2) (-2)
  have qMarker : Q.Inside (33/20) (47/20) := by
    apply (inside_translated_iff B (-2) (-2) _ _).mpr
    norm_num
    exact marker
  have qLow : Q.Inside 1 (113/50) := by
    apply (inside_translated_iff B (-2) (-2) _ _).mpr
    norm_num
    exact low
  have qHigh : Q.Inside 1 (12/5) := by
    apply (inside_translated_iff B (-2) (-2) _ _).mpr
    norm_num
    exact high
  have qMissing (x y : ℝ) (point : ¬ B.Inside (-2+x) (-2+y)) : ¬ Q.Inside x y :=
    fun h => point ((inside_translated_iff B (-2) (-2) _ _).mp h)
  have raw := C981CompletionLastPositivePair.neighbor_faces_any Q bn side qMarker qLow qHigh
    (qMissing 1 2 (by norm_num; exact missingLow))
    (qMissing (8/5) 2 (by norm_num; exact missingInner))
    (qMissing 1 3 (by norm_num; exact missingCorner))
    (qMissing (8/5) 3 (by norm_num; exact missingTop))
  dsimp [Q,OpenSquare.translated] at raw
  exact ⟨by linarith only [raw.1],by linarith only [raw.2.1],
    by linarith only [raw.2.2.1],by linarith only [raw.2.2.2]⟩

theorem upper_wall (R : OpenSquare) (wall : ∀ x y, R.Inside x y → y ≤ 2) :
    R.s*(R.loU+R.side)+R.c*(R.loV+R.side) ≤ 2 := by
  let Q := R.translated 0 1
  have bound : ∀ x y, Q.Inside x y → y ≤ 1 := by
    intro x y point
    have raw := wall _ _ ((inside_translated_iff R 0 1 _ _).mp point)
    linarith only [raw]
  have raw := C981CompletionCornerAdvance.upper_wall Q bound
  dsimp [Q,OpenSquare.translated] at raw
  nlinarith only [raw,R.unit_normal]

theorem alternatives (B R : OpenSquare) (bn : Normal B.c B.s)
    (rc : 0 < R.c) (rs : 0 ≤ R.s) (side : 1 < B.side) (same : B.side=R.side)
    (minor : Minor B.c B.s)
    (bands : -B.c ≤ B.loU ∧ (2/5)*B.s ≤ B.loV ∧
      B.loU+B.side ≤ B.s-(2/5)*B.c ∧ B.loV+B.side ≤ B.c+B.s)
    (high : B.Inside (-1) (2/5))
    (rA : R.Inside (-(2/5)) 1) (rD : R.Inside (13/50) 1)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) :
    B.loU+B.side ≤ lower R B.c B.s ∨ upper B R.c R.s ≤ R.loU := by
  let alpha := B.c*R.c+B.s*R.s
  let beta := B.c*R.s-B.s*R.c
  have bp : 0 < B.c := by linarith only [minor.bLow]
  have tp : 0 < B.s := by linarith only [minor.tLow]
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos bp rc,mul_nonneg bn.1 rs]
  have noBV (h : upper B (-B.s) B.c ≤ lower R (-B.s) B.c ∨
      upper R (-B.s) B.c ≤ lower B (-B.s) B.c) : False := by
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have own := strict_bounds B _ _ (-B.s) B.c unit high
    rcases h with forward | reverse
    · have other := (strict_bounds R _ _ (-B.s) B.c unit rD).1
      nlinarith only [forward,own.2,other,minor.tLow,minor.bHigh]
    · have other := (strict_bounds R _ _ (-B.s) B.c unit rA).2
      nlinarith only [reverse,own.1,other,minor.bLow,minor.tHigh]
  have noRV (h : upper B (-R.s) R.c ≤ lower R (-R.s) R.c ∨
      upper R (-R.s) R.c ≤ lower B (-R.s) R.c) : False := by
    have unit : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
    have maxFormula := upper_in_bands B (-R.s) R.c
    have minFormula := lower_in_bands B (-R.s) R.c
    have first : (-R.s)*B.c+R.c*B.s=-beta := by dsimp [beta]; ring
    have last : -(-R.s)*B.s+R.c*B.c=alpha := by dsimp [alpha]; ring
    rw [first,last,abs_of_pos ap] at maxFormula minFormula
    by_cases sign : beta ≤ 0
    · have coords := C981CompletionOppositeSupport.cross_order B.c B.s R.c R.s
        bp bn.1 rc rs bn.2.2 R.unit_normal (by dsimp [beta] at sign; linarith only [sign])
      rw [abs_of_nonneg (neg_nonneg.mpr sign)] at maxFormula minFormula
      rcases h with forward | reverse
      · have bound := (strict_bounds R _ _ (-R.s) R.c unit rD).1
        have one := mul_nonneg (neg_nonneg.mpr sign) (sub_nonneg.mpr bands.1)
        have two := mul_nonneg ap.le (sub_nonneg.mpr bands.2.1)
        have strict := mul_pos (show 0 < alpha-beta by linarith only [ap,sign]) (sub_pos.mpr side)
        let K := B.c+B.s-1-(3/5)*B.c*B.s
        let G := 63/50+B.s-B.c-(3/5)*B.s^2
        have kp : 0 < K := by dsimp [K]; linarith only [minor.kLow]
        have gp : 0 < G := by
          have square := mul_nonneg (sub_nonneg.mpr minor.tHigh)
            (show 0 ≤ 1/2+B.s by linarith only [bn.1])
          dsimp [G]
          nlinarith only [minor.bHigh,bn.1,square]
        have identity : -beta*(1-B.c)+alpha*(1+(2/5)*B.s)-(R.c-(13/50)*R.s)=
            R.c*K+R.s*G := by
          dsimp [alpha,beta,K,G]
          linear_combination R.s*bn.2.2
        have k := mul_pos rc kp
        have g := mul_nonneg rs gp.le
        have difference : upper B (-R.s) R.c -
            (-beta*(1-B.c)+alpha*(1+(2/5)*B.s)) =
            -beta*(B.loU- -B.c)+alpha*(B.loV-(2/5)*B.s)+
              (alpha-beta)*(B.side-1) := by
          rw [maxFormula]
          ring
        have support : -beta*(1-B.c)+alpha*(1+(2/5)*B.s) <
            upper B (-R.s) R.c := by
          apply sub_pos.mp
          rw [difference]
          exact add_pos_of_nonneg_of_pos (add_nonneg one two) strict
        have margin : R.c-(13/50)*R.s <
            -beta*(1-B.c)+alpha*(1+(2/5)*B.s) := by
          apply sub_pos.mp
          rw [identity]
          exact add_pos_of_pos_of_nonneg k g
        have bound' : lower R (-R.s) R.c < R.c-(13/50)*R.s := by
          convert bound using 1 <;> ring
        exact (not_lt_of_ge forward) (lt_trans bound' (lt_trans margin support))
      · have own := (strict_bounds B _ _ (-R.s) R.c unit high).1
        have other := (strict_bounds R _ _ (-R.s) R.c unit rA).2
        nlinarith only [reverse,own,other,coords.1,coords.2,minor.bLow,minor.tHigh]
    · have sign' : 0 ≤ beta := le_of_lt (lt_of_not_ge sign)
      rw [abs_of_nonpos (neg_nonpos.mpr sign')] at maxFormula minFormula
      rcases h with forward | reverse
      · have own := (strict_bounds B _ _ (-R.s) R.c unit high).2
        have other := (strict_bounds R _ _ (-R.s) R.c unit rD).1
        have ratio : 0 < (63/50)*B.s-(3/5)*B.c := by
          linarith only [minor.tLow,minor.bHigh]
        have comparison := mul_pos rc ratio
        have cross := mul_nonneg (by norm_num : (0:ℝ) ≤ 63/50) sign'
        dsimp [beta] at cross
        have product : 0 < B.c*((63/50)*R.s-(3/5)*R.c) := by
          nlinarith only [comparison,cross]
        have margin := pos_of_mul_pos_right product bp.le
        nlinarith only [forward,own,other,margin]
      · have other := (strict_bounds R _ _ (-R.s) R.c unit rA).2
        have one := mul_nonneg sign' (sub_nonneg.mpr bands.1)
        have two := mul_nonneg ap.le (show 0 ≤ B.c+B.s-B.side-B.loV by linarith only [bands.2.2.2])
        have strict := mul_pos (show 0 < alpha+beta by linarith only [ap,sign']) (sub_pos.mpr side)
        let F := B.s-B.c-B.s^2
        let G := 3/5+B.c*B.s-B.c-B.s
        have fn : F < 0 := by dsimp [F]; nlinarith only [minor.bLow,minor.tHigh,sq_nonneg B.s]
        have bt := mul_nonneg (show 0 ≤ 1-B.c by linarith only [(normal_bounds bn).2.1]) bn.1
        have gn : G ≤ 0 := by dsimp [G]; nlinarith only [bt,minor.bLow]
        have identity : alpha*(B.c+B.s-1)+beta*(B.c-1)-(R.c+(2/5)*R.s)=R.c*F+R.s*G := by
          dsimp [alpha,beta,F,G]
          linear_combination (R.c+R.s)*bn.2.2
        have f := mul_neg_of_pos_of_neg rc fn
        have g := mul_nonpos_of_nonneg_of_nonpos rs gn
        have difference : alpha*(B.c+B.s-1)+beta*(B.c-1)-
            lower B (-R.s) R.c =
            beta*(B.loU- -B.c)+alpha*(B.c+B.s-B.side-B.loV)+
              (alpha+beta)*(B.side-1) := by
          rw [minFormula]
          ring
        have support : lower B (-R.s) R.c <
            alpha*(B.c+B.s-1)+beta*(B.c-1) := by
          apply sub_pos.mp
          rw [difference]
          exact add_pos_of_nonneg_of_pos (add_nonneg one two) strict
        have margin : alpha*(B.c+B.s-1)+beta*(B.c-1) < R.c+(2/5)*R.s := by
          apply sub_neg.mp
          rw [identity]
          exact add_neg_of_neg_of_nonpos f g
        have other' : R.c+(2/5)*R.s < upper R (-R.s) R.c := by
          convert other using 1 <;> ring
        exact (not_lt_of_ge reverse) (lt_trans support (lt_trans margin other'))
  have all := CongruentSAT.faceSeparation_of_disjoint B R same apart
  change pairRadius B R ≤ |B.c*(centerX R-centerX B)+B.s*(centerY R-centerY B)| ∨
    pairRadius B R ≤ |-B.s*(centerX R-centerX B)+B.c*(centerY R-centerY B)| ∨
    pairRadius R B ≤ |R.c*(centerX R-centerX B)+R.s*(centerY R-centerY B)| ∨
    pairRadius R B ≤ |-R.s*(centerX R-centerX B)+R.c*(centerY R-centerY B)| at all
  have sep (x y radius : ℝ) (identity : supportRadius B x y+supportRadius R x y=radius)
      (h : radius ≤ |x*(centerX R-centerX B)+y*(centerY R-centerY B)|) :=
    separated B R x y (by rwa [identity])
  have forward (x y : ℝ) (xp : 0 < x) (yp : 0 ≤ y) (unit : x^2+y^2=1)
      (h : upper B x y ≤ lower R x y ∨ upper R x y ≤ lower B x y) :
      upper B x y ≤ lower R x y := by
    rcases h with h | h
    · exact h
    · have own := (strict_bounds B _ _ x y unit high).1
      have other := (strict_bounds R _ _ x y unit rD).2
      exfalso
      nlinarith only [h,own,other,xp,yp]
  rcases all with bu | bv | ru | rv
  · left
    simpa only [(ownU B).2] using forward _ _ bp bn.1 B.unit_normal
      (sep _ _ _ (parallel_radius B R) bu)
  · exact False.elim (noBV (sep _ _ _ (transverse_radius B R) bv))
  · have identity : supportRadius B R.c R.s+supportRadius R R.c R.s=pairRadius R B := by
      rw [add_comm]; exact parallel_radius R B
    right
    simpa only [(ownU R).1] using forward _ _ rc rs R.unit_normal (sep _ _ _ identity ru)
  · have identity : supportRadius B (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R B := by
      rw [add_comm]; exact transverse_radius R B
    exact False.elim (noRV (sep _ _ _ identity rv))

#print axioms alternatives
end N12Compact.C981CompletionLastRightFaces
