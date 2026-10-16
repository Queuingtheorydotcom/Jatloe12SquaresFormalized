import Compact.Completion.C981.LastScalars

/-! Continuous scalar margins for a central square whose positive sine
is below .32. All endpoint comparisons use rational factorizations. -/
namespace N12Compact.C981CompletionLastPositiveScalars
open C977CornerCubic
set_option Elab.async false

theorem small_bounds {d r : ℝ} (normal : Normal d r) (small : r < 8/25) :
    947/1000 < d ∧ d+r < 127/100 := by
  have bounds := normal_bounds normal
  have square := mul_pos (show 0 < 8/25-r by linarith only [small])
    (show 0 < 8/25+r by linarith only [normal.1])
  have lower : 947/1000 < d := by
    apply lt_of_not_ge
    intro low
    have product := mul_nonneg (sub_nonneg.mpr low)
      (show 0 ≤ 947/1000+d by linarith only [bounds.1])
    nlinarith only [product,square,normal.2.2]
  have upper : d+r < 127/100 := by
    apply lt_of_not_ge
    intro high
    have product := mul_nonneg
      (show 0 ≤ d-(127/100-r) by linarith only [high])
      (show 0 ≤ d+(127/100-r) by linarith only [lower,small])
    have factor := mul_nonneg
      (show 0 ≤ 8/25-r by linarith only [small])
      (show 0 ≤ 127/50-2*(r+8/25) by linarith only [small])
    nlinarith only [product,factor,normal.2.2]
  exact ⟨lower,upper⟩

theorem neighbor_bounds {b t : ℝ} (normal : Normal b t) (angle : 1/2 ≤ t) :
    b ≤ 867/1000 ∧ 683/500 ≤ b+t ∧
      53/500 ≤ b+t-1-(3/5)*b*t ∧
      b-t-1/4+(3/5)*t^2 ≤ 267/1000 := by
  have bounds := normal_bounds normal
  have ts := mul_nonneg (sub_nonneg.mpr angle)
    (show 0 ≤ t+1/2 by linarith only [normal.1])
  have bSmall : b ≤ 867/1000 := by
    nlinarith only [normal.2.2,ts,sq_nonneg (b-867/1000)]
  have high : b+t ≤ 10/7 := bounds.2.2.2.2.2
  have low : 683/500 ≤ b+t := by
    apply le_of_not_gt
    intro no
    have tHigh : t ≤ 683/1000 := by linarith only [no,normal.2.1]
    have compare := mul_nonneg
      (show 0 ≤ 683/500-t-b by linarith only [no])
      (show 0 ≤ 683/500-t+b by linarith only [tHigh,bounds.1])
    have interval := mul_nonneg (sub_nonneg.mpr angle)
      (show 0 ≤ 433/500-t by linarith only [tHigh])
    nlinarith only [compare,interval,normal.2.2]
  have kProduct := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ 1-(3/10)*(b+t+683/500) by linarith only [high])
  have kLower : 53/500 ≤ b+t-1-(3/5)*b*t := by
    nlinarith only [kProduct,normal.2.2]
  have tHigh : t ≤ 5/7 := by linarith only [normal.2.1,high]
  have jProduct := mul_nonneg (sub_nonneg.mpr angle)
    (show 0 ≤ 1-(3/5)*(t+1/2) by linarith only [tHigh])
  have jUpper : b-t-1/4+(3/5)*t^2 ≤ 267/1000 := by
    nlinarith only [jProduct,bSmall]
  exact ⟨bSmall,low,kLower,jUpper⟩

theorem first_impossible (d r b t : ℝ) (cn : Normal d r) (bn : Normal b t)
    (small : r < 8/25) (angle : 1/2 ≤ t)
    (cut : 1 < b*(1+r-(13/50)*r^2-(31/50)*d*r)+
      t*(1-d+(13/50)*d*r-(31/50)*r^2)) : False := by
  have cb := normal_bounds cn
  have dl := (small_bounds cn small).1
  have cross := mul_nonneg (show 0 ≤ d by linarith only [cb.1]) cn.1
  have dr := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
  have defect : 1-d ≤ (3/5)*r^2 := by
    have product := mul_nonneg (sub_nonneg.mpr cb.2.1)
      (show 0 ≤ 3*d-2 by linarith only [dl])
    nlinarith only [product,cn.2.2]
  let F := 1+r-(13/50)*r^2-(31/50)*d*r
  let G := 1-d+(13/50)*d*r-(31/50)*r^2
  have span := mul_nonneg cn.1 (show 0 ≤ 8/25-r by linarith only [small])
  have fp : 43/50 ≤ F := by dsimp [F]; nlinarith only [dr,span,cn.1]
  have gu : G ≤ (13/50)*r := by dsimp [G]; nlinarith only [dr,defect,sq_nonneg r]
  have gc : G ≤ 52/625 := by linarith only [gu,small]
  have dlWeight := mul_nonneg cn.1 (show 0 ≤ d-947/1000 by linarith only [dl])
  have fu : F ≤ 1+(20643/50000)*r-(13/50)*r^2 := by dsimp [F]; nlinarith only [dlWeight]
  have increasing := mul_nonneg (show 0 ≤ 8/25-r by linarith only [small])
    (show 0 ≤ 20643/50000-(13/50)*(r+8/25) by linarith only [small])
  have maximum : F ≤ 172733/156250 := by nlinarith only [fu,increasing]
  have endpoint := C981CompletionLastScalars.half_endpoint_refined bn angle fp
    (show G ≤ 41/100 by linarith only [gc])
  change 1 < b*F+t*G at cut
  have last : (751/867)*F+G/2 < 1 := by
    linarith only [maximum,gc]
  exact (not_lt_of_ge (le_trans endpoint last.le)) cut

theorem second_impossible (d r b t : ℝ) (cn : Normal d r) (bn : Normal b t)
    (small : r < 8/25) (angle : 1/2 ≤ t)
    (cut : 1 < b*(1+r-(22/25)*r/(d+r))+
      t*(13/50+(1-d)-(22/25)*r/(d+r))) : False := by
  have cb := normal_bounds cn
  have ⟨dl,hl⟩ := small_bounds cn small
  have defect : 1-d ≤ (257/500)*r^2 := by
    have product := mul_nonneg (sub_nonneg.mpr cb.2.1)
      (show 0 ≤ (257/500)*(1+d)-1 by linarith only [dl])
    nlinarith only [product,cn.2.2]
  have hPositive : 0 < d+r := by linarith only [cb.2.2.2.2.1]
  have qLower : 69/100 < (22/25)/(d+r) :=
    (lt_div_iff₀ hPositive).mpr (by linarith only [hl])
  have qUpper : (22/25)/(d+r) ≤ 22/25 :=
    (div_le_iff₀ hPositive).mpr (by linarith only [cb.2.2.2.2.1])
  have qr := mul_nonneg cn.1
    (show 0 ≤ (22/25)/(d+r)-69/100 by linarith only [qLower])
  have qu := mul_nonneg cn.1 (sub_nonneg.mpr qUpper)
  let F := 1+r-(22/25)*r/(d+r)
  let G := 13/50+(1-d)-(22/25)*r/(d+r)
  have identity : (22/25)*r/(d+r)=((22/25)/(d+r))*r := by ring
  have fp : 43/50 ≤ F := by dsimp [F]; rw [identity]; nlinarith only [qu,cn.1]
  have fu : F ≤ 1+(31/100)*r := by dsimp [F]; rw [identity]; nlinarith only [qr]
  have gu : G ≤ 13/50+(257/500)*r^2-(69/100)*r := by
    dsimp [G]; rw [identity]; nlinarith only [qr,defect]
  have span := mul_nonneg cn.1 (show 0 ≤ 8/25-r by linarith only [small])
  have square : r^2 ≤ 64/625 := by
    nlinarith only [span,small]
  have gc : G ≤ 41/100 := by linarith only [gu,square,cn.1]
  have endpoint := C981CompletionLastScalars.half_endpoint bn angle fp gc
  change 1 < b*F+t*G at cut
  have last : (867/1000)*F+G/2 < 1 := by
    nlinarith only [fu,gu,span,small,cn.1]
  exact (not_lt_of_ge (le_trans endpoint last.le)) cut

#print axioms first_impossible
#print axioms second_impossible
end N12Compact.C981CompletionLastPositiveScalars
