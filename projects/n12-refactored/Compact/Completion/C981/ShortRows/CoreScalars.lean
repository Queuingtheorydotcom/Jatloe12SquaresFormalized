import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Continuous margins for the four-diamond central owner. All input
normals are actual square normals; no orientation mesh is used. -/
namespace N12Compact.C981CompletionShortScalars
open C977CornerCubic
set_option Elab.async false

def Core (c s : ℝ) : Prop :=
  24/25 ≤ c ∧ c ≤ 1 ∧ 0 ≤ s ∧ s ≤ 13/50 ∧ s ≤ (9/35)*c

theorem core_bounds {c s : ℝ} (normal : Normal c s) (narrow : 35*s ≤ 9*c) :
    Core c s := by
  have bounds := normal_bounds normal
  have square := mul_nonneg (show 0 ≤ 9*c-35*s by linarith only [narrow])
    (show 0 ≤ 9*c+35*s by linarith only [bounds.1,normal.1])
  have lower : 24/25 ≤ c := by
    by_contra bad
    have product := mul_nonneg
      (show 0 ≤ 24/25-c by linarith only [bad])
      (show 0 ≤ 24/25+c by linarith only [bounds.1])
    nlinarith only [square,product,normal.2.2]
  exact ⟨lower,bounds.2.1,normal.1,by linarith only [narrow,bounds.2.1],
    by linarith only [narrow]⟩

private theorem defect {b t : ℝ} (normal : Normal b t) :
    1-b ≤ (3/5)*t^2 := by
  have bounds := normal_bounds normal
  have product := mul_nonneg
    (show 0 ≤ b-2/3 by linarith only [bounds.1])
    (show 0 ≤ 1-b by linarith only [bounds.2.1])
  nlinarith only [product,normal.2.2]

theorem backward_u {c s b t : ℝ} (core : Core c s) (bp : 0 < b)
    (negative : t ≤ 0) (canonical : -b ≤ t) :
    0 < b*(c-7/10+(7/20)*s^2+(61/100)*c*s)+
      t*(s+9/100+(61/100)*s^2-(7/20)*c*s) := by
  have cslo := mul_nonneg core.2.2.1 (sub_nonneg.mpr core.1)
  have cshi := mul_nonneg core.2.2.1 (sub_nonneg.mpr core.2.1)
  have s2 : s^2 ≤ 169/2500 := by
    nlinarith only [core.2.2.1,core.2.2.2.1]
  let f := c-7/10+(7/20)*s^2+(61/100)*c*s
  let g := s+9/100+(61/100)*s^2-(7/20)*c*s
  have gp : 0 ≤ g := by
    dsimp [g]; nlinarith only [cshi,core.2.2.1,sq_nonneg s]
  have margin : 13/100 < f-g := by
    dsimp [f,g]
    nlinarith only [cslo,core.1,core.2.2.2.1,s2]
  have one := mul_nonneg gp (show 0 ≤ t+b by linarith only [canonical])
  have two := mul_pos bp (lt_trans (by norm_num : (0:ℝ) < 13/100) margin)
  dsimp [f,g] at one two
  nlinarith only [one,two]

theorem positive_own_v {c s b t : ℝ} (core : Core c s) (normal : Normal b t) :
    b*(37/50+(61/100)*s^2-(7/20)*c*s+s)+
      t*(27/20-(7/20)*s^2-(61/100)*c*s-c) < 1 := by
  have bounds := normal_bounds normal
  have cslo := mul_nonneg core.2.2.1 (sub_nonneg.mpr core.1)
  have span := mul_nonneg core.2.2.1 (sub_nonneg.mpr core.2.2.2.1)
  let r := 37/50+(83/100)*s
  let w := 39/100-(29/50)*s
  have first : 37/50+(61/100)*s^2-(7/20)*c*s+s ≤ r := by
    dsimp [r]; nlinarith only [cslo,span]
  have last : 27/20-(7/20)*s^2-(61/100)*c*s-c ≤ w := by
    dsimp [w]; nlinarith only [cslo,core.1,core.2.2.1,sq_nonneg s]
  have short : r^2+w^2 < 1 := by
    dsimp [r,w]
    nlinarith only [span,core.2.2.2.1]
  have identity : (b*r+t*w)^2+(b*w-t*r)^2=r^2+w^2 := by
    calc
      _ = (b^2+t^2)*(r^2+w^2) := by ring
      _ = _ := by rw [normal.2.2]; ring
  have projection : b*r+t*w < 1 := by
    nlinarith only [short,identity,sq_nonneg (b*w-t*r),sq_nonneg (b*r+t*w-1)]
  exact lt_of_le_of_lt
    (add_le_add (mul_le_mul_of_nonneg_left first (by linarith only [bounds.1]))
      (mul_le_mul_of_nonneg_left last normal.1)) projection

theorem negative_low {c s b u : ℝ} (core : Core c s) (normal : Normal b u) :
    0 < c*(b-37/50+(13/20)*u^2+(9/20)*b*u)+
      s*(-7/20-(9/20)*u^2+(13/20)*b*u-u) := by
  have bounds := normal_bounds normal
  have dd := defect normal
  have u2 : u^2 ≤ 1/2 := by
    have product := mul_nonneg (sub_nonneg.mpr normal.2.1)
      (show 0 ≤ b+u by linarith only [bounds.1,normal.1])
    nlinarith only [product,normal.2.2]
  let f := b-37/50+(13/20)*u^2+(9/20)*b*u
  let g := -7/20-(9/20)*u^2+(13/20)*b*u-u
  have fp : 0 ≤ f := by
    dsimp [f]; nlinarith only [dd,mul_nonneg (show 0 ≤ b by linarith only [bounds.1]) normal.1,
      sq_nonneg u]
  have gn : g ≤ 0 := by
    have high := mul_nonneg normal.1 (sub_nonneg.mpr bounds.2.1)
    dsimp [g]; nlinarith only [high,normal.1,sq_nonneg u]
  have first := mul_nonneg fp (sub_nonneg.mpr core.1)
  have last := mul_nonneg (show 0 ≤ -g by linarith only [gn])
    (sub_nonneg.mpr core.2.2.2.1)
  have bu := mul_nonneg normal.1 (sub_nonneg.mpr bounds.1)
  dsimp [f,g] at first last
  nlinarith only [first,last,dd,bu,u2,normal.1]

theorem negative_steep {c s b u : ℝ} (core : Core c s) (normal : Normal b u)
    (steep : (10/37)*b ≤ u) :
    0 < c*((13/20)*b*u-(9/100)*u^2)-
      s*(7/20+(13/20)*u^2+(9/100)*b*u) := by
  have bounds := normal_bounds normal
  have bu := mul_nonneg (show 0 ≤ b by linarith only [bounds.1]) normal.1
  have uu := mul_nonneg normal.1 (sub_nonneg.mpr normal.2.1)
  have product := mul_nonneg (show 0 ≤ u-(10/37)*b by linarith only [steep])
    (sub_nonneg.mpr normal.2.1)
  have square : 0 < b^2 := by nlinarith only [bounds.1]
  have margin : 0 < (3/5)*b*u-(13/50)*u^2-23/250 := by
    nlinarith only [product,bu,square,normal.2.2]
  have fp : 0 ≤ (13/20)*b*u-(9/100)*u^2 := by nlinarith only [uu,bu]
  have gp : 0 ≤ 7/20+(13/20)*u^2+(9/100)*b*u := by nlinarith only [bu,sq_nonneg u]
  have first := mul_nonneg fp (sub_nonneg.mpr core.1)
  have last := mul_nonneg gp (sub_nonneg.mpr core.2.2.2.1)
  nlinarith only [first,last,margin,bu,sq_nonneg u]

theorem positive_small {c s b t : ℝ} (core : Core c s) (normal : Normal b t)
    (small : t ≤ 13/50) :
    0 < c*(b-37/50+(13/20)*t^2-(13/20)*b*t)+
      s*(-7/20-(13/20)*t^2-(13/20)*b*t+t) := by
  have bounds := normal_bounds normal
  have dd := defect normal
  have bt := mul_nonneg normal.1 (sub_nonneg.mpr bounds.2.1)
  have t2 : t^2 ≤ 169/2500 := by nlinarith only [normal.1,small]
  let f := b-37/50+(13/20)*t^2-(13/20)*b*t
  let g := -7/20-(13/20)*t^2-(13/20)*b*t+t
  have fp : 0 ≤ f := by dsimp [f]; nlinarith only [dd,bt,small,sq_nonneg t]
  have gn : g ≤ 0 := by
    have lower := mul_nonneg normal.1 (sub_nonneg.mpr normal.2.1)
    dsimp [g]; nlinarith only [lower,sq_nonneg (t-5/13)]
  have first := mul_nonneg fp (sub_nonneg.mpr core.1)
  have last := mul_nonneg (show 0 ≤ -g by linarith only [gn])
    (sub_nonneg.mpr core.2.2.2.1)
  dsimp [f,g] at first last
  nlinarith only [first,last,dd,bt,small,t2]

theorem positive_low {c s b t : ℝ} (core : Core c s) (normal : Normal b t) :
    0 < c*(b-37/50+(13/20)*t^2-(9/20)*b*t)+
      s*(-7/20-(9/20)*t^2-(13/20)*b*t+t) := by
  have bounds := normal_bounds normal
  have dd := defect normal
  have bt : b*t ≤ 1/2 := by nlinarith only [normal.2.2,sq_nonneg (b-t)]
  let f := b-37/50+(13/20)*t^2-(9/20)*b*t
  let g := -7/20-(9/20)*t^2-(13/20)*b*t+t
  have fp : 0 ≤ f := by dsimp [f]; nlinarith only [dd,bt,sq_nonneg t]
  have gn : g ≤ 0 := by
    have lower := mul_nonneg normal.1 (sub_nonneg.mpr normal.2.1)
    dsimp [g]; nlinarith only [lower,sq_nonneg (t-5/11)]
  have first := mul_nonneg fp (sub_nonneg.mpr core.1)
  have last := mul_nonneg (show 0 ≤ -g by linarith only [gn])
    (sub_nonneg.mpr core.2.2.2.1)
  let h := b+t
  let d := b-t
  have hh : 1 ≤ h ∧ h ≤ 10/7 := ⟨bounds.2.2.2.2.1,bounds.2.2.2.2.2⟩
  have hd : 0 ≤ d := sub_nonneg.mpr normal.2.1
  have unit : h^2+d^2=2 := by dsimp [h,d]; nlinarith only [normal.2.2]
  have chord := mul_nonneg (sub_nonneg.mpr hh.1) (sub_nonneg.mpr hh.2)
  have hlow : 7/5-(5/12)*d^2 ≤ h := by
    have remainder : 0 ≤ 1/35-h/84 := by linarith only [hh.2]
    have positive := add_nonneg
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 5/12) chord) remainder
    have identity : h+(5/12)*d^2-7/5 =
        (5/12)*(h-1)*(10/7-h)+(1/35-h/84) := by
      linear_combination (5/12)*unit
    have positive' : 0 ≤ h+(5/12)*d^2-7/5 := by
      rw [identity]
      simpa only [mul_assoc] using positive
    linarith only [positive']
  have margin : 0 < (24/25)*b+(13/50)*t+(507/1000)*t^2-
      (601/1000)*b*t-4007/5000 := by
    have move := mul_nonneg hd (sub_nonneg.mpr hh.2)
    dsimp [h,d] at hlow move
    have nonnegative : 0 ≤ b-t := sub_nonneg.mpr normal.2.1
    nlinarith only [hlow,move,sq_nonneg (b-t-1/7),normal.2.2,nonnegative]
  dsimp [f,g] at first last
  nlinarith only [first,last,margin]

theorem positive_lower_u {c s b t : ℝ} (core : Core c s) (normal : Normal b t)
    (order : 0 ≤ c*t-s*b) :
    0 < c*(b+t-37/50-(1/5)*b*t)+
      s*(-4/5-(1/5)*t^2-b+t) := by
  have bounds := normal_bounds normal
  have cp : 0 < c := by linarith only [core.1]
  have bp : 0 < b := by linarith only [bounds.1]
  let f := b+t-37/50-(1/5)*b*t
  let g := -4/5-(1/5)*t^2-b+t
  have gn : g ≤ 0 := by dsimp [g]; nlinarith only [normal.2.1,sq_nonneg t]
  by_cases small : t ≤ (9/35)*b
  · have margin : 0 < 1-(37/50)*b-t := by linarith only [small,bounds.2.1,bounds.1]
    have weighted := mul_nonneg order (show 0 ≤ -g by linarith only [gn])
    have identity : b*(c*f+s*g)=c*(1-(37/50)*b-t)+(c*t-s*b)*(-g) := by
      dsimp [f,g]; linear_combination (c-c*t/5)*normal.2.2
    have positive := mul_pos cp margin
    have total : 0 < b*(c*f+s*g) := by
      dsimp [f,g] at identity weighted positive ⊢
      nlinarith only [identity,weighted,positive]
    exact pos_of_mul_pos_right total bp.le
  · have large : (9/35)*b ≤ t := (lt_of_not_ge small).le
    have tmin : 6/25 ≤ t := by
      apply le_of_not_gt
      intro smallt
      have blo : 24/25 ≤ b := by
        apply le_of_not_gt
        intro smallb
        have first := mul_pos (show 0 < 24/25-b by linarith only [smallb])
          (show 0 < 24/25+b by linarith only [bounds.1])
        have last := mul_pos (show 0 < 6/25-t by linarith only [smallt])
          (show 0 < 6/25+t by linarith only [normal.1])
        nlinarith only [normal.2.2,first,last]
      linarith only [large,blo,smallt]
    have thi : t ≤ 3/4 := by
      have square := mul_nonneg (sub_nonneg.mpr normal.2.1)
        (show 0 ≤ b+t by linarith only [bounds.1,normal.1])
      nlinarith only [square,normal.2.2,normal.1]
    have dd := defect normal
    have bt := mul_nonneg normal.1 (sub_nonneg.mpr bounds.2.1)
    have chord := mul_nonneg (sub_nonneg.mpr tmin) (sub_nonneg.mpr thi)
    have margin : 0 < f+(9/35)*g := by
      dsimp [f,g]; nlinarith only [dd,bt,chord,tmin,thi]
    have first := mul_pos cp margin
    have last := mul_nonneg (show 0 ≤ -g by linarith only [gn])
      (show 0 ≤ (9/35)*c-s by linarith only [core.2.2.2.2])
    dsimp [f,g] at first last
    nlinarith only [first,last]

end N12Compact.C981CompletionShortScalars
