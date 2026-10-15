import Compact.Completion.C1092.WallProfileScalars

/-! Uniform rational margins for the actual mixed-wide-wall crossing.
No angle partition or extremum computation is used. -/
namespace N12Compact.C1092MixedWideCrossingScalars
set_option Elab.async false

theorem small (c s z : ℝ) (cp : 0 < c) (sp : 0 < s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (zp : 0 < z) (zu : z < 1/2) (angle : z*(1+c)=s)
    (sform : (1+z^2)*s=2*z) (large : 2/5 < (1-z)^2/2) :
    z < 53/500 ∧ 97/100 < c ∧ s < 21/100 ∧ z ≤ (51/100)*s := by
  have zSmall : z < 53/500 := by
    apply lt_of_not_ge
    intro bad
    have square := mul_nonneg (sub_nonneg.mpr bad)
      (show 0 ≤ (1-z)+447/500 by linarith only [zu])
    nlinarith only [square,large]
  have monotone := mul_nonneg (show 0 ≤ 53/500-z by linarith only [zSmall])
    (show 0 ≤ 2-(21/100)*(53/500+z) by linarith only [zSmall])
  have polynomial : 0 < (21/100)*(1+z^2)-2*z := by
    nlinarith only [monotone]
  have sineSmall : s < 21/100 := by
    apply (mul_lt_mul_left (by positivity : 0 < 1+z^2)).mp
    nlinarith only [sform,polynomial]
  have cosineLarge : 97/100 < c := by
    apply lt_of_not_ge
    intro bad
    have csquare := mul_nonneg (sub_nonneg.mpr bad)
      (show 0 ≤ 97/100+c by linarith only [cp])
    have ssquare := mul_pos (sub_pos.mpr sineSmall)
      (show 0 < 21/100+s by linarith only [sp])
    nlinarith only [unit,csquare,ssquare]
  have halfBound : z ≤ (51/100)*s := by
    have weight := mul_nonneg sp.le
      (show 0 ≤ (51/100)*(1+c)-1 by linarith only [cosineLarge])
    apply (mul_le_mul_left (by linarith only [cp] : 0 < 1+c)).mp
    nlinarith only [angle,weight]
  exact ⟨zSmall,cosineLarge,sineSmall,halfBound⟩

theorem margins (c s d t z : ℝ) (cp : 0 < c) (sp : 0 < s)
    (cn : c^2+s^2=1) (dp : 0 < d) (tn : 0 ≤ t) (dn : d^2+t^2=1)
    (wide : 5/4 < d+t) (zp : 0 ≤ z) (zu : z < 53/500)
    (cosine : 97/100 < c) (sine : s < 21/100)
    (half : z ≤ (51/100)*s) (angle : z*(1+c)=s) :
    7/25 < t ∧ 0 < c*t-s*d ∧
      0 < t*(1-z-c+(2/5)*s)+(c*t-s*d)*(d+t-1) ∧
      0 < d*(-z*(c+s)+(13/50)*s^2)+
        t*((1-z)*s-(13/50)*s*c+2/5) := by
  have cu : c ≤ 1 := by nlinarith only [cn,sq_nonneg s,cp]
  have du : d ≤ 1 := by nlinarith only [dn,sq_nonneg t,dp]
  have tLarge : 7/25 < t := by
    have square := mul_pos (sub_pos.mpr wide)
      (show 0 < d+t+5/4 by linarith only [dp,tn])
    have product := mul_nonneg tn (sub_nonneg.mpr du)
    nlinarith only [square,dn,product]
  let k := c*t-s*d
  have kLarge : (11/50)*t < k := by
    have cWeight := mul_pos (show 0 < t by linarith only [tLarge])
      (sub_pos.mpr cosine)
    have dWeight := mul_nonneg sp.le (sub_nonneg.mpr du)
    dsimp [k]
    nlinarith only [cWeight,dWeight,tLarge,sine]
  have kp : 0 < k := by nlinarith only [kLarge,tLarge]
  have first : 0 < t*(1-z-c+(2/5)*s)+k*(d+t-1) := by
    have base : -(11/100)*s ≤ 1-z-c+(2/5)*s := by
      linarith only [half,cu]
    have baseWeight := mul_nonneg (show 0 ≤ t by linarith only [tLarge])
      (sub_nonneg.mpr base)
    have sineWeight := mul_pos (show 0 < t by linarith only [tLarge])
      (sub_pos.mpr sine)
    have gain0 := mul_pos (sub_pos.mpr kLarge)
      (show 0 < d+t-1 by linarith only [wide])
    have gain1 := mul_pos (show 0 < t by linarith only [tLarge])
      (show 0 < (11/50)*(d+t-1)-11/200 by linarith only [wide])
    nlinarith only [baseWeight,sineWeight,gain0,gain1,tLarge]
  have ratio : z*(c+s) ≤ (121/200)*s := by
    have bound : c+s ≤ (121/200)*(1+c) := by linarith only [cu,sine]
    have weight := mul_nonneg zp (sub_nonneg.mpr bound)
    nlinarith only [weight,angle]
  have second : 0 < d*(-z*(c+s)+(13/50)*s^2)+
      t*((1-z)*s-(13/50)*s*c+2/5) := by
    have coefficient : 0 ≤ 1-z-(13/50)*c-317/500 := by
      linarith only [zu,cu]
    have firstWeight := mul_nonneg dp.le
      (show 0 ≤ -z*(c+s)+(13/50)*s^2+(121/200)*s by
        nlinarith only [ratio,sq_nonneg s])
    have secondWeight := mul_nonneg tn (mul_nonneg sp.le coefficient)
    have dWeight := mul_nonneg sp.le (sub_nonneg.mpr du)
    have tWeight := mul_nonneg sp.le (show 0 ≤ t-7/25 by linarith only [tLarge])
    nlinarith only [firstWeight,secondWeight,dWeight,tWeight,tLarge,sine]
  exact ⟨tLarge,kp,first,second⟩

#print axioms small
#print axioms margins
end N12Compact.C1092MixedWideCrossingScalars
