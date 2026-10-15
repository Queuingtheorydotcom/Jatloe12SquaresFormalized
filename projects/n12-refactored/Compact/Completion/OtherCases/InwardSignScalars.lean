import Compact.Completion.OtherCases.SharpPointScalars

/-! Compact continuous margins for the inward-sign theorem. Endpoint
affinity, two unit-circle products, and a coarse chord bound replace
derivatives and square roots. -/
namespace N12Compact.Completion.OtherCases.InwardSignScalars
open C1092WallProfileScalars
set_option Elab.async false

theorem affine_negative (d r A B : ℝ) (dp : 0<d) (rn : 0≤r) (order : r≤d)
    (left : A<0) (right : A+B<0) : d*A+r*B<0 := by
  by_cases equal : r=d
  · rw [equal]
    have product := mul_neg_of_pos_of_neg dp right
    nlinarith only [product]
  · have gap : r<d := lt_of_le_of_ne order equal
    have first := mul_neg_of_pos_of_neg (sub_pos.mpr gap) left
    have last := mul_nonpos_of_nonneg_of_nonpos rn right.le
    nlinarith only [first,last]

theorem x_negative (c s : ℝ) (cp : 0<c) (sp : 0<s) (order : s≤c)
    (unit : c^2+s^2=1) :
    (1-c)*(c+s-1)-(13/50)*s<0 := by
  have bounds := CommonCases.CanonicalScalars.bounds c s cp sp.le order unit
  have factor := mul_nonneg sp.le
    (show 0≤1+c-2*s by linarith only [order,bounds.2.1])
  have scaled : 0≤(1+c)*(s-2*(1-c)) := by nlinarith only [factor,unit]
  have defect := nonneg_of_mul_nonneg_right scaled
    (show 0<1+c by linarith only [cp])
  have remainder := mul_nonneg (show 0≤1-c by linarith only [bounds.2.1])
    (show 0≤3/7-(c+s-1) by linarith only [bounds.2.2.2.1])
  nlinarith only [defect,remainder,sp]

private theorem c_strict (c s : ℝ) (cp : 0<c) (sp : 0<s) (unit : c^2+s^2=1) :
    c<1 := by
  have square := sq_pos_of_pos sp
  nlinarith only [unit,square,sq_nonneg (c-1),cp]

theorem negative_bar (c s d r : ℝ) (cp : 0<c) (sp : 0<s) (order : s≤c)
    (unit : c^2+s^2=1) (dp : 0<d) (rn : 0≤r) (rOrder : r≤d) :
    d*((c-1)*(c+s)+(13/50)*s*(s-c))+
      r*((c-1)*(c-s)+(13/50)*s*(c+s))<0 := by
  have bounds := CommonCases.CanonicalScalars.bounds c s cp sp.le order unit
  have cSmall := c_strict c s cp sp unit
  have first := mul_neg_of_neg_of_pos (show c-1<0 by linarith only [cSmall])
    (show 0<c+s by linarith only [cp,sp])
  have last := mul_nonpos_of_nonneg_of_nonpos sp.le
    (show s-c≤0 by linarith only [order])
  have aNegative : (c-1)*(c+s)+(13/50)*s*(s-c)<0 := by
    nlinarith only [first,last]
  have sumProduct := mul_neg_of_pos_of_neg (sub_pos.mpr cSmall)
    (show 13/25-(37/25)*c<0 by linarith only [bounds.1])
  have sumNegative : ((c-1)*(c+s)+(13/50)*s*(s-c))+
      ((c-1)*(c-s)+(13/50)*s*(c+s))<0 := by
    nlinarith only [sumProduct,unit]
  exact affine_negative d r _ _ dp rn rOrder aNegative sumNegative

theorem positive_bar (c s d r : ℝ) (cp : 0<c) (sp : 0<s) (order : s≤c)
    (unit : c^2+s^2=1) (dp : 0<d) (rn : 0≤r) (rOrder : r≤d) :
    d*((c-1)*(c-s)+(13/50)*s*(c+s)-7/20)+
      r*((c-1)*(c+s)+(13/50)*s*(s-c)+7/20)<0 := by
  have bounds := CommonCases.CanonicalScalars.bounds c s cp sp.le order unit
  have cSmall := c_strict c s cp sp unit
  have first := mul_nonpos_of_nonpos_of_nonneg
    (show c-1≤0 by linarith only [bounds.2.1]) (sub_nonneg.mpr order)
  have comparison := mul_nonneg cp.le (sub_nonneg.mpr order)
  have aNegative : (c-1)*(c-s)+(13/50)*s*(c+s)-7/20<0 := by
    nlinarith only [first,comparison,unit]
  have sumProduct := mul_neg_of_pos_of_neg (sub_pos.mpr cSmall)
    (show 13/25-(37/25)*c<0 by linarith only [bounds.1])
  have sumNegative : ((c-1)*(c-s)+(13/50)*s*(c+s)-7/20)+
      ((c-1)*(c+s)+(13/50)*s*(s-c)+7/20)<0 := by
    nlinarith only [sumProduct,unit]
  exact affine_negative d r _ _ dp rn rOrder aNegative sumNegative

theorem positive_floor (c s d r : ℝ) (cp : 0<c) (sp : 0<s) (order : s≤c)
    (unit : c^2+s^2=1) (dp : 0<d) (rn : 0≤r) (rOrder : r≤d) :
    d*(c*(13/20-c))+
      r*((1-c)*(s-1)-(13/50)*s+(7/20)*c)<0 := by
  have bounds := CommonCases.CanonicalScalars.bounds c s cp sp.le order unit
  have first := mul_neg_of_pos_of_neg cp
    (show 13/20-c<0 by linarith only [bounds.1])
  have sumNegative : c*(13/20-c)+((1-c)*(s-1)-(13/50)*s+(7/20)*c)<0 := by
    have x := x_negative c s cp sp order unit
    nlinarith only [x]
  exact affine_negative d r _ _ dp rn rOrder first sumNegative

theorem difference_order (c s d r : ℝ) (cp : 0<c) (sn : 0≤s)
    (dp : 0<d) (rn : 0≤r) (cu : c^2+s^2=1) (du : d^2+r^2=1)
    (cross : c*r-s*d≤0) : c-s≤d-r := by
  have product := mul_nonneg (show 0≤s*d-c*r by linarith only [cross])
    (add_nonneg (mul_nonneg sn dp.le) (mul_nonneg cp.le rn))
  have identity : c^2*r^2-s^2*d^2=r^2-s^2 := by
    linear_combination r^2*cu-s^2*du
  have rSmall : r≤s := by
    by_contra bad
    have high : s<r := lt_of_not_ge bad
    have square := mul_pos (sub_pos.mpr high)
      (show 0<r+s by linarith only [high,sn])
    nlinarith only [product,identity,square]
  have square := mul_nonneg (sub_nonneg.mpr rSmall) (add_nonneg sn rn)
  have cSmall : c≤d := by
    by_contra bad
    have high : d<c := lt_of_not_ge bad
    have difference := mul_pos (sub_pos.mpr high) (add_pos cp dp)
    nlinarith only [cu,du,square,difference]
  linarith only [cSmall,rSmall]

theorem projection_cap (c s : ℝ) (cp : 0<c) (sn : 0≤s) (unit : c^2+s^2=1) :
    c+(13/50)*s<517/500 := by
  have identity : (c+(13/50)*s)^2+((13/50)*c-s)^2=2669/2500 := by
    linear_combination (2669/2500)*unit
  by_contra bad
  have high : 517/500≤c+(13/50)*s := le_of_not_gt bad
  have product := mul_nonneg (sub_nonneg.mpr high)
    (show 0≤c+(13/50)*s+517/500 by linarith only [cp,sn])
  nlinarith only [identity,product,sq_nonneg ((13/50)*c-s)]

theorem short_arc (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (span : 1<c+(13/50)*s) :
    87/100<c ∧ s<49/100 := by
  have cutoff := SharpPointScalars.half_upper c s (13/50) cp sp unit span
  have cross := SharpPointScalars.half_before c s (2331/2669) (1300/2669) (13/50)
    cp sp.le unit (by norm_num) (by norm_num) (by norm_num) cutoff.le
  have upper := CommonCases.CanonicalProjection.before c s (2331/2669) (1300/2669)
    0 1 unit (by norm_num) cross (by norm_num) (by norm_num)
  have sSmall : s<49/100 := by norm_num at upper; linarith only [upper]
  have sSquare := mul_pos (sub_pos.mpr sSmall)
    (show 0<49/100+s by linarith only [sp])
  have cLarge : 87/100<c := by
    by_contra bad
    have small : c≤87/100 := le_of_not_gt bad
    have cSquare := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤87/100+c by linarith only [cp])
    nlinarith only [unit,sSquare,cSquare]
  exact ⟨cLarge,sSmall⟩

#print axioms negative_bar
#print axioms positive_bar
#print axioms positive_floor
#print axioms difference_order
end N12Compact.Completion.OtherCases.InwardSignScalars

