import Compact.Completion.OtherCases.C976MergedLeft.Inputs
import Compact.Completion.CommonCases.BernsteinQuartic

/-! Exact full-interval certificates from C976-MERGED-LEFT-ENDING
sections 3--5. All decimal constants in the chapter are rational here. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open C1092WallProfileScalars
set_option Elab.async false

theorem small_corner_margin (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (order : s≤c) (unit : c^2+s^2=1) (small : s≤(38/65)*c) :
    1<c+(3/20)*c*s+(7/20)*s^2 := by
  have data := quarter_data c s cp.le sp.le unit
  have cu := (CommonCases.CanonicalScalars.bounds c s cp sp.le order unit).2.1
  let t := half c s
  have tp : 0<t := div_pos sp (by linarith only [cp])
  have relation : t*(1+c)=s := data.2.2.1
  have tu : t≤8/25 := by
    apply le_of_not_gt
    intro large
    have product := mul_pos (sub_pos.mpr large) (show 0<1+c by linarith only [cp])
    nlinarith only [product,relation,small,cu]
  have polynomial : 0<3-6*t-3*t^2-20*t^3 := by
    have product := mul_nonneg (sub_nonneg.mpr tu)
      (show 0≤6+3*(8/25+t)+20*((8/25)^2+(8/25)*t+t^2) by positivity)
    have identity : 3-6*t-3*t^2-20*t^3=
        367/3125+(8/25-t)*(6+3*(8/25+t)+20*((8/25)^2+(8/25)*t+t^2)) := by ring
    linarith only [identity,product]
  have den : 1+t^2≠0 := ne_of_gt (by positivity)
  have cf : c=(1-t^2)/(1+t^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*t/(1+t^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.2])
  have identity : 10*(1+t^2)^2*(c+(3/20)*c*s+(7/20)*s^2-1)=
      t*(3-6*t-3*t^2-20*t^3) := by
    rw [cf,sf]
    field_simp [den] <;> ring
  have scaled : 0<10*(1+t^2)^2*(c+(3/20)*c*s+(7/20)*s^2-1) := by
    rw [identity]
    exact mul_pos tp polynomial
  have result := (mul_pos_iff_of_pos_left (show 0<10*(1+t^2)^2 by positivity)).mp scaled
  linarith only [result]

theorem top_span (c s : ℝ) (unit : c^2+s^2=1) (slope : (38/65)*c≤s) :
    c+(23/100)*s<1 := by
  have comparison : c+(23/100)*s≤(3687/283450)*(65*c+38*s) := by
    linarith only [slope]
  have identity : (65*c+38*s)^2+(38*c-65*s)^2=5669 := by
    nlinarith only [unit]
  have norm : (65*c+38*s)^2≤5669 := by
    nlinarith only [identity,sq_nonneg (38*c-65*s)]
  have weighted := mul_le_mul_of_nonneg_left norm (show 0≤(3687/283450:ℝ)^2 by positivity)
  have bound : (3687/283450)*(65*c+38*s)<1 := by
    nlinarith only [weighted,sq_nonneg ((3687/283450)*(65*c+38*s)-1)]
  exact lt_of_le_of_lt comparison bound

theorem cosine_small (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (slope : (38/65)*c<s) : c<7/8 := by
  have product := mul_pos (show 0<65*s-38*c by linarith only [slope])
    (show 0<65*s+38*c by linarith only [cp,sn])
  nlinarith only [product,unit,cp]

theorem half_small_of_cosine (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (large : 50/63<c) : half c s<17/50 := by
  have data := quarter_data c s cp.le sn unit
  have identity : (1+c)*(half c s)^2=1-c := by nlinarith only [data.2.2.2.1]
  have bound : (half c s)^2<13/113 := by
    have product := mul_nonneg (sq_nonneg (half c s)) (show 0≤c-50/63 by linarith only [large])
    nlinarith only [identity,large,product]
  nlinarith only [bound,data.1]

theorem lower_corner_margin (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (small : half c s≤17/50) :
    0<(37/100)*c+(11/100)*s-27/80+(351/10000)*s^2-(81/1250)*c*s := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have tn : 0≤t := data.1
  have tu : t≤17/50 := small
  have certificate := CommonCases.BernsteinQuartic.positive ((50/17)*t)
    (13/400) (5023/125000) (939201/25000000)
    (4388639/156250000) (14305853/2500000000)
    (by positivity) (by linarith only [tu])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have polynomial : 0<(325+904*t-5346*t^2+3496*t^3-7075*t^4)/10000 := by
    have identity : CommonCases.BernsteinQuartic.value ((50/17)*t)
        (13/400) (5023/125000) (939201/25000000)
        (4388639/156250000) (14305853/2500000000)=
        (325+904*t-5346*t^2+3496*t^3-7075*t^4)/10000 := by
      dsimp only [CommonCases.BernsteinQuartic.value]
      ring
    simpa only [identity] using certificate
  have den : 1+t^2≠0 := ne_of_gt (by positivity)
  have cf : c=(1-t^2)/(1+t^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*t/(1+t^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.2])
  have identity : (1+t^2)^2*((37/100)*c+(11/100)*s-27/80+
      (351/10000)*s^2-(81/1250)*c*s)=
      (325+904*t-5346*t^2+3496*t^3-7075*t^4)/10000 := by
    rw [cf,sf]
    field_simp [den] <;> ring
  have scaled : 0<(1+t^2)^2*((37/100)*c+(11/100)*s-27/80+
      (351/10000)*s^2-(81/1250)*c*s) := by rw [identity]; exact polynomial
  exact (mul_pos_iff_of_pos_left (show 0<(1+t^2)^2 by positivity)).mp scaled

theorem early_span (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (small : half c s≤7/20) : (27/100)*c+(63/50)*s<1 := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have product := mul_nonneg (show 0≤7-20*t by linarith only [small])
    (show 0≤40+14*t by have hn : 0≤t := data.1; positivity)
  have identity : (1+t^2)*(280*c-351*s)=(7-20*t)*(40+14*t) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have cross : 351*s≤280*c := by
    have result : 0≤(1+t^2)*(280*c-351*s) := by rw [identity]; exact product
    have nonneg := (mul_nonneg_iff_of_pos_left (show 0<1+t^2 by positivity)).mp result
    linarith only [nonneg]
  have bound := CommonCases.CanonicalProjection.before c s (351/449) (280/449)
    (27/100) (63/50) unit (by norm_num) (by linarith only [cross])
    (by norm_num) (by norm_num)
  linarith only [bound]

theorem target_span (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (large : 7/20≤half c s) : (26/25)*c+(27/100)*s<1 := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have product := mul_nonneg (show 0≤20*t-7 by linarith only [large])
    (show 0≤40+14*t by have hn : 0≤t := data.1; positivity)
  have identity : (1+t^2)*(351*s-280*c)=(20*t-7)*(40+14*t) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have cross : 280*c≤351*s := by
    have result : 0≤(1+t^2)*(351*s-280*c) := by rw [identity]; exact product
    have nonneg := (mul_nonneg_iff_of_pos_left (show 0<1+t^2 by positivity)).mp result
    linarith only [nonneg]
  have bound := CommonCases.CanonicalProjection.after c s (351/449) (280/449)
    (26/25) (27/100) unit (by norm_num) (by linarith only [cross])
    (by norm_num) (by norm_num)
  linarith only [bound]

end N12Compact.Completion.OtherCases.C976MergedLeft
