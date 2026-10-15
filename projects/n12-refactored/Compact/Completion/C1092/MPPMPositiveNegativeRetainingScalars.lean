import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfileScalars

/-! Exact scalar part of POSITIVE-NEGATIVE-RETAINING-SHALLOW.
The final sharpening uses a rational quadratic difference on [.23,.38],
in place of differentiation or an irrational endpoint. Source only. -/
namespace N12Compact.C1092MPPMPositiveNegativeRetaining.Scalars
open C977CornerCubic C1092MPPMNonpositivePredecessor
set_option Elab.async false
noncomputable section

def P (d t : ℝ) : ℝ := 1-t+(13/50)*d*t+t^2/2
def Q (d t : ℝ) : ℝ := 1-d+d*t/2-(13/50)*t^2

theorem first_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (tp : 0<t) : 0<1-P d t*c-Q d t*s := by
  have eb := normal_bounds en
  have es := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds en
  have dp : 0<d := es.1
  have th : t<71/100 := es.2.2.2.1
  have pn : 0≤P d t := by
    dsimp [P]
    nlinarith only [th,mul_nonneg dp.le tp.le,sq_nonneg t]
  have qn : 0≤Q d t := by
    have product := mul_nonneg tp.le
      (show 0≤d/2-(13/50)*t by linarith only [en.2.1,tp])
    dsimp [Q]
    nlinarith only [product,eb.2.1]
  have pu : P d t≤1-(19/50)*t := by
    have product := mul_nonneg tp.le
      (show 0≤31/50-(13/50)*d-t/2 by linarith only [eb.2.1,th])
    dsimp [P]
    nlinarith only [product]
  have half : 1-d≤(21/50)*t := by
    have product := mul_nonneg tp.le
      (show 0≤(21/50)*(1+d)-t by linarith only [eb.1,th])
    have scaled : 0≤(1+d)*((21/50)*t-(1-d)) := by
      nlinarith only [product,en.2.2]
    have result := nonneg_of_mul_nonneg_right scaled
      (show 0<1+d by linarith only [dp])
    linarith only [result]
  have qu : Q d t≤(23/25)*t := by
    have product := mul_nonneg tp.le (show 0≤1-d by linarith only [eb.2.1])
    dsimp [Q]
    nlinarith only [half,product,sq_nonneg t]
  have pcap : 0≤1-(19/50)*t := by linarith only [th]
  have qcap : 0≤(23/25)*t := by positivity
  have p2 := mul_nonneg (sub_nonneg.mpr pu) (add_nonneg pcap pn)
  have q2 := mul_nonneg (sub_nonneg.mpr qu) (add_nonneg qcap qn)
  have gap := mul_pos tp
    (show 0<19/25-(2477/2500)*t by linarith only [th])
  have norm : (P d t)^2+(Q d t)^2<1^2 := by
    nlinarith only [p2,q2,gap]
  have bound := norm_lt (P d t) (Q d t) c s 1 cn.2.2 (by norm_num) norm
  linarith only [bound]

theorem transverse_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (kn : 0≤c*d-s*t) (ell : c*t+s*d≤1) :
    0<1-s+(c*d-s*t)*(1-d)-(13/50)*(c*t+s*d)*t := by
  have cs := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds cn
  have es := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds en
  have product := mul_nonneg kn (show 0≤1-d by linarith only [es.2.1])
  have weighted := mul_le_mul_of_nonneg_right ell en.1
  nlinarith only [product,weighted,cs.2.2.2.1,es.2.2.2.1]

theorem envelope {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    d*(1+c*s-c-s)-t*(c-s+s^2)<(43/500)*d-t/2 := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have estimates := C1092MPPMSteepPositiveNegativeProfile.Scalars.envelope cn
  have first := mul_lt_mul_of_pos_left estimates.1 dp
  have second := mul_le_mul_of_nonneg_left estimates.2 en.1
  dsimp [C1092MPPMSteepPositiveNegativeProfile.Scalars.f,
    C1092MPPMSteepPositiveNegativeProfile.Scalars.B] at first second
  linarith only [first,second]

theorem preliminary {d t H : ℝ} (en : Normal d t)
    (forward : -(13/50)*t<H) (height : H<(43/500)*d-t/2) :
    t<(2/5)*d ∧ 23/25<d ∧ t<19/50 := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have slope : t<(2/5)*d := by linarith only [forward,height,dp]
  have square := mul_pos (sub_pos.mpr slope)
    (show 0<(2/5)*d+t by linarith only [dp,en.1])
  have dl : 23/25<d := by
    by_contra no
    have bad := mul_nonneg (show 0≤23/25-d by linarith only [no])
      (show 0≤23/25+d by linarith only [dp])
    nlinarith only [square,en.2.2,bad]
  have th : t<19/50 := by
    by_contra no
    have bad := mul_nonneg (show 0≤t-19/50 by linarith only [no])
      (show 0≤t+19/50 by linarith only [en.1])
    nlinarith only [square,en.2.2,bad]
  exact ⟨slope,dl,th⟩

/-- The two strict simultaneous bounds on the same H force the sharper
angle. No independently selected wall position enters this inequality. -/
theorem sharpen {d t H : ℝ} (en : Normal d t) (tp : 0<t)
    (dl : 23/25<d) (th : t<19/50)
    (upper : H<(43/500)*d-t/2)
    (lower : d+t-1-d*t<d*H) :
    4*t<d ∧ H<43/500 ∧ 97/100<d ∧ t<1/4 := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [dl]
  have slope : 4*t<d := by
    by_contra no
    have tl : 23/100<t := by linarith only [no,dl]
    have radial := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
      (show 0≤(21/40)*(1+d)-1 by linarith only [dl])
    have chord : 1-(21/40)*t^2≤d := by nlinarith only [radial,en.2.2]
    have weighted := mul_nonneg (sub_nonneg.mpr chord)
      (show 0≤1-t/2 by linarith only [th])
    have increasing := mul_nonneg (show 0≤t-23/100 by linarith only [tl])
      (show 0≤1/2-(439/1000)*(t+23/100) by linarith only [th])
    have cube := mul_nonneg tp.le (sq_nonneg t)
    have obstruction : 0<d+t-1-d*t/2-(43/500)*d^2 := by
      nlinarith only [weighted,increasing,cube,en.2.2]
    have cap := mul_lt_mul_of_pos_left upper dp
    nlinarith only [obstruction,cap,lower]
  have hh : H<43/500 := by linarith only [upper,eb.2.1,tp]
  have square := mul_pos (show 0<d-4*t by linarith only [slope])
    (show 0<d+4*t by linarith only [dp,tp])
  have cosine : 97/100<d := by
    by_contra no
    have bad := mul_nonneg (show 0≤97/100-d by linarith only [no])
      (show 0≤97/100+d by linarith only [dp])
    nlinarith only [square,en.2.2,bad]
  exact ⟨slope,hh,cosine,by linarith only [slope,eb.2.1]⟩

end
end N12Compact.C1092MPPMPositiveNegativeRetaining.Scalars
