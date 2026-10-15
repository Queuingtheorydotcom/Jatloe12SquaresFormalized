import Compact.Completion.C1092.WallProfileScalars
import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.OutwardScalars

/-! Exact continuous projection margins for the shared sharp bar point.
Circle endpoints are rational; all comparisons follow from two dot products
or factored half-angle identities, with every limiting orientation retained. -/
namespace N12Compact.Completion.OtherCases.SharpPointScalars
open C1092WallProfileScalars
set_option Elab.async false

theorem half_strict (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c) :
    half c s < 1 := by
  unfold half
  exact (div_lt_one (by linarith only [cp])).mpr (by linarith only [order])

theorem half_upper (c s k : ℝ) (cp : 0 < c) (sp : 0 < s)
    (unit : c^2+s^2=1) (span : 1 < c+k*s) : half c s < k := by
  have data := quarter_data c s cp.le sp.le unit
  have tp : 0 < half c s := div_pos sp (by linarith only [cp])
  have scale : 0 < 1+(half c s)^2 := by nlinarith only [sq_nonneg (half c s)]
  have positive := mul_pos scale (sub_pos.mpr span)
  have identity : (1+(half c s)^2)*(c+k*s-1)=2*(half c s)*(k-half c s) := by
    calc
      _ = (1+(half c s)^2)*c+k*((1+(half c s)^2)*s)-(1+(half c s)^2) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  rw [identity] at positive
  have weight : 0 < 2*half c s := by linarith only [tp]
  have gap := (mul_pos_iff_of_pos_left weight).mp positive
  linarith only [gap]

theorem half_lower (c s a : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (span : 1 < a*c+s) : (1-a) < (1+a)*half c s := by
  have data := quarter_data c s cp.le sn unit
  have tu := half_strict c s cp sn order
  have scale : 0 < 1+(half c s)^2 := by nlinarith only [sq_nonneg (half c s)]
  have positive := mul_pos scale (sub_pos.mpr span)
  have identity : (1+(half c s)^2)*(a*c+s-1)=
      (1-half c s)*((1+a)*half c s-(1-a)) := by
    calc
      _ = a*((1+(half c s)^2)*c)+(1+(half c s)^2)*s-(1+(half c s)^2) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  rw [identity] at positive
  have gap := (mul_pos_iff_of_pos_left (sub_pos.mpr tu)).mp positive
  linarith only [gap]

private theorem cross_identity (c s c0 s0 k : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1)
    (cform : (1+k^2)*c0=1-k^2) (sform : (1+k^2)*s0=2*k) :
    (1+(half c s)^2)*(1+k^2)*(s0*c-c0*s)=
      2*(k-half c s)*(1+k*half c s) := by
  have data := quarter_data c s cp.le sn unit
  calc
    _ = ((1+k^2)*s0)*((1+(half c s)^2)*c)-
        ((1+k^2)*c0)*((1+(half c s)^2)*s) := by ring
    _ = _ := by rw [cform,sform,data.2.2.2.1,data.2.2.2.2]; ring

theorem half_before (c s c0 s0 k : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (kn : 0 ≤ k)
    (cform : (1+k^2)*c0=1-k^2) (sform : (1+k^2)*s0=2*k)
    (bound : half c s ≤ k) : c0*s ≤ s0*c := by
  have data := quarter_data c s cp.le sn unit
  have last : 0 ≤ 1+k*half c s := by
    have product := mul_nonneg kn data.1
    linarith only [product]
  have positive := mul_nonneg (show 0 ≤ 2*(k-half c s) by linarith only [bound]) last
  have identity := cross_identity c s c0 s0 k cp sn unit cform sform
  have scaled : 0 ≤ (1+(half c s)^2)*(1+k^2)*(s0*c-c0*s) := by
    rwa [identity]
  have scale : 0 < (1+(half c s)^2)*(1+k^2) :=
    mul_pos (by nlinarith only [sq_nonneg (half c s)]) (by nlinarith only [sq_nonneg k])
  have gap := nonneg_of_mul_nonneg_right scaled scale
  linarith only [gap]

theorem half_after (c s c0 s0 k : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (kn : 0 ≤ k)
    (cform : (1+k^2)*c0=1-k^2) (sform : (1+k^2)*s0=2*k)
    (bound : k ≤ half c s) : s0*c ≤ c0*s := by
  have data := quarter_data c s cp.le sn unit
  have last : 0 ≤ 1+k*half c s := by
    have product := mul_nonneg kn data.1
    linarith only [product]
  have negative := mul_nonpos_of_nonpos_of_nonneg
    (show 2*(k-half c s) ≤ 0 by linarith only [bound]) last
  have identity := cross_identity c s c0 s0 k cp sn unit cform sform
  have scaled : 0 ≤ (1+(half c s)^2)*(1+k^2)*(c0*s-s0*c) := by
    rw [show (1+(half c s)^2)*(1+k^2)*(c0*s-s0*c)=
      -((1+(half c s)^2)*(1+k^2)*(s0*c-c0*s)) by ring,identity]
    exact neg_nonneg.mpr negative
  have scale : 0 < (1+(half c s)^2)*(1+k^2) :=
    mul_pos (by nlinarith only [sq_nonneg (half c s)]) (by nlinarith only [sq_nonneg k])
  have gap := nonneg_of_mul_nonneg_right scaled scale
  linarith only [gap]

/-- A uniform strict arc margin for either of the two vertex crossings. -/
theorem arc (c s : ℝ) (cp : 0 < c) (sp : 0 < s) (unit : c^2+s^2=1) :
    1+(413/500)*c*s < c+s := by
  have cross := mul_pos cp sp
  have low : 1 ≤ c+s := by nlinarith only [unit,cross,cp,sp]
  have high : c+s ≤ 99/70 := by nlinarith only [unit,sq_nonneg (c-s),cp,sp]
  have remainder := mul_nonneg (sub_nonneg.mpr high) (sub_nonneg.mpr low)
  nlinarith only [remainder,unit,cross]

theorem outward_short_u (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (unit : c^2+s^2=1) (span : 1 < c+(143/500)*s) :
    (27/50)*c+s < 1 := by
  have bound := half_upper c s (143/500) cp sp unit span
  have cross := half_before c s (229551/270449) (143000/270449) (143/500)
    cp sp.le unit (by norm_num) (by norm_num) (by norm_num) bound.le
  have projection := CommonCases.CanonicalProjection.before c s
    (229551/270449) (143000/270449) (27/50) 1 unit
    (by norm_num) cross (by norm_num) (by norm_num)
  linarith only [projection]

theorem outward_lower_u (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (unit : c^2+s^2=1) (span : 1 < c+(143/500)*s) :
    (19/40)*c+(9/8)*s < 1 := by
  have bound := half_upper c s (143/500) cp sp unit span
  have cross := half_before c s (229551/270449) (143000/270449) (143/500)
    cp sp.le unit (by norm_num) (by norm_num) (by norm_num) bound.le
  have projection := CommonCases.CanonicalProjection.before c s
    (229551/270449) (143000/270449) (19/40) (9/8) unit
    (by norm_num) cross (by norm_num) (by norm_num)
  linarith only [projection]

theorem outward_lower_v (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (span : 1 < (37/50)*c+s) :
    (9/8)*c-(11/40)*s < 1 := by
  have bound := half_lower c s (37/50) cp sn order unit span
  have cutoff : 13/87 ≤ half c s := by linarith only [bound]
  have cross := half_after c s (3700/3869) (1131/3869) (13/87)
    cp sn unit (by norm_num) (by norm_num) (by norm_num) cutoff
  have projection := CommonCases.CanonicalProjection.after c s
    (3700/3869) (1131/3869) (9/8) (-11/40) unit
    (by norm_num) cross (by norm_num) (by norm_num)
  linarith only [projection]

theorem upper_lower_v (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (span : 1 < (11/25)*c+s) :
    (7/8)*c+(21/40)*s < 1 := by
  have bound := half_lower c s (11/25) cp sn order unit span
  have cutoff : 7/18 ≤ half c s := by linarith only [bound]
  have cross := half_after c s (275/373) (252/373) (7/18)
    cp sn unit (by norm_num) (by norm_num) (by norm_num) cutoff
  have projection := CommonCases.CanonicalProjection.after c s
    (275/373) (252/373) (7/8) (21/40) unit
    (by norm_num) cross (by norm_num) (by norm_num)
  linarith only [projection]

#print axioms outward_lower_u
#print axioms upper_lower_v
end N12Compact.Completion.OtherCases.SharpPointScalars

