import Compact.Completion.C1092.WallProfileScalars
import Compact.Completion.CommonCases.CanonicalScalars

/-! Exact quartic margin for the shorter actual corner reach. The whole
canonical interval follows from two positive polynomial factorizations. -/
namespace N12Compact.Completion.OtherCases.ShorterCornerScalars
open C1092WallProfileScalars
set_option Elab.async false

private theorem polynomial (t : ℝ) (tn : 0≤t) (tu : t≤1/2) :
    0<1-58*t^2+200*t^3-99*t^4 := by
  by_cases small : t≤3/10
  · have cube : 0≤t^3 := pow_nonneg tn 3
    have remainder := mul_nonneg cube (show 0≤200-99*t-1703/10 by
      linarith only [small])
    have factor := mul_nonneg (sq_nonneg (t-1160/5109))
      (show 0≤t+(1160/5109)/2 by linarith only [tn])
    have identity : 1-58*t^2+(1703/10)*t^3 =
        260843/78305643+(1703/10)*(t-1160/5109)^2*(t+(1160/5109)/2) := by ring
    nlinarith only [identity,factor,remainder]
  · have dn : 0≤t-3/10 := by linarith only [small]
    have cube : 0≤(t-3/10)^3 := pow_nonneg dn 3
    have remainder := mul_nonneg cube
      (show 0≤406/5-99*(t-3/10) by linarith only [tu])
    have square := sq_nonneg (t-3/10)
    have identity : 1-58*t^2+200*t^3-99*t^4 =
        3781/10000+(2127/250)*(t-3/10)+(3427/50)*(t-3/10)^2+
          (t-3/10)^3*(406/5-99*(t-3/10)) := by ring
    linarith only [identity,dn,square,remainder]

theorem margin (c s : ℝ) (cp : 0<c) (sn : 0≤s) (order : s≤c)
    (unit : c^2+s^2=1) :
    0<c+s-1-c*s+(1/50)*c^2+(11/50)*s^2 := by
  let t := half c s
  have data := quarter_data c s cp.le sn unit
  have tn : 0≤t := data.1
  have cu := (CommonCases.CanonicalScalars.bounds c s cp sn order unit).2.1
  have tu : t≤1/2 := by
    dsimp only [t,half]
    apply (div_le_iff₀ (by linarith only [cp] : 0<1+c)).mpr
    linarith only [order,cu]
  have positive := polynomial t tn tu
  have cForm : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sForm : (1+t^2)*s=2*t := data.2.2.2.2
  have identity : 50*(1+t^2)^2*(c+s-1-c*s+(1/50)*c^2+(11/50)*s^2) =
      1-58*t^2+200*t^3-99*t^4 := by
    calc
      _ = 50*((1+t^2)*((1+t^2)*c)+(1+t^2)*((1+t^2)*s)-(1+t^2)^2-
          ((1+t^2)*c)*((1+t^2)*s))+
          ((1+t^2)*c)^2+11*((1+t^2)*s)^2 := by ring
      _ = _ := rw [cForm,sForm]; ring
  have scaled : 0<50*(1+t^2)^2*(c+s-1-c*s+(1/50)*c^2+(11/50)*s^2) := by
    rwa [identity]
  have scale : 0<50*(1+t^2)^2 :=
    mul_pos (by norm_num) (pow_pos (by nlinarith only [sq_nonneg t]) 2)
  exact (mul_pos_iff_of_pos_left scale).mp scaled

#print axioms margin
end N12Compact.Completion.OtherCases.ShorterCornerScalars

