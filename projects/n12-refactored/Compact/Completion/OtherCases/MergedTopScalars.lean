import Compact.Completion.CommonCases.CanonicalScalars

/-! Exact one-angle margins in the merged-top obstruction. The side cap
forces a whole steep arc; factored polynomial differences replace derivatives. -/
namespace N12Compact.Completion.OtherCases.MergedTopScalars
set_option Elab.async false

theorem steep_data (c t : ℝ) (cp : 0<c) (tn : 0≤t) (order : t≤c)
    (unit : c^2+t^2=1) (span : (27/20)*c-(1/20)*t<1001/1000) :
    5*c<6*t ∧ 16/25<t ∧ t<5/7 ∧ 7/10<c ∧ c≤1 := by
  have bounds := CommonCases.CanonicalScalars.bounds c t cp tn order unit
  have steep : 5*c<6*t := by
    by_contra failed
    have low : 6*t≤5*c := le_of_not_gt failed
    have square := mul_nonneg (sub_nonneg.mpr low)
      (show 0≤5*c+6*t by linarith only [cp,tn])
    have cLower : 96/125<c := by
      by_contra bad
      have high : c≤96/125 := le_of_not_gt bad
      have cSquare := mul_nonneg (sub_nonneg.mpr high)
        (show 0≤96/125+c by linarith only [cp])
      nlinarith only [square,cSquare,unit]
    linarith only [span,cLower,low]
  have tp : 0<t := by linarith only [steep,cp]
  have ratioSquare := mul_pos (show 0<6*t-5*c by linarith only [steep])
    (show 0<6*t+5*c by linarith only [cp,tp])
  have lower : 16/25<t := by
    by_contra bad
    have high : t≤16/25 := le_of_not_gt bad
    have tSquare := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤16/25+t by linarith only [tn])
    nlinarith only [ratioSquare,tSquare,unit]
  have difference := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤c+t by linarith only [cp,tn])
  have upper : t<5/7 := by
    by_contra bad
    have high : 5/7≤t := le_of_not_gt bad
    have tSquare := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤t+5/7 by linarith only [tn])
    nlinarith only [difference,tSquare,unit]
  exact ⟨steep,lower,upper,bounds.1,bounds.2.1⟩

theorem u_margin (c t : ℝ) (cp : 7/10<c) (cu : c≤1)
    (tl : 16/25≤t) (tu : t≤5/7) (unit : c^2+t^2=1) :
    0<c-27/20+(7/10)*t*(c+t) := by
  have tn : 0≤t := by linarith only [tl]
  have defectProduct := mul_nonneg (sub_nonneg.mpr cu)
    (show 0≤(3/5)*(1+c)-1 by linarith only [cp])
  have defect : 1-(3/5)*t^2≤c := by nlinarith only [defectProduct,unit]
  have tSquareProduct := mul_nonneg (sub_nonneg.mpr tu)
    (show 0≤5/7+t by linarith only [tn])
  have tSquare : t^2≤25/49 := by nlinarith only [tSquareProduct]
  have bracket : 0≤7/10+(1/10)*(t+16/25)-
      (21/50)*(t^2+(16/25)*t+(16/25)^2) := by
    nlinarith only [tSquare,tu,tn]
  have remainder := mul_nonneg (sub_nonneg.mpr tl) bracket
  have identity : -7/20+(7/10)*t+(1/10)*t^2-(21/50)*t^3 =
      (-7/20+(7/10)*(16/25)+(1/10)*(16/25)^2-(21/50)*(16/25)^3)+
      (t-16/25)*(7/10+(1/10)*(t+16/25)-
        (21/50)*(t^2+(16/25)*t+(16/25)^2)) := by ring
  have polynomial : 0< -7/20+(7/10)*t+(1/10)*t^2-(21/50)*t^3 := by
    linarith only [identity,remainder]
  have weight := mul_nonneg (sub_nonneg.mpr defect)
    (show 0≤1+(7/10)*t by linarith only [tn])
  nlinarith only [weight,polynomial]

theorem v_margin (c t : ℝ) (cp : 7/10<c)
    (tl : 16/25≤t) (tu : t≤5/7) :
    0<t-3/5-(3/4)*t^2+(13/20)*c*t := by
  have tn : 0<t := by linarith only [tl]
  have bracket : 0≤291/200-(3/4)*(t+16/25) := by linarith only [tu]
  have remainder := mul_nonneg (sub_nonneg.mpr tl) bracket
  have identity : (291/200)*t-(3/4)*t^2-3/5 =
      3/125+(t-16/25)*(291/200-(3/4)*(t+16/25)) := by ring
  have polynomial : 0<(291/200)*t-(3/4)*t^2-3/5 := by
    linarith only [identity,remainder]
  have strict := mul_pos (show 0<(13/20)*t by linarith only [tn])
    (show 0<c-7/10 by linarith only [cp])
  nlinarith only [polynomial,strict]

#print axioms steep_data
#print axioms u_margin
#print axioms v_margin
end N12Compact.Completion.OtherCases.MergedTopScalars

