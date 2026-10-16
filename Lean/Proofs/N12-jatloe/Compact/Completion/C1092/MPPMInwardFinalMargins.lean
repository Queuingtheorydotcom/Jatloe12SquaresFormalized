import Compact.Completion.C1092.MPPMInwardFinalEndpoints

/-! Full continuous successor margins, obtained from the printed exact
rational endpoints and the proved chord monotonicity. Both beta values
and the missing-center zero-height alternative are retained. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars CommonCases.CanonicalProjection
set_option Elab.async false

private theorem first_normal : Normal (95727000/103958161) (40541839/103958161) := by
  norm_num [Normal]

private theorem last_normal : Normal (4165/4813) (2412/4813) := by
  norm_num [Normal]

theorem small_tenth {c s : ℝ} (cn : Normal c s) (small : half c s≤1/10) :
    49/50<c ∧ s<1/5 := by
  have endpoint : Normal (99/101) (20/101) := by norm_num [Normal]
  have endpointHalf : half (99/101) (20/101)=(1:ℝ)/10 := by norm_num [half]
  have cross := half_cross cn endpoint
    (by simpa only [endpointHalf] using small)
  have coordinates := coordinates_after endpoint cn cross
  constructor <;> nlinarith only [coordinates.1,coordinates.2]

theorem centered_half_margins {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (close : 49/50<c) (small : s<9/50) (halfSmall : half c s≤91/1000)
    (height : 0≤c/11-s/2)
    (cross : (40541839/103958161)*d≤(95727000/103958161)*t) :
    0<FC (1/2) c s d t ∧ 0<FE (1/2) (c/11-s/2) c s d t := by
  have cb := normal_bounds cn
  have coefficients := coefficients_after (1/2) dn first_normal cross
  have p : P d t<9/10 := by
    have endpoint : P (95727000/103958161) (40541839/103958161)<9/10 := by norm_num [P]
    exact lt_of_le_of_lt coefficients.1 endpoint
  have q : Q (1/2) d t<11/20 := by
    have endpoint : Q (1/2) (95727000/103958161) (40541839/103958161)<11/20 := by norm_num [Q]
    exact lt_of_le_of_lt coefficients.2 endpoint
  have first := mul_lt_mul_of_pos_left p (by linarith only [cb.1] : 0<c)
  have last := mul_le_mul_of_nonneg_left q.le cn.1
  have FCpos : 0<FC (1/2) c s d t := by
    rw [FC_formula _ _ _ _ _ dn.2.2]
    nlinarith only [first,last,cb.2.1,small]
  have comparison := FE_after cn dn first_normal close.le
    (by linarith only [small]) (by norm_num : (0:ℝ)≤1/2) le_rfl height
    (show c/11-s/2≤1/10 by linarith only [cb.2.1,cn.1])
    (by norm_num) (by norm_num) cross
  exact ⟨FCpos,lt_of_lt_of_le (centered_half_endpoint cn halfSmall) comparison⟩

theorem centered_final_margins {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (close : 49/50<c) (small : s<9/50) (halfSmall : half c s≤91/1000)
    (height : 0≤c/11-s/2) (cross : (2412/4813)*d≤(4165/4813)*t) :
    0<FC (13/50) c s d t ∧ 0<FE (13/50) (c/11-s/2) c s d t := by
  have cb := normal_bounds cn
  have coefficients := coefficients_after (13/50) dn last_normal cross
  have p : P d t<177/200 := by
    have endpoint : P (4165/4813) (2412/4813)<177/200 := by norm_num [P]
    exact lt_of_le_of_lt coefficients.1 endpoint
  have q : Q (13/50) d t<17/25 := by
    have endpoint : Q (13/50) (4165/4813) (2412/4813)<17/25 := by norm_num [Q]
    exact lt_of_le_of_lt coefficients.2 endpoint
  have first := mul_lt_mul_of_pos_left p (by linarith only [cb.1] : 0<c)
  have last := mul_le_mul_of_nonneg_left q.le cn.1
  have deficit : c≤1-s^2/2 := by nlinarith only [cn.2.2,sq_nonneg (1-c)]
  have endpoint := mul_nonneg (show 0≤9/50-s by linarith only [small])
    (show 0≤17/25-(177/400)*(s+9/50) by linarith only [small,cn.1])
  have FCpos : 0<FC (13/50) c s d t := by
    rw [FC_formula _ _ _ _ _ dn.2.2]
    nlinarith only [first,last,deficit,endpoint]
  have comparison := FE_after cn dn last_normal close.le
    (by linarith only [small]) (by norm_num : (0:ℝ)≤13/50) (by norm_num) height
    (show c/11-s/2≤1/10 by linarith only [cb.2.1,cn.1])
    (by norm_num) (by norm_num) cross
  exact ⟨FCpos,lt_of_lt_of_le (centered_final_endpoint cn halfSmall) comparison⟩

theorem missing_final_margins {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (small : half c s≤1/10) (cross : (2412/4813)*d≤(4165/4813)*t) :
    0<FC (13/50) c s d t ∧ 0<FE (13/50) 0 c s d t := by
  have cb := normal_bounds cn
  have coordinates := small_tenth cn small
  have endpoint : Normal (99/101) (20/101) := by norm_num [Normal]
  have endpointHalf : half (99/101) (20/101)=(1:ℝ)/10 := by norm_num [half]
  have pOrder := half_cross cn endpoint (by simpa only [endpointHalf] using small)
  have projection := before c s (99/101) (20/101)
    (P (4165/4813) (2412/4813)) (Q (13/50) (4165/4813) (2412/4813))
    cn.2.2 endpoint.2.2 (by nlinarith only [pOrder]) (by norm_num [P,Q]) (by norm_num [P,Q])
  have value : 0<FC (13/50) c s (4165/4813) (2412/4813) := by
    rw [FC_formula _ _ _ _ _ last_normal.2.2]
    have exactEndpoint :
        P (4165/4813) (2412/4813)*(99/101)+
          Q (13/50) (4165/4813) (2412/4813)*(20/101)<1 := by norm_num [P,Q]
    nlinarith only [projection,exactEndpoint]
  have first := FC_after (13/50) cn dn last_normal cross
  have last := FE_after cn dn last_normal coordinates.1.le coordinates.2.le
    (by norm_num : (0:ℝ)≤13/50) (by norm_num) (by norm_num : (0:ℝ)≤0)
    (by norm_num) (by norm_num) (by norm_num) cross
  exact ⟨lt_of_lt_of_le value first,lt_of_lt_of_le (missing_final_endpoint cn small) last⟩

#print axioms centered_half_margins
#print axioms centered_final_margins
#print axioms missing_final_margins
end N12Compact.C1092MPPMInwardFinal
