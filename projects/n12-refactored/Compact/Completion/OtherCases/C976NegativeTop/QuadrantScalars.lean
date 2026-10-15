import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.Positivity

/-! Exact quadrant estimates from sections 2 and 4 of the C976 negative
northeast/top ending. These do not impose a canonical ordering on C,S. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
set_option Elab.async false

theorem quadrant_bounds (C S : ℝ) (Cp : 0<C) (Sn : 0≤S)
    (unit : C^2+S^2=1) (ratio : (2/3)*S≤C) :
    11/20<C ∧ S<5/6 ∧ C≤1 ∧ 1≤C+S ∧
      1+(4/5)*C*S≤C+S := by
  have cross := mul_nonneg (show 0≤C-(2/3)*S by linarith only [ratio])
    (show 0≤C+(2/3)*S by linarith only [Cp,Sn])
  have cBound : 11/20<C := by nlinarith only [unit,cross,Cp,Sn]
  have sBound : S<5/6 := by nlinarith only [unit,cross,Sn]
  have cUpper : C≤1 := by nlinarith only [unit,sq_nonneg S,Cp]
  have product := mul_nonneg Cp.le Sn
  have sumLower : 1≤C+S := by nlinarith only [unit,product,Cp,Sn]
  have sumUpper : C+S≤3/2 := by nlinarith only [unit,sq_nonneg (C-S),Cp,Sn]
  have gap := mul_nonneg (sub_nonneg.mpr sumUpper) (sub_nonneg.mpr sumLower)
  exact ⟨cBound,sBound,cUpper,sumLower,by nlinarith only [gap,unit]⟩

/-- The affine estimate (9), without division by the northeast cosine. -/
theorem lower_exit_margin (c s C S : ℝ) (cp : 0<c) (sn : 0≤s)
    (Cp : 0<C) (Sn : 0≤S) (unit : C^2+S^2=1) (ratio : (2/3)*S≤C) :
    min ((13/50)*c) ((37/50)*s)≤(c*S+s*C)*(1-(3/4)*S) := by
  have bounds := quadrant_bounds C S Cp Sn unit ratio
  have weight : 0<1-(3/4)*S := by linarith only [bounds.2.1]
  have product := mul_nonneg Sn
    (show 0≤15/8-(9/4)*S by linarith only [bounds.2.1])
  have cross := mul_nonneg Cp.le Sn
  have base : (1/3)≤(S+C/3)*(1-(3/4)*S) := by
    nlinarith only [bounds.2.2.2.2,product,cross,Sn]
  have increase := mul_nonneg (show 0≤(13/37-1/3)*C by positivity) weight.le
  have star : 1/3≤(S+(13/37)*C)*(1-(3/4)*S) := by
    nlinarith only [base,increase]
  by_cases low : s≤(13/37)*c
  · rw [min_eq_right (by linarith only [low])]
    by_cases slope : 0≤C*(1-(3/4)*S)-37/50
    · have first := mul_nonneg (mul_nonneg cp.le Sn) weight.le
      have last := mul_nonneg sn slope
      nlinarith only [first,last]
    · have first := mul_nonneg cp.le (show 0≤
          (S+(13/37)*C)*(1-(3/4)*S)-13/50 by linarith only [star])
      have last := mul_nonneg (show 0≤(13/37)*c-s by linarith only [low])
        (show 0≤37/50-C*(1-(3/4)*S) by linarith only [slope])
      nlinarith only [first,last]
  · rw [min_eq_left (by linarith only [low])]
    have first := mul_nonneg cp.le (show 0≤
        (S+(13/37)*C)*(1-(3/4)*S)-13/50 by linarith only [star])
    have last := mul_nonneg (show 0≤s-(13/37)*c by linarith only [low])
      (mul_nonneg Cp.le weight.le)
    nlinarith only [first,last]

/-- The strictly positive wall correction (14). The axial equality is
kept separate because it is used explicitly in the proof. -/
theorem wall_delta (C S : ℝ) (Cp : 0<C) (Sp : 0<S)
    (unit : C^2+S^2=1) :
    (1/10)*S<1-(1-S)/C-(18/25)*S := by
  let η : ℝ := (1-S)/C
  have Cp1 : 0<1+S := by linarith only [Sp]
  have etaForm : η=C/(1+S) := by
    dsimp only [η]
    apply (div_eq_div_iff (ne_of_gt Cp) (ne_of_gt Cp1)).mpr
    nlinarith only [unit]
  have etaPositive : 0<η := by rw [etaForm]; exact div_pos Cp Cp1
  have identity : (1+η)*(1-η-(41/50)*S)=
      S*((η-41/100)^2+119/10000) := by
    have relation : C*η=1-S := by
      dsimp only [η]
      field_simp [ne_of_gt Cp] <;> ring
    have relation' : η*(1+S)=C := by
      rw [etaForm]
      field_simp [ne_of_gt Cp1] <;> ring
    have weighted := congrArg (fun z : ℝ => η*z) relation'
    have polynomial : 1-η^2=S*(1+η^2) := by
      nlinarith only [relation,weighted]
    nlinarith only [polynomial]
  have positive : 0<S*((η-41/100)^2+119/10000) :=
    mul_pos Sp (by nlinarith only [sq_nonneg (η-41/100)])
  have delta : 0<1-η-(41/50)*S := by
    apply (mul_pos_iff_of_pos_left (by linarith only [etaPositive])).mp
    linarith only [identity,positive]
  dsimp only [η] at delta
  linarith only [delta]

#print axioms lower_exit_margin
#print axioms wall_delta
end N12Compact.Completion.OtherCases.C976NegativeTop
