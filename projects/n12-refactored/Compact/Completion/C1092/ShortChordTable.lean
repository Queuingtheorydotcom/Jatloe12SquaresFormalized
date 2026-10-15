import Compact.Geometry.C977CornerCubic
import S12.ShortCluster

/-! Two genuine short chords give complete face tables for both canonical
signs. Four actual excluded endpoints and three strict owned points suffice;
the proof uses the literal face alternatives, without a chord formula. -/
namespace N12Compact.C1092ShortChordTable
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

def PositiveFaces (b t p q a : ℝ) : Prop :=
  -b ≤ p ∧ p+a ≤ t-(39/100)*b ∧ (39/100)*t ≤ q ∧ q+a ≤ b+t

def NegativeFaces (b t p q a : ℝ) : Prop :=
  -b-t ≤ p ∧ p+a ≤ -(39/100)*b ∧ -t ≤ q ∧ q+a ≤ b-(39/100)*t

theorem steep {b t a : ℝ} (cn : Normal b t) (ha : 1 < a)
    (width : a ≤ t+(61/100)*b) :
    (9/20 : ℝ) < t ∧ b < 9/10 := by
  have bounds := normal_bounds cn
  have bweak : b ≤ 1-t^2/2 := by
    nlinarith only [cn.2.2,sq_nonneg (1-b)]
  have tp : 9/20 < t := by
    apply lt_of_not_ge
    intro no
    have first : 0 ≤ 9/20-t := sub_nonneg.mpr no
    have last : 0 ≤ 1-(61/200)*(t+9/20) := by linarith only [no]
    have product := mul_nonneg first last
    nlinarith only [product,bweak,width,ha]
  have bp : b < 9/10 := by
    apply lt_of_not_ge
    intro no
    have first := mul_pos (show 0 < t-9/20 by linarith only [tp])
      (show 0 < t+9/20 by linarith only [cn.1])
    have last := mul_nonneg (show 0 ≤ b-9/10 by linarith only [no])
      (show 0 ≤ b+9/10 by linarith only [bounds.1])
    nlinarith only [first,last,cn.2.2]
  exact ⟨tp,bp⟩

theorem positive (B : OpenSquare) (ha : 1 < B.side) (cn : Normal B.c B.s)
    (M : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (L0 : ¬ B.Inside (-1) 0) (L1 : ¬ B.Inside (-1) 1)
    (R0 : ¬ B.Inside (-39/100) 0) (R1 : ¬ B.Inside (-39/100) 1) :
    PositiveFaces B.c B.s B.loU B.loV B.side ∧
      (9/20 : ℝ) < B.s ∧ B.c < 9/10 := by
  classical
  have bounds := normal_bounds cn
  have cp : 0 < B.c := by linarith only [bounds.1]
  have l0 : -B.c ≤ B.loU ∨ B.s ≤ B.loV := by
    by_cases first : -B.c ≤ B.loU
    · exact Or.inl first
    · right; apply le_of_not_gt; intro second; apply L0
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lt_of_not_ge first,second,M.2.1,H1.2.2.2,cp,cn.1]
  have l1 : B.loU+B.side ≤ -B.c+B.s ∨ B.loV+B.side ≤ B.c+B.s := by
    by_cases first : B.loU+B.side ≤ -B.c+B.s
    · exact Or.inl first
    · right; apply le_of_not_gt; intro second; apply L1
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lt_of_not_ge first,second,H2.1,H2.2.2.1,cp,cn.1]
  have rightLow : (39/100)*B.s ≤ B.loV := by
    apply le_of_not_gt
    intro low
    apply R0
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,H2.1,M.2.1,H1.2.2.2,cp,cn.1,cn.2.1]
  have rightHigh : B.loU+B.side ≤ B.s-(39/100)*B.c := by
    apply le_of_not_gt
    intro upper
    have vUpper : B.c+(39/100)*B.s < B.loV+B.side := by
      linarith only [rightLow,ha,bounds.2.1]
    apply R1
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,vUpper,H2.1,M.2.2.1,cp,cn.1]
  have leftHigh : B.loV+B.side ≤ B.c+B.s := by
    rcases l1 with bad | good
    · exfalso; linarith only [bad,M.2.1,cn.2.1]
    · exact good
  have leftLow : -B.c ≤ B.loU := by
    rcases l0 with good | bad
    · exact good
    · exfalso; linarith only [bad,leftHigh,ha,bounds.2.1]
  have faces : PositiveFaces B.c B.s B.loU B.loV B.side :=
    ⟨leftLow,rightHigh,rightLow,leftHigh⟩
  have width : B.side ≤ B.s+(61/100)*B.c := by linarith only [leftLow,rightHigh]
  exact ⟨faces,steep cn ha width⟩

theorem negative (B : OpenSquare) (ha : 1 < B.side) (cn : Normal B.c (-B.s))
    (M : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (L0 : ¬ B.Inside (-1) 0) (L1 : ¬ B.Inside (-1) 1)
    (R0 : ¬ B.Inside (-39/100) 0) (R1 : ¬ B.Inside (-39/100) 1) :
    NegativeFaces B.c (-B.s) B.loU B.loV B.side ∧
      (9/20 : ℝ) < -B.s ∧ B.c < 9/10 := by
  classical
  have bounds := normal_bounds cn
  have cp : 0 < B.c := by linarith only [bounds.1]
  have leftLow : B.s ≤ B.loV := by
    apply le_of_not_gt; intro low; apply L0
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,H2.1,M.2.1,H2.2.2.2,cp,cn.1,cn.2.1]
  have l1 : -B.c+B.s ≤ B.loU ∨ B.loV+B.side ≤ B.c+B.s := by
    by_cases first : -B.c+B.s ≤ B.loU
    · exact Or.inl first
    · right; apply le_of_not_gt; intro second; apply L1
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lt_of_not_ge first,second,M.2.1,H2.2.2.1,cp,cn.1]
  have r1 : -(39/100)*B.c+B.s ≤ B.loU ∨ B.loV+B.side ≤ B.c+(39/100)*B.s := by
    by_cases first : -(39/100)*B.c+B.s ≤ B.loU
    · exact Or.inl first
    · right; apply le_of_not_gt; intro second; apply R1
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lt_of_not_ge first,second,M.2.1,M.2.2.1,cp,cn.1,cn.2.1]
  have rightHigh : B.loU+B.side ≤ -(39/100)*B.c := by
    apply le_of_not_gt
    intro upper
    have rightLow : B.loV < (39/100)*B.s := by
      apply lt_of_not_ge
      intro low
      rcases r1 with first | last
      · linarith only [low,first,H1.1,H1.2.2.1,cp]
      · linarith only [low,last,ha,bounds.2.1]
    apply R0
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,rightLow,H2.1,M.2.2.2,cp,cn.1]
  have rightLow : B.loV+B.side ≤ B.c+(39/100)*B.s := by
    rcases r1 with bad | good
    · exfalso; linarith only [bad,rightHigh,ha,bounds.2.2.2.1]
    · exact good
  have leftHigh : -B.c+B.s ≤ B.loU := by
    rcases l1 with good | bad
    · exact good
    · exfalso; linarith only [bad,leftLow,ha,bounds.2.1]
  have faces : NegativeFaces B.c (-B.s) B.loU B.loV B.side := by
    refine ⟨?_,rightHigh,?_,?_⟩ <;> linarith only [leftHigh,leftLow,rightLow]
  have width : B.side ≤ -B.s+(61/100)*B.c := by linarith only [leftHigh,rightHigh]
  exact ⟨faces,steep cn ha width⟩

#print axioms positive
#print axioms negative
end N12Compact.C1092ShortChordTable
