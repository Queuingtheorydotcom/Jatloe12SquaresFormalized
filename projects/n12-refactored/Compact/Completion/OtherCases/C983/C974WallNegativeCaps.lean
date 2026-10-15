import Compact.Completion.OtherCases.C983.C974MissingCornerData

/-! MISSING-CORNER-WALL-SIGN §1.2, with all exclusions supplied by
the raw physical input. Coordinates stay in the original local chart.
The returned caps include weak boundary contact. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem wall_negative_caps (K W : OpenSquare) (e : Input K W) (t : ℝ)
    (frame : W.s= -t) (dp : 0<W.c) (tn : 0≤t) (order : t≤W.c) :
    (24/25)*W.c+(6/25)*t≤W.loU ∧ 77*t<20*W.c ∧
      W.loV+W.side≤2*t+W.c/2 ∧
      (W.loU+W.side≤2*W.c ∨ W.loV+W.side≤2*t) := by
  let d := W.c
  have unit : d^2+t^2=1 := by simpa only [frame,neg_sq] using W.unit_normal
  have side : 1<W.side := by simpa only [←e.sameSide] using e.sideLarge
  have du : d≤1 := by nlinarith only [unit,sq_nonneg t,dp]
  have p := e.pw
  have r := e.r
  dsimp [OpenSquare.Inside,InBands] at p r
  rw [frame] at p r
  have origin := e.o
  simp only [OpenSquare.Inside,InBands,frame,mul_one,mul_zero,add_zero,neg_neg] at origin
  have outside : ¬W.Inside (24/25) (-6/25) := fun own => e.apart _ _ ⟨e.s,own⟩
  have cAlternative : W.loU+W.side≤2*d ∨ W.loV+W.side≤2*t := by
    by_cases first : W.loU+W.side≤2*d
    · exact Or.inl first
    · right
      by_contra last
      apply e.missingC
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [InBands] <;> rw [frame] <;>
        linarith only [r.1,r.2.2.1,dp,tn,first,last]
  have lower : (24/25)*d+(6/25)*t≤W.loU := by
    by_contra no
    have lowV : (24/25)*t-(6/25)*d≤W.loV := by
      by_contra last
      apply outside
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [InBands] <;> rw [frame] <;>
        linarith only [no,last,r.2.1,origin.2.2.2,dp,tn,order]
    have mAlternative : (27/20)*d-(13/20)*t≤W.loU ∨
        W.loV+W.side≤(27/20)*t+(13/20)*d := by
      by_cases first : (27/20)*d-(13/20)*t≤W.loU
      · exact Or.inl first
      · right
        by_contra last
        apply e.missingM
        refine ⟨?_,?_,?_,?_⟩ <;> dsimp [InBands] <;> rw [frame] <;>
          linarith only [first,last,r.2.1,origin.2.2.1,dp,tn]
    have mLow : (27/20)*d-(13/20)*t≤W.loU := by
      rcases mAlternative with low | high
      · exact low
      · have width : 1<(39/100)*t+(89/100)*d := by linarith only [side,lowV,high]
        have projection : (39/100)*t+(89/100)*d<1 := by
          nlinarith only [unit,sq_nonneg ((39/100)*d-(89/100)*t)]
        exact (not_lt_of_ge projection.le width).elim
    have cHigh : W.loV+W.side≤2*t := by
      rcases cAlternative with highU | highV
      · have width : 1<(13/20)*(d+t) := by linarith only [side,mLow,highU]
        have sum : d+t≤3/2 := by nlinarith only [unit,sq_nonneg (d-t)]
        exact (by linarith only [width,sum] : False).elim
      · exact highV
    have width : 1<(26/25)*t+(6/25)*d := by linarith only [side,lowV,cHigh]
    have identity : (512/625)*(d^2+t^2)-((26/25)*t+(6/25)*d)^2=
        (d-t)*((476/625)*d+(164/625)*t) := by ring
    have product' := mul_nonneg (sub_nonneg.mpr order)
      (show 0≤(476/625)*d+(164/625)*t by positivity)
    have square := mul_pos (sub_pos.mpr width)
      (show 0<(26/25)*t+(6/25)*d+1 by positivity)
    rw [unit] at identity
    nlinarith only [product',identity,square]
  have slope : 77*t<20*d := by linarith only [lower,p.1]
  have f0' : d-t/2≤W.loU ∨ W.loV+W.side≤t+d/2 := by
    by_cases low : d-t/2≤W.loU
    · exact Or.inl low
    · right
      by_contra high
      apply e.missingF0
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [InBands] <;> rw [frame] <;>
        linarith only [low,high,r.2.1,origin.2.2.1,dp,tn]
  have f1 : W.loU+W.side≤2*d-t/2 ∨ W.loV+W.side≤2*t+d/2 := by
    by_cases highU : W.loU+W.side≤2*d-t/2
    · exact Or.inl highU
    · right
      by_contra highV
      apply e.missingF1
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [InBands] <;> rw [frame] <;>
        linarith only [highU,highV,r.1,r.2.2.1,dp,tn,slope]
  have cap : W.loV+W.side≤2*t+d/2 := by
    rcases f0' with low | high
    · rcases f1 with highU | highV
      · linarith only [side,low,highU,du]
      · exact highV
    · linarith only [high,tn]
  exact ⟨lower,slope,cap,cAlternative⟩

end
#print axioms wall_negative_caps
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
