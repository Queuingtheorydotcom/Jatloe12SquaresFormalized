import Compact.Completion.OtherCases.SouthwestSupportPoint.Inputs

/-! Section 2 of C974-C976-SW-SUPPORT-POINT. The negative frame is the
coordinate-swapped version of the same positive-frame lower-face proof. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint.LowerFaces
open S12 S12Pilot
set_option Elab.async false

private theorem positive_data (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (-7/20) (-7/20)) (inwardWest : q.Inside (-13/50) 0)
    (north : ¬q.Inside (-7/20) (7/20)) (east : ¬q.Inside (7/20) (-7/20))
    (bottom : ¬q.Inside (-2/5) (-1)) (left : ¬q.Inside (-1) (-13/50)) :
    (2/5)*q.s-q.c≤q.loV ∧ -q.c-(13/50)*q.s≤q.loU := by
  have m := marker
  have d := inwardWest
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at m d
  have bottomV : (2/5)*q.s-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    have bottomU : -(2/5)*q.c-q.s≤q.loU := by
      apply le_of_not_gt
      intro lowU
      exact bottom ⟨by linarith only [lowU],by linarith only [m.2.1,cp,sn],
        by linarith only [low],by linarith only [m.2.2.2,cp,order]⟩
    have shortN := CommonCases.OutwardScalars.increasing_projection q.c q.s (1/20) (27/20)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    have northV : q.loV+q.side≤(7/20)*(q.c+q.s) := by
      apply le_of_not_gt
      intro high
      exact north ⟨by linarith only [m.1,sn],
        by linarith only [bottomU,side,shortN],
        by linarith only [m.2.2.1,cp],by linarith only [high]⟩
    have shortR := (short_projections q (3/4) (13/20) (by norm_num)).2.1
    have eastV : -(7/20)*(q.s+q.c)≤q.loV := by
      apply le_of_not_gt
      intro lowV
      exact east ⟨by linarith only [m.1,cp],
        by linarith only [bottomU,side,shortR],
        by linarith only [lowV],by linarith only [d.2.2.2,cp,sn]⟩
    have shortWidth := CommonCases.OutwardScalars.increasing_projection q.c q.s (7/10) (7/10)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    linarith only [northV,eastV,side,shortWidth]
  have leftU : -q.c-(13/50)*q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    have short := (short_projections q (-3/5) (37/50) (by norm_num)).2.2.2
    exact left ⟨by linarith only [low],by linarith only [d.2.1,cp,sn],
      by linarith only [m.2.2.1,cp,sn],by linarith only [bottomV,side,short]⟩
  exact ⟨bottomV,leftU⟩

theorem positive (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    (2/5)*q.s-q.c≤q.loV ∧ -q.c-(13/50)*q.s≤q.loU :=
  positive_data q h.side cp sn order h.marker h.inwardWest h.missingNorth h.missingEast
    (h.bottomSegment (-2/5) (by norm_num) (by norm_num)) h.missingLeftHigh

theorem negative (q : OpenSquare) (h : Input q) (s : ℝ) (signed : q.s= -s)
    (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c) :
    (2/5)*s-q.c≤q.loU ∧ -(13/50)*s-q.c≤q.loV := by
  let r := turnFrame (turnFrame (turnFrame (pullSwap q)))
  have same (x y : ℝ) : r.Inside x y ↔ q.Inside y x := by
    simp only [r,turnFrame_inside,inside_pullSwap]
  have rc : r.c=q.c := by simp only [r,turnFrame,pullSwap,neg_neg]
  have rs : r.s=s := by simp only [r,turnFrame,pullSwap,signed,neg_neg]
  have side : r.side=q.side := rfl
  have data := positive_data r (by simpa only [side] using h.side)
    (by simpa only [rc] using cp) (by simpa only [rs] using sn)
    (by simpa only [rc,rs] using order)
    ((same _ _).mpr h.marker) ((same _ _).mpr h.inwardSouth)
    (fun p => h.missingEast ((same _ _).mp p))
    (fun p => h.missingNorth ((same _ _).mp p))
    (fun p => h.missingLeftLow ((same _ _).mp p))
    (fun p => h.bottomSegment (-13/50) (by norm_num) le_rfl ((same _ _).mp p))
  dsimp only [r,turnFrame,pullSwap] at data
  rw [signed] at data
  constructor <;> nlinarith only [data.1,data.2]

#print axioms positive
#print axioms negative
end N12Compact.Completion.OtherCases.SouthwestSupportPoint.LowerFaces
