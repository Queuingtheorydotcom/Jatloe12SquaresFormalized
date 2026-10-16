import Compact.Completion.OtherCases.LowerCornerSupport
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames

/-! Exhaustive full lower-support alternatives supplied by the actual
bottom bar. Neither endpoint is substituted for the whole excluded segment. -/
namespace N12Compact.Completion.OtherCases.BottomBarSupport
open S12 S12Pilot
set_option Elab.async false

theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (cu : q.c≤1)
    (elbow : q.Inside (13/50) 0)
    (lastLowU : q.loU<(4/5)*q.c-q.s)
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬q.Inside x (-1)) :
    -(13/50)*q.s-q.c≤q.loV ∨ -1≤q.s*q.loU+q.c*q.loV := by
  by_cases firstV : -(13/50)*q.s-q.c≤q.loV
  · exact Or.inl firstV
  · have rLowV : q.loV< -q.s*(13/50)-q.c := by linarith only [firstV]
    have rHighU : q.c*(13/50)-q.s<q.loU+q.side := by
      linarith only [elbow.2.1,sn]
    have rHighV : -q.s*(13/50)-q.c<q.loV+q.side := by
      linarith only [elbow.2.2.2,cp]
    have rFace : q.c*(13/50)-q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      exact avoid (13/50) le_rfl (by norm_num) (by
        simpa only [OpenSquare.Inside,InBands,mul_neg,neg_mul,mul_one,sub_eq_add_neg] using
          And.intro low (And.intro rHighU (And.intro rLowV rHighV)))
    have tLowU : q.loU<q.c*(4/5)-q.s := by linarith only [lastLowU]
    have tHighU : q.c*(4/5)-q.s<q.loU+q.side := by
      linarith only [rFace,side,cu]
    have tHighV : -q.s*(4/5)-q.c<q.loV+q.side := by
      linarith only [elbow.2.2.2,cp,sn]
    have tFace : -q.s*(4/5)-q.c≤q.loV := by
      apply le_of_not_gt
      intro low
      exact avoid (4/5) (by norm_num) le_rfl (by
        simpa only [OpenSquare.Inside,InBands,mul_neg,neg_mul,mul_one,sub_eq_add_neg] using
          And.intro tLowU (And.intro tHighU (And.intro low tHighV)))
    exact Or.inr (LowerCornerSupport.horizontal q (13/50) (4/5) (by norm_num)
      rFace ⟨rLowV,rHighV⟩ ⟨tLowU,tHighU⟩ tFace avoid)

theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (side : 1<q.side) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (lowerU : 0≤q.loU) (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0)
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬q.Inside x (-1)) :
    (13/50)*t-q.c≤q.loV ∧
      ((4/5)*t-q.c≤q.loV ∨ -1≤ -t*(q.loU+q.side)+q.c*q.loV) := by
  have m := marker
  have d := elbow
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,add_zero,zero_add]
    at m d
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have short := CommonCases.OutwardScalars.increasing_projection q.c t (13/50) 1
    cp tn order unit (by norm_num) (by norm_num) (by norm_num)
  have rLowU : q.loU<q.c*(13/50)+t := by linarith only [d.1,tn]
  have rHighU : q.c*(13/50)+t<q.loU+q.side := by linarith only [lowerU,side,short]
  have rHighV : t*(13/50)-q.c<q.loV+q.side := by linarith only [d.2.2.2,cp]
  have rFace : t*(13/50)-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    exact avoid (13/50) le_rfl (by norm_num) (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg,neg_mul,mul_one]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowU,rHighU,low,rHighV])
  refine ⟨by linarith only [rFace],?_⟩
  by_cases lastV : (4/5)*t-q.c≤q.loV
  · exact Or.inl lastV
  · right
    have tLowU : q.loU<q.c*(4/5)+t := by linarith only [m.1,cp,tn]
    have tLowV : q.loV<t*(4/5)-q.c := by linarith only [lastV]
    have tHighV : t*(4/5)-q.c<q.loV+q.side := by linarith only [d.2.2.2,cp,order]
    have tFace : q.loU+q.side≤q.c*(4/5)+t := by
      apply le_of_not_gt
      intro high
      exact avoid (4/5) (by norm_num) le_rfl (by
        simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg,neg_mul,mul_one]
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [tLowU,high,tLowV,tHighV])
    have support := LowerCornerSupport.horizontal (turnFrame q) (13/50) (4/5) (by norm_num)
      (by dsimp only [turnFrame]; rw [signed]; linarith only [rFace])
      (by dsimp only [turnFrame]; rw [signed]; constructor <;> linarith only [rHighU,rLowU])
      (by dsimp only [turnFrame]; rw [signed]; constructor <;> linarith only [tLowV,tHighV])
      (by dsimp only [turnFrame]; rw [signed]; linarith only [tFace])
      (fun x low high own => avoid x low high ((turnFrame_inside q x (-1)).mp own))
    dsimp only [turnFrame] at support
    rw [signed] at support
    nlinarith only [support]

#print axioms positive
#print axioms negative
end N12Compact.Completion.OtherCases.BottomBarSupport

