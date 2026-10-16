import Compact.Completion.OtherCases.BottomBarSupport
import Compact.Completion.CommonCases.CanonicalProjection

/-! Source translation of C974-C976-NEGATIVE-UPPER-ANGLE, Theorem 1.
The entire foreign segment is retained; its lower-right tangency is handled
by the existing closed corner-support theorem. No side upper bound is used. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
open S12 S12Pilot
set_option Elab.async false

theorem mixed_angle (N : OpenSquare) (s : ℝ) (signed : N.s = -s)
    (side : 1<N.side) (cp : 0<N.c) (sn : 0≤s) (order : s≤N.c)
    (marker : N.Inside (7/20) (-13/20))
    (inward : N.Inside 0 (-37/50)) (elbow : N.Inside (13/50) 0)
    (origin : ¬N.Inside 0 0)
    (segment : ∀ x : ℝ,13/50≤x → x≤1/2 → ¬N.Inside x (-1)) :
    0<s ∧ s<(13/25)*N.c ∧ 0≤N.loU ∧ (1/2)*s-N.c≤N.loV := by
  have unit : N.c^2+s^2=1 := by simpa only [signed,neg_sq] using N.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds N.c s cp sn order unit
  have bands (x y : ℝ) : N.Inside x y ↔
      N.loU<N.c*x-s*y ∧ N.c*x-s*y<N.loU+N.side ∧
      N.loV<s*x+N.c*y ∧ s*x+N.c*y<N.loV+N.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  have m := (bands _ _).mp marker
  have f := (bands _ _).mp inward
  have g := (bands _ _).mp elbow
  have uLower : 0≤N.loU := by
    apply le_of_not_gt
    intro low
    apply origin ((bands _ _).mpr ?_)
    refine ⟨by linarith only [low],?_,?_,?_⟩ <;>
      linarith only [g.2.1,g.2.2.2,m.2.2.1,cp,sn,order]
  have sp : 0<s := by linarith only [uLower,f.1]
  have short := CommonCases.OutwardScalars.increasing_projection N.c s (13/50) 1
    cp sn order unit (by norm_num) (by norm_num) (by norm_num)
  have dLowU : N.loU<N.c*(13/50)+s := by linarith only [g.1,sp]
  have dHighU : N.c*(13/50)+s<N.loU+N.side := by
    linarith only [uLower,side,short]
  have dHighV : s*(13/50)-N.c<N.loV+N.side := by
    linarith only [g.2.2.2,cp]
  have dFace : (13/50)*s-N.c≤N.loV := by
    apply le_of_not_gt
    intro low
    exact segment (13/50) le_rfl (by norm_num) ((bands _ _).mpr
      ⟨by linarith only [dLowU],by linarith only [dHighU],
        by linarith only [low],by linarith only [dHighV]⟩)
  have xLowU : N.loU<N.c*(1/2)+s := by linarith only [m.1,cp,sp]
  have xHighV : s*(1/2)-N.c<N.loV+N.side := by
    linarith only [m.2.2.2,cp,order]
  have lastFace : (1/2)*s-N.c≤N.loV := by
    apply le_of_not_gt
    intro xLowV
    have xFace : N.loU+N.side≤(1/2)*N.c+s := by
      apply le_of_not_gt
      intro high
      exact segment (1/2) (by norm_num) le_rfl ((bands _ _).mpr
        ⟨by linarith only [xLowU],by linarith only [high],
          by linarith only [xLowV],by linarith only [xHighV]⟩)
    have span : 1<(1/2)*N.c+s := by linarith only [uLower,side,xFace]
    have slope : (3/4)*N.c<s := by
      apply lt_of_not_ge
      intro small
      have projection := CommonCases.CanonicalProjection.before N.c s (4/5) (3/5)
        (1/2) 1 unit (by norm_num) (by linarith only [small])
        (by norm_num) (by norm_num)
      linarith only [span,projection]
    have sineLarge : 3/5<s := by
      apply lt_of_not_ge
      intro small
      have cosineSmall : N.c<4/5 := by linarith only [slope,small]
      have csq := mul_pos (sub_pos.mpr cosineSmall)
        (show 0<4/5+N.c by linarith only [cp])
      have ssq := mul_nonneg (sub_nonneg.mpr small)
        (show 0≤3/5+s by linarith only [sn])
      nlinarith only [unit,csq,ssq]
    have sineSmall : s<1 := by nlinarith only [unit,sq_pos_of_pos cp,sp]
    have corner := LowerCornerSupport.horizontal (turnFrame N) (13/50) (1/2)
      (by norm_num)
      (by dsimp only [turnFrame]; rw [signed]; linarith only [dFace])
      (by dsimp only [turnFrame]; rw [signed];
          constructor <;> linarith only [dLowU,dHighU])
      (by dsimp only [turnFrame]; rw [signed];
          constructor <;> linarith only [xLowV,xHighV])
      (by dsimp only [turnFrame]; rw [signed]; linarith only [xFace])
      (fun x low high own => segment x low high ((turnFrame_inside N x (-1)).mp own))
    have physical : -1≤ -s*(N.loU+N.side)+N.c*N.loV := by
      dsimp only [turnFrame] at corner
      rw [signed] at corner
      nlinarith only [corner]
    have height : 1<s+(37/50)*N.c^2 := by
      have product := mul_pos (sub_pos.mpr sineSmall)
        (show 0<(37/50)*s-13/50 by linarith only [sineLarge])
      nlinarith only [product,unit]
    have first := mul_pos sp (show 0<N.loU+N.side-1 by linarith only [uLower,side])
    have second := mul_pos cp (show 0< -(37/50)*N.c-N.loV by linarith only [f.2.2.1])
    nlinarith only [physical,height,first,second]
  exact ⟨sp,by linarith only [lastFace,f.2.2.1],uLower,lastFace⟩

#print axioms mixed_angle
end N12Compact.Completion.OtherCases.C976NegativeTop
