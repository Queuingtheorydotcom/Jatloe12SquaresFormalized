import Compact.Completion.C1092.MMMP.Ending
import Compact.Completion.OtherCases.TopOnlyLeftPoint

/-! The final northeast profile follows from its established actual sign,
the genuine top origin and the actual right bar. The all-angle sign theorem
has already discharged the other representative before this local lemma. -/
namespace N12Compact.C1092MMMPStrongNortheastFaces
open S12 S12Pilot C977CornerCubic
open N12Compact.Completion.OtherCases
set_option Elab.async false

theorem profile (N : OpenSquare) (side : 1<N.side) (cn : Normal N.c N.s)
    (marker : N.Inside (7/20) (7/20)) (top : N.Inside (13/50) 1)
    (missingL : ¬N.Inside 0 (13/50)) (missingI : ¬N.Inside 0 (2/5))
    (missingO : ¬N.Inside 0 1) (missingC : ¬N.Inside 1 1)
    (bar : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬N.Inside 1 y) :
    C1092MMMPEnding.Profile N ∧ 252/373≤N.s := by
  have cb := normal_bounds cn
  have cp : 0<N.c := by linarith only [cb.1]
  have faces := TopOnlyLeftPoint.positive_faces N side cp cn.1 cn.2.1 marker top
    missingL missingO missingC (bar (13/50) le_rfl (by norm_num))
  have strong := TopOnlyLeftPoint.bar_face N side cp cn.1 cn.2.1 marker
    faces.1 faces.2.1 faces.2.2.2 bar
  have uStrong : (2/5)*N.s≤N.loU := by
    apply le_of_not_gt
    intro failure
    apply missingI
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,faces.2.2.2,side,marker.2.1,top.2.2.2,cp,cn.1,cn.2.1,cb.2.1]
  have span : 1<(11/25)*N.c+N.s := by linarith only [strong,faces.2.2.2,side]
  have angle := SharpPointScalars.half_lower N.c N.s (11/25) cp cn.1 cn.2.1 N.unit_normal span
  have denominator : 0<1+N.c := by linarith only [cp]
  have steep : 7*(1+N.c)<18*N.s := by
    have bound : 7/18 < N.s/(1+N.c) := by
      dsimp [C1092WallProfileScalars.half] at angle
      linarith only [angle]
    have scaled := (lt_div_iff₀ denominator).mp bound
    linarith only [scaled]
  have sine : 252/373≤N.s := by
    apply le_of_not_gt
    intro bad
    have cosine : N.c<275/373 := by linarith only [steep,bad]
    have first := mul_pos (show 0<275/373-N.c by linarith only [cosine])
      (show 0<275/373+N.c by linarith only [cp])
    have last := mul_pos (show 0<252/373-N.s by linarith only [bad])
      (show 0<252/373+N.s by linarith only [cn.1])
    nlinarith only [first,last,N.unit_normal]
  exact ⟨⟨uStrong,by linarith only [strong],faces.2.2.1,faces.2.2.2⟩,sine⟩

#print axioms profile
end N12Compact.C1092MMMPStrongNortheastFaces
