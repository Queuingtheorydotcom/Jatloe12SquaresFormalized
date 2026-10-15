import Compact.Completion.C1092.MPPMInwardPositiveNegativeSupport
import Compact.Geometry.IncreasingSegmentAvoidance

/-! The two genuine extra entrances of the positive inward far ending:
the negative successor's foreign right-far point, and the two endpoints
of one actual preceding-wall segment. All exits and contacts are weak. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

theorem negative_far_faces (C E : OpenSquare) (h : PairInput C E)
    (en : Normal E.c (-E.s)) (far : ¬E.Inside 1 (-14/25)) :
    E.loV+E.side≤-E.s-(14/25)*E.c ∧ 60/109< -E.s := by
  have f := negative_faces C E h en
  have eb := normal_bounds en
  have dp : 0<E.c := by linarith only [eb.1]
  have tp : 0< -E.s := by
    linarith only [f.upperV,f.lowerV,h.recipient.side,eb.2.1]
  have highU : E.c-(14/25)*E.s<E.loU+E.side := by
    apply lt_of_not_ge
    intro low
    have width : 1<E.c+(3/50)*(-E.s) := by
      linarith only [low,f.lowerU,h.recipient.side]
    have small := half_of_width en width
    have sine := sine_le_twice_half en
    nlinarith only [small,sine,f.upperV,f.lowerV,h.recipient.side,eb.2.1]
  have upperV : E.loV+E.side≤-E.s-(14/25)*E.c := by
    apply le_of_not_gt
    intro high
    apply far
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [highU,high,h.recipient.successorMarker.1,h.recipient.near.2.2.1,
        dp,tp,en.2.1]
  have width : 1< -E.s+(263/500)*E.c := by
    linarith only [upperV,f.lowerV,h.recipient.side]
  have large : 60/109< -E.s := by
    apply lt_of_not_ge
    intro low
    have bound := CommonCases.UnitCircleChord.increasing
      (c:=(91/109:ℝ)) (s:=60/109) (d:=E.c) (t:=-E.s) (A:=263/500) (B:=1)
      (by norm_num) dp.le (by norm_num) en.2.2 (by norm_num) en.1 low
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at bound
    linarith only [width,bound]
  exact ⟨upperV,large⟩

/-- The strict endpoints and convexity belong to one actual L. The
square/segment alternative is the existing exact crossing theorem,
including a crossing on either square face or either segment endpoint. -/
theorem left_segment_alternatives (C L : OpenSquare) (h : Input C)
    (marker : L.Inside (-543/500) 0) (seed : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    C.loV+C.side≤(543/500)*C.s ∨
      -(7059/25000)≤((13/50)*C.c-(43/500)*C.s)*C.loU-
        ((13/50)*C.s+(43/500)*C.c)*(C.loV+C.side) := by
  have p := profile C h
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have du : 0<C.c*(-1-(-543/500))+C.s*(13/50-0) := by
    linarith only [cp,p.positive]
  have dv : 0< -C.s*(-1-(-543/500))+C.c*(13/50-0) := by
    linarith only [cp,p.positive,h.normal.2.1]
  have startU : C.loU<C.c*(-1)+C.s*(13/50) := by
    linarith only [p.upperU,h.side,cb.2.1,h.normal.1]
  have endU : C.c*(-1)+C.s*(13/50)<C.loU+C.side := by
    linarith only [h.crosspoint.2.1,cp,h.normal.2.1]
  have startV : C.loV< -C.s*(-543/500)+C.c*0 := by
    linarith only [p.halfpoint.2.2.1,cp,p.positive]
  have cut := IncreasingSegmentAvoidance.dichotomy C L (-543/500) 0 (-1) (13/50)
    marker seed du dv startU endU startV apart
  have determinant :
      (-C.s*(-1-(-543/500))+C.c*(13/50-0))*(C.c*(-543/500)+C.s*0)-
        (C.c*(-1-(-543/500))+C.s*(13/50-0))*(-C.s*(-543/500)+C.c*0)=
        -(7059/25000) := by
    linear_combination -(7059/25000)*C.unit_normal
  rcases cut with above|oblique
  · exact Or.inl (by nlinarith only [above])
  · exact Or.inr (by rw [determinant] at oblique; nlinarith only [oblique])

end
#print axioms negative_far_faces
#print axioms left_segment_alternatives
end N12Compact.C1092MPPMInwardPositive
