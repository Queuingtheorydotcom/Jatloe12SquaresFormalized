import Compact.Completion.OtherCases.OrdinaryLeftTop.Inputs
import Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins

/-! The complete nonpositive canonical-sign argument in
ORDINARY-LEFT-TOP-OBSTRUCTION.md, section 1.1. Axial and diagonal frames are
included. All strictness comes from original point ownership and side > 1. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop
open S12 S12Pilot
set_option Elab.async false

theorem nonpositive_impossible (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s = -t) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c) : False := by
  have unit : q.c^2+t^2=1 := by
    have original := q.unit_normal
    rw [signed] at original
    nlinarith only [original]
  have bounds := CommonCases.CanonicalScalars.bounds q.c t cp tn order unit
  have cu : q.c ≤ 1 := bounds.2.1
  have bands (x y : ℝ) : q.Inside x y ↔
      q.loU < q.c*x-t*y ∧ q.c*x-t*y < q.loU+q.side ∧
      q.loV < t*x+q.c*y ∧ t*x+q.c*y < q.loV+q.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  have m := (bands _ _).mp h.marker
  have a := (bands _ _).mp h.anchor
  have farLowerU : q.loU < q.c*(37/50)-t*0 := by
    linarith only [a.1,cp,tn]
  have farUpperV : t*(37/50)+q.c*0 < q.loV+q.side := by
    linarith only [m.2.2.2,order,cp]
  have farFaces : q.loU+q.side ≤ (37/50)*q.c ∨ (37/50)*t ≤ q.loV := by
    by_cases upper : q.loU+q.side ≤ (37/50)*q.c
    · exact Or.inl upper
    · right
      apply le_of_not_gt
      intro lower
      exact h.far ((bands _ _).mpr
        ⟨farLowerU,by linarith only [upper],by linarith only [lower],farUpperV⟩)
  have farUpperU : q.loU+q.side ≤ (37/50)*q.c := by
    rcases farFaces with upper | lower
    · exact upper
    · exfalso
      have topUpperU : q.loU+q.side ≤ (37/50)*q.c-t := by
        apply le_of_not_gt
        intro upper
        exact h.topFar ((bands _ _).mpr ⟨
          by linarith only [a.1,order],
          by linarith only [upper],
          by linarith only [m.2.2.1,cp,tn],
          by linarith only [lower,h.side,cu]⟩)
      have cornerLowerU : -t ≤ q.loU := by
        apply le_of_not_gt
        intro lowerU
        exact h.corner ((bands _ _).mpr ⟨
          by linarith only [lowerU],
          by linarith only [a.2.1,tn],
          by linarith only [a.2.2.1,cp],
          by linarith only [lower,h.side,cu,tn]⟩)
      linarith only [topUpperU,cornerLowerU,h.side,cu]
  have middleFaces : q.loU+q.side ≤ (1/2)*q.c ∨ (1/2)*t ≤ q.loV := by
    by_cases upper : q.loU+q.side ≤ (1/2)*q.c
    · exact Or.inl upper
    · right
      apply le_of_not_gt
      intro lower
      exact h.middle ((bands _ _).mpr ⟨
        by linarith only [a.1,cp,tn],
        by linarith only [upper],
        by linarith only [lower],
        by linarith only [m.2.2.2,cp,tn]⟩)
  have middleUpperU : q.loU+q.side ≤ (1/2)*q.c := by
    rcases middleFaces with upper | lower
    · exact upper
    · exfalso
      have topLowerU : (11/25)*q.c-t ≤ q.loU := by
        apply le_of_not_gt
        intro lowerU
        exact h.topNear ((bands _ _).mpr ⟨
          by linarith only [lowerU],
          by linarith only [m.2.1,cp,tn],
          by linarith only [m.2.2.1,cp,order],
          by linarith only [lower,h.side,cu,tn]⟩)
      have projection := ScalarMargins.threeTenths q.c t cp tn order unit
      linarith only [topLowerU,farUpperU,projection,h.side]
  have angle : (3/7)*q.c < t := by
    linarith only [m.2.1,middleUpperU]
  have leftLowerV : -(43/500)*t ≤ q.loV := by
    apply le_of_not_gt
    intro lowerV
    have lowerU : q.loU < -(43/500)*q.c := by
      apply lt_of_not_ge
      intro no
      linarith only [no,middleUpperU,h.side,cu]
    exact h.left ((bands _ _).mpr ⟨
      by linarith only [lowerU],
      by linarith only [m.2.1,cp,order],
      by linarith only [lowerV],
      by linarith only [m.2.2.2,cp,tn]⟩)
  have cornerLowerU : -t ≤ q.loU := by
    apply le_of_not_gt
    intro lowerU
    have upperV : q.c < q.loV+q.side := by
      have projection := ScalarMargins.smallSine q.c t cp tn order unit angle.le
      linarith only [leftLowerV,projection,h.side]
    exact h.corner ((bands _ _).mpr ⟨
      by linarith only [lowerU],
      by linarith only [a.2.1,tn],
      by linarith only [a.2.2.1,cp],
      by linarith only [upperV]⟩)
  have angleLarge : (2/3)*q.c < t := by
    apply lt_of_not_ge
    intro no
    have projection := ScalarMargins.halfBeforeTwoThirds q.c t cp tn order unit no
    linarith only [middleUpperU,cornerLowerU,projection,h.side]
  have topUpperV : q.loV+q.side ≤ q.c+(11/25)*t := by
    apply le_of_not_gt
    intro upperV
    have lowerU : q.loU < (11/25)*q.c-t := by
      apply lt_of_not_ge
      intro no
      have projection := ScalarMargins.sixHundredths q.c t cp tn order unit
      linarith only [no,middleUpperU,projection,h.side]
    exact h.topNear ((bands _ _).mpr ⟨
      by linarith only [lowerU],
      by linarith only [m.2.1,cp,tn],
      by linarith only [m.2.2.1,cp,order],
      by linarith only [upperV]⟩)
  have projectionU := ScalarMargins.twentySevenOneOhFour q.c t cp tn order unit
  have projectionV := ScalarMargins.oneOhFourSeventeen q.c t cp tn order unit angleLarge.le
  exact h.lower ((bands _ _).mpr ⟨
    by linarith only [a.1,cp,tn],
    by linarith only [cornerLowerU,projectionU,h.side],
    by linarith only [topUpperV,projectionV,h.side],
    by linarith only [a.2.2.2,cp,order]⟩)

end N12Compact.Completion.OtherCases.OrdinaryLeftTop
