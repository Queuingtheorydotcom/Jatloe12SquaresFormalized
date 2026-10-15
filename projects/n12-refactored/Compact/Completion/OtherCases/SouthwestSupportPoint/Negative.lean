import Compact.Completion.OtherCases.SouthwestSupportPoint.LowerFaces
import Compact.Completion.OtherCases.SouthwestSupportPoint.Scalars

/-! Section 6 of C974-C976-SW-SUPPORT-POINT. Both weak exits of the
excluded bottom origin are retained; the exact f4/f5 margins cover them. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem negative (q : OpenSquare) (h : Input q) (s : ℝ) (signed : q.s= -s)
    (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c)
    (support : q.loU+q.side≤(13/50)*q.c ∨ upper q 35 9≤91/10) :
    q.Inside (-73/100) (-1/25) := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds q.c s cp sn order unit
  have bands (x y : ℝ) : q.Inside x y ↔
      q.loU<q.c*x-s*y ∧ q.c*x-s*y<q.loU+q.side ∧
      q.loV<s*x+q.c*y ∧ s*x+q.c*y<q.loV+q.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  have m := (bands _ _).mp h.marker
  have p := (bands _ _).mp h.inwardSouth
  have d := (bands _ _).mp h.inwardWest
  have e := (bands _ _).mp h.west
  have f := (bands _ _).mp h.south
  have upperU : -(73/100)*q.c+(1/25)*s<q.loU+q.side := by
    linarith only [e.2.1,cp,order]
  have upperV : -(73/100)*s-(1/25)*q.c<q.loV+q.side := by
    linarith only [d.2.2.2,cp,sn]
  rcases support with cap | wall
  · have lowerU : q.loU< -(73/100)*q.c+(1/25)*s := by
      linarith only [cap,h.side,bounds.2.1,sn]
    have angle : s<(13/25)*q.c := by linarith only [f.2.1,cap]
    have lowerV : q.loV< -(73/100)*s-(1/25)*q.c := by
      linarith only [m.2.2.1,angle,cp]
    exact (bands _ _).mpr ⟨by linarith only [lowerU],by linarith only [upperU],
      by linarith only [lowerV],by linarith only [upperV]⟩
  · let α := 35*q.c-9*s
    let β := 35*s+9*q.c
    have ap : 0<α := by dsimp only [α]; linarith only [cp,order]
    have bp : 0<β := by dsimp only [β]; linarith only [cp,sn]
    have exactSupport : upper q 35 9=α*(q.loU+q.side)+β*(q.loV+q.side) := by
      rw [WallProfile.upper_in_bands,signed]
      have alpha : 35*q.c+9*(-s)=α := by dsimp only [α]; ring
      have beta : -35*(-s)+9*q.c=β := by dsimp only [β]; ring
      rw [alpha,beta,abs_of_nonneg ap.le,abs_of_nonneg bp.le]
      ring
    have faces := LowerFaces.negative q h s signed cp sn order
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<α+β by linarith only [ap,bp])
    have lowerV : q.loV< -(73/100)*s-(1/25)*q.c := by
      apply lt_of_not_ge
      intro failed
      by_cases slope : s≤(3/4)*q.c
      · linarith only [m.2.2.1,slope,cp,failed]
      · have sine : 3/5≤s := by
          apply le_of_not_gt
          intro small
          have cosine : q.c<4/5 := by linarith only [slope,small]
          have first := mul_pos (sub_pos.mpr cosine)
            (show 0<4/5+q.c by linarith only [cp])
          have last := mul_nonneg (show 0≤3/5-s by linarith only [small])
            (show 0≤3/5+s by linarith only [sn])
          nlinarith only [first,last,unit]
        have floor : -q.c+(13/50)*s≤q.loU := by linarith only [faces.1,sn]
        have first := mul_nonneg ap.le (sub_nonneg.mpr floor)
        have last := mul_nonneg bp.le (sub_nonneg.mpr failed)
        have cross := mul_nonneg cp.le sn
        have margin : 0<44*q.c+26*s+(747/100)*s^2+(1013/100)*q.c*s-2223/50 := by
          nlinarith only [bounds.1,sine,cross,sq_nonneg s]
        have identity : α+β+α*(-q.c+(13/50)*s)+β*(-(73/100)*s-(1/25)*q.c)-91/10=
            44*q.c+26*s+(747/100)*s^2+(1013/100)*q.c*s-2223/50 := by
          dsimp only [α,β]
          linear_combination -(884/25)*unit
        nlinarith only [wall,exactSupport,first,last,strict,margin,identity]
    have lowerU : q.loU< -(73/100)*q.c+(1/25)*s := by
      apply lt_of_not_ge
      intro failed
      have first := mul_nonneg ap.le (sub_nonneg.mpr failed)
      have originFaces : -q.c≤q.loV ∨ q.loU+q.side≤s := by
        by_cases floor : -q.c≤q.loV
        · exact Or.inl floor
        · right
          apply le_of_not_gt
          intro cap
          exact h.missingBottom ((bands _ _).mpr ⟨
            by linarith only [p.1,sn],by linarith only [cap],
            by linarith only [floor],by linarith only [p.2.2.2,cp]⟩)
      rcases originFaces with floor | cap
      · have last := mul_nonneg bp.le (sub_nonneg.mpr floor)
        have margin := Scalars.negative_lower q.c s cp sn order unit
        change 0<α+β+α*(-(73/100)*q.c+(1/25)*s)-β*q.c-91/10 at margin
        nlinarith only [wall,exactSupport,first,last,strict,margin]
      · have span : 1<(73/100)*q.c+(24/25)*s := by linarith only [failed,cap,h.side]
        have angle := Scalars.half_lower_of_span q.c s cp sn unit span
        have last := mul_nonneg bp.le (sub_nonneg.mpr faces.2)
        have margin := Scalars.negative_upper q.c s cp sn order unit angle.le
        change 0<α+β+α*(-(73/100)*q.c+(1/25)*s)+β*(-(13/50)*s-q.c)-91/10 at margin
        nlinarith only [wall,exactSupport,first,last,strict,margin]
    exact (bands _ _).mpr ⟨by linarith only [lowerU],by linarith only [upperU],
      by linarith only [lowerV],by linarith only [upperV]⟩

#print axioms negative
end N12Compact.Completion.OtherCases.SouthwestSupportPoint
