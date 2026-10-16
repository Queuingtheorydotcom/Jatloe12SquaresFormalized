import Compact.Completion.OtherCases.SouthwestSupportPoint.LowerFaces
import Compact.Completion.OtherCases.SouthwestSupportPoint.Scalars

/-! Sections 4 and 5 of C974-C976-SW-SUPPORT-POINT: all four target bands
for the nonnegative canonical sign, with the actual segment alternatives. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

private theorem positive_lowerU (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (support : q.loU+q.side≤(13/50)*q.c ∨ upper q 35 9≤91/10) :
    q.loU< -(73/100)*q.c-(1/25)*q.s := by
  apply lt_of_not_ge
  intro low
  rcases support with cap | wall
  · have short := (short_projections q (99/100) (1/25) (by norm_num)).2.1
    linarith only [low,cap,h.side,short]
  · let α := 35*q.c+9*q.s
    let β := 9*q.c-35*q.s
    have ap : 0<α := by dsimp only [α]; linarith only [cp,sn]
    have first := mul_nonneg ap.le (sub_nonneg.mpr low)
    have beta : -35*q.s+9*q.c=β := by dsimp only [β]; ring
    by_cases sign : 0≤β
    · have floor := (LowerFaces.positive q h cp sn order).1
      have second := mul_nonneg sign (sub_nonneg.mpr floor)
      have exactSupport : upper q 35 9=α*(q.loU+q.side)+β*(q.loV+q.side) := by
        rw [WallProfile.upper_in_bands,beta,
          abs_of_nonneg (show 0≤35*q.c+9*q.s from ap.le),abs_of_nonneg sign]
        dsimp only [α]
        ring
      have margin := Scalars.positive_low q.c q.s cp sn order q.unit_normal sign
      have strict := mul_pos (sub_pos.mpr h.side)
        (show 0<α+β by linarith only [ap,sign])
      change 0<α+β-α*((73/100)*q.c+(1/25)*q.s)+β*((2/5)*q.s-q.c)-91/10 at margin
      nlinarith only [wall,exactSupport,first,second,margin,strict]
    · have sign' : β≤0 := le_of_not_ge sign
      have p := h.inwardSouth
      have pLow : q.loV< -(13/50)*q.c := by
        linarith only [p.2.2.1]
      have second := mul_nonneg_of_nonpos_of_nonpos sign'
        (show q.loV+(13/50)*q.c≤0 by linarith only [pLow])
      have exactSupport : upper q 35 9=α*(q.loU+q.side)+β*q.loV := by
        rw [WallProfile.upper_in_bands,beta,
          abs_of_nonneg (show 0≤35*q.c+9*q.s from ap.le),abs_of_nonpos sign']
        dsimp only [α]
        ring
      have margin := Scalars.positive_high q.c q.s cp sn order q.unit_normal sign'
      have strict := mul_pos (sub_pos.mpr h.side) ap
      change 0<α*(1-(73/100)*q.c-(1/25)*q.s)-(13/50)*q.c*β-91/10 at margin
      nlinarith only [wall,exactSupport,first,second,margin,strict]

private theorem positive_upperV (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    (73/100)*q.s-(1/25)*q.c<q.loV+q.side := by
  have floor := (LowerFaces.positive q h cp sn order).1
  by_cases slope : (3/4)*q.c≤q.s
  · have short := CommonCases.CanonicalProjection.after q.c q.s (4/5) (3/5)
      (24/25) (33/100) q.unit_normal (by norm_num) (by linarith only [slope])
      (by norm_num) (by norm_num)
    linarith only [floor,h.side,short]
  · have slope' : q.s≤(3/4)*q.c := le_of_not_ge slope
    apply lt_of_not_ge
    intro targetCap
    have m := h.marker
    have d := h.inwardWest
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at m d
    have shortB := (short_projections q (-23/100) (24/25) (by norm_num)).2.2.2
    have bLowV : q.loV<q.s*(1/2)-q.c := by linarith only [targetCap,h.side,shortB]
    have bHighV : q.s*(1/2)-q.c<q.loV+q.side := by
      linarith only [m.2.2.2,cp,order]
    have bFace : -(1/2)*q.c-q.s≤q.loU := by
      apply le_of_not_gt
      intro lower
      exact h.bottomSegment (-1/2) le_rfl (by norm_num)
        ⟨by linarith only [lower],by linarith only [m.2.1,cp,sn],
          by linarith only [bLowV],by linarith only [bHighV]⟩
    have shortN := CommonCases.CanonicalProjection.before q.c q.s (4/5) (3/5)
      (3/20) (27/20) q.unit_normal (by norm_num) (by linarith only [slope'])
      (by norm_num) (by norm_num)
    have nFace : q.loV+q.side≤(7/20)*(q.c+q.s) := by
      apply le_of_not_gt
      intro upper
      exact h.missingNorth ⟨by linarith only [m.1,sn],
        by linarith only [bFace,h.side,shortN],
        by linarith only [m.2.2.1,cp],by linarith only [upper]⟩
    have rFace : q.loU+q.side≤(7/20)*(q.c-q.s) := by
      apply le_of_not_gt
      intro upper
      have lowerV : q.loV< -(7/20)*(q.c+q.s) := by
        have short := CommonCases.OutwardScalars.increasing_projection q.c q.s (7/10) (7/10)
          cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
        linarith only [nFace,h.side,short]
      exact h.missingEast ⟨by linarith only [m.1,cp],by linarith only [upper],
        by linarith only [lowerV],by linarith only [d.2.2.2,cp,sn]⟩
    have shortZ := (short_projections q (61/100) (13/20) (by norm_num)).2.1
    have zLowU : q.loU< -(13/50)*q.c-q.s := by
      linarith only [rFace,h.side,shortZ]
    have zHighU : -(13/50)*q.c-q.s<q.loU+q.side := by linarith only [d.2.1,sn]
    have zFace : (13/50)*q.s-q.c≤q.loV := by
      apply le_of_not_gt
      intro lower
      exact h.bottomSegment (-13/50) (by norm_num) le_rfl
        ⟨by linarith only [zLowU],by linarith only [zHighU],
          by linarith only [lower],by linarith only [m.2.2.2,cp,sn]⟩
    have vertex := LowerCornerSupport.horizontal q (-1/2) (-13/50) (by norm_num)
      (by linarith only [bFace])
      ⟨by linarith only [bLowV],by linarith only [bHighV]⟩
      ⟨by linarith only [zLowU],by linarith only [zHighU]⟩
      (by linarith only [zFace]) h.bottomSegment
    have first := mul_nonneg sn (sub_nonneg.mpr rFace)
    have last := mul_nonneg cp.le (sub_nonneg.mpr targetCap)
    have necessary : q.side*(q.c+q.s)≤24/25-(31/100)*q.s^2+(27/25)*q.c*q.s := by
      nlinarith only [first,last,vertex,q.unit_normal]
    have margin := Scalars.positive_vertex q.c q.s cp sn order q.unit_normal slope'
    change 0<q.c+q.s-24/25+(31/100)*q.s^2-(27/25)*q.c*q.s at margin
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<q.c+q.s by linarith only [cp,sn])
    nlinarith only [necessary,margin,strict]

theorem positive (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (support : q.loU+q.side≤(13/50)*q.c ∨ upper q 35 9≤91/10) :
    q.Inside (-73/100) (-1/25) := by
  have lowerU := positive_lowerU q h cp sn order support
  have upperV := positive_upperV q h cp sn order
  have west := h.west
  have marker := h.marker
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [lowerU,upperV,west.2.1,marker.2.2.1,cp,sn]

#print axioms positive
end N12Compact.Completion.OtherCases.SouthwestSupportPoint
