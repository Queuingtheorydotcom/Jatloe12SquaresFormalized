import Compact.Completion.OtherCases.C976MergedLeft.Profile

/-! Section 4 retains both lower-face alternatives at the actual left
segment. Its whole-segment condition is used at the possible corner tie. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open S12 S12Pilot C1092WallProfileScalars
set_option Elab.async false

theorem left_lower_face (q : OpenSquare) (h : Input q) (p : Profile q) :
    -(13/50)*q.s≤q.loU := by
  let alpha := (13/100)*q.c+(6/25)*q.s
  let beta := (6/25)*q.c-(13/100)*q.s
  have ap : 0<alpha := by dsimp only [alpha]; linarith only [p.cosine,p.sine]
  have bp : 0<beta := by dsimp only [beta]; linarith only [p.cosine,p.canonical]
  have cSmall := cosine_small q.c q.s p.cosine p.sine.le q.unit_normal p.angleLower
  have short : (113/100)*q.c-(6/25)*q.s<1 := by linarith only [cSmall,p.sine]
  let uS := -(6/25)*q.c-(13/100)*q.s
  let vS := (6/25)*q.s-(13/100)*q.c
  let uL := -(13/50)*q.s
  let vL := -(13/50)*q.c
  have sLowV : q.loV<vS := by dsimp only [vS]; linarith only [p.upperV,h.side,short]
  have sHighV : vS<q.loV+q.side := by
    dsimp only [vS]; linarith only [h.inward.2.2.2,p.cosine,p.canonical]
  have sHighU : uS<q.loU+q.side := by
    dsimp only [uS]; linarith only [h.left.2.1,p.cosine,p.sine]
  have sFace : uS≤q.loU := by
    apply le_of_not_gt
    intro low
    have missing := h.segment 0 (by norm_num) (by norm_num)
    norm_num at missing
    apply missing
    dsimp only [uS,vS] at low sHighU sLowV sHighV
    exact ⟨by linarith only [low],by linarith only [sHighU],
      by linarith only [sLowV],by linarith only [sHighV]⟩
  have lHighU : uL<q.loU+q.side := by
    dsimp only [uL]; linarith only [h.marker.2.1,p.cosine,p.sine]
  have lHighV : vL<q.loV+q.side := by
    dsimp only [vL]; linarith only [h.inward.2.2.2,p.cosine]
  apply le_of_not_gt
  intro lLowU
  have lLowU' : q.loU<uL := lLowU
  have lLowV : vL≤q.loV := by
    apply le_of_not_gt
    intro low
    have missing := h.segment 1 (by norm_num) le_rfl
    norm_num at missing
    apply missing
    dsimp only [uL,vL] at lLowU' lHighU low lHighV
    exact ⟨by linarith only [lLowU'],by linarith only [lHighU],
      by linarith only [low],by linarith only [lHighV]⟩
  have cLarge : 50/63<q.c := by
    dsimp only [vL] at lLowV
    linarith only [lLowV,p.upperV,h.side]
  have tSmall := half_small_of_cosine q.c q.s p.cosine p.sine.le q.unit_normal cLarge
  have avoid (t : ℝ) (low : 0≤t) (high : t≤1) :
      ¬(q.loU<(1-t)*uS+t*uL ∧ (1-t)*uS+t*uL<q.loU+q.side ∧
        -(q.loV+q.side)<(1-t)*(-vS)+t*(-vL) ∧
        (1-t)*(-vS)+t*(-vL)< -q.loV) := by
    rintro ⟨a,b,c,d⟩
    apply h.segment t low high
    dsimp only [uS,vS,uL,vL] at a b c d
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [a,b,c,d]
  have corner := SegmentCorner.crossing_order q.loU (q.loU+q.side)
    (-(q.loV+q.side)) (-q.loV) uS (-vS) uL (-vL)
    sFace lLowU' lHighU (by linarith only [sHighV]) (by linarith only [sLowV])
    (by linarith only [lLowV]) avoid
  have support : -(39/625)≤alpha*q.loU+beta*q.loV := by
    dsimp only [uS,vS,uL,vL] at corner
    dsimp only [alpha,beta]
    nlinarith only [corner,q.unit_normal]
  have upperU := mul_nonneg ap.le (sub_nonneg.mpr p.upperU)
  have upperV := mul_nonneg bp.le (sub_nonneg.mpr p.upperV)
  have width : q.side*((37/100)*q.c+(11/100)*q.s)≤
      27/80-(351/10000)*q.s^2+(81/1250)*q.c*q.s := by
    dsimp only [alpha,beta] at support upperU upperV
    nlinarith only [support,upperU,upperV,q.unit_normal]
  have margin := lower_corner_margin q.c q.s p.cosine p.sine.le q.unit_normal tSmall.le
  have extra := mul_pos (sub_pos.mpr h.side)
    (show 0<(37/100)*q.c+(11/100)*q.s by linarith only [p.cosine,p.sine])
  nlinarith only [width,margin,extra]

theorem half_large (q : OpenSquare) (h : Input q) (p : Profile q) :
    7/20<half q.c q.s := by
  have lower := left_lower_face q h p
  apply lt_of_not_ge
  intro small
  have span := early_span q.c q.s p.cosine p.sine.le q.unit_normal small
  linarith only [lower,p.upperU,h.side,span]

end N12Compact.Completion.OtherCases.C976MergedLeft
