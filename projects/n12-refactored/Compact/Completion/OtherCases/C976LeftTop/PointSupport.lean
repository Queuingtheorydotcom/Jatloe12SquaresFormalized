import Compact.Completion.OtherCases.C976LeftTop.PointProfile

/-! The lower-segment support used in C976-LEFT-UPPER-POINTS sections
3 and 5. The proof retains both endpoint exits and the weak corner tie.
It does not need the target upper point as an input. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open S12 S12Pilot
set_option Elab.async false

def lowerAlpha (c s : ℝ) : ℝ := (13/100)*c+(6/25)*s
def lowerBeta (c s : ℝ) : ℝ := (6/25)*c-(13/100)*s

theorem lower_segment_support (q : OpenSquare) (h : Input q) (p : Profile q)
    (large : (1/3)*q.c≤q.s) :
    -(39/625)≤lowerAlpha q.c q.s*q.loU+lowerBeta q.c q.s*q.loV := by
  let a := lowerAlpha q.c q.s
  let b := lowerBeta q.c q.s
  have ap : 0<a := by dsimp only [a,lowerAlpha]; linarith only [p.cosine,p.sine]
  have bp : 0<b := by dsimp only [b,lowerBeta]; linarith only [p.cosine,p.canonical]
  have left := h.left
  have marker := h.marker
  have inward := h.inward
  have norm : (3*q.c+q.s)^2≤10 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-3*q.s)]
  have comparison : (113/100)*q.c-(6/25)*q.s≤(63/200)*(3*q.c+q.s) := by
    linarith only [large]
  have short : (113/100)*q.c-(6/25)*q.s<1 := by
    have squared : ((63/200)*(3*q.c+q.s))^2<1 := by nlinarith only [norm]
    have bound : (63/200)*(3*q.c+q.s)<1 := by
      nlinarith only [squared,sq_nonneg ((63/200)*(3*q.c+q.s)-1)]
    linarith only [comparison,bound]
  let uE := -(6/25)*q.c-(13/100)*q.s
  let vE := (6/25)*q.s-(13/100)*q.c
  let uF := -(13/50)*q.s
  let vF := -(13/50)*q.c
  have eLowV : q.loV<vE := by dsimp only [vE]; linarith only [p.upperV,h.side,short]
  have eHighV : vE<q.loV+q.side := by dsimp only [vE]; linarith only [inward.2.2.2,p.cosine,p.canonical]
  have eHighU : uE<q.loU+q.side := by dsimp only [uE]; linarith only [left.2.1,p.cosine,p.sine]
  have eFace : uE≤q.loU := by
    apply le_of_not_gt
    intro low
    have missing := h.segment 0 (by norm_num) (by norm_num)
    norm_num at missing
    apply missing
    dsimp only [uE,vE] at low eHighU eLowV eHighV
    exact ⟨by linarith only [low],by linarith only [eHighU],
      by linarith only [eLowV],by linarith only [eHighV]⟩
  have fHighU : uF<q.loU+q.side := by dsimp only [uF]; linarith only [marker.2.1,p.cosine,p.sine]
  have fHighV : vF<q.loV+q.side := by dsimp only [vF]; linarith only [inward.2.2.2,p.cosine]
  by_cases fFace : uF≤q.loU
  · have first := mul_nonneg ap.le (sub_nonneg.mpr fFace)
    have last := mul_nonneg bp.le (sub_nonneg.mpr p.lowerV)
    have positive := mul_nonneg
      (show 0≤(3/4)*q.c-q.s by linarith only [p.angleUpper])
      (show 0≤(467/5000)*q.c-(351/10000)*(q.s+(3/4)*q.c) by
        linarith only [p.canonical,p.cosine])
    have identity : (33/625)*q.c^2-(467/5000)*q.c*q.s+(351/10000)*q.s^2=
        (399/160000)*q.c^2+((3/4)*q.c-q.s)*
          ((467/5000)*q.c-(351/10000)*(q.s+(3/4)*q.c)) := by ring
    have margin : 0<(33/625)*q.c^2-(467/5000)*q.c*q.s+(351/10000)*q.s^2 := by
      nlinarith only [identity,positive,sq_pos_of_pos p.cosine]
    change -(39/625)≤a*q.loU+b*q.loV
    dsimp only [a,b,uF,lowerAlpha,lowerBeta] at first last ⊢
    nlinarith only [first,last,margin,q.unit_normal]
  · have fLowU : q.loU<uF := lt_of_not_ge fFace
    have fLowV : vF≤q.loV := by
      apply le_of_not_gt
      intro low
      have missing := h.segment 1 (by norm_num) le_rfl
      norm_num at missing
      apply missing
      dsimp only [uF,vF] at fLowU fHighU low fHighV
      exact ⟨by linarith only [fLowU],by linarith only [fHighU],
        by linarith only [low],by linarith only [fHighV]⟩
    have avoid (t : ℝ) (low : 0≤t) (high : t≤1) :
        ¬(q.loU<(1-t)*uE+t*uF ∧ (1-t)*uE+t*uF<q.loU+q.side ∧
          -(q.loV+q.side)<(1-t)*(-vE)+t*(-vF) ∧
          (1-t)*(-vE)+t*(-vF)< -q.loV) := by
      rintro ⟨a,b,c,d⟩
      apply h.segment t low high
      dsimp only [uE,vE,uF,vF] at a b c d
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [a,b,c,d]
    have corner := SegmentCorner.crossing_order q.loU (q.loU+q.side)
      (-(q.loV+q.side)) (-q.loV) uE (-vE) uF (-vF)
      eFace fLowU fHighU (by linarith only [eHighV]) (by linarith only [eLowV])
      (by linarith only [fLowV]) avoid
    dsimp only [uE,vE,uF,vF] at corner
    dsimp only [lowerAlpha,lowerBeta]
    nlinarith only [corner,q.unit_normal]

theorem upperU_strict (q : OpenSquare) (h : Input q) (p : Profile q)
    (large : (1/3)*q.c≤q.s) :
    lowerAlpha q.c q.s+lowerBeta q.c q.s*(1-q.c)-39/625<
      lowerAlpha q.c q.s*(q.loU+q.side) := by
  have support := lower_segment_support q h p large
  have ap : 0<lowerAlpha q.c q.s := by dsimp only [lowerAlpha]; linarith only [p.cosine,p.sine]
  have bp : 0<lowerBeta q.c q.s := by dsimp only [lowerBeta]; linarith only [p.cosine,p.canonical]
  have upper := mul_nonneg bp.le (sub_nonneg.mpr p.upperV)
  have extra := mul_pos (sub_pos.mpr h.side) (add_pos ap bp)
  nlinarith only [support,upper,extra]

end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
