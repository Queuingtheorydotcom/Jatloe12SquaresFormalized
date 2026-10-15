import Compact.Completion.OtherCases.C976LeftTop.Inputs
import Compact.Completion.OtherCases.C976LeftTop.Scalars

/-! Section 4: the entire original lower segment forces one weak lower
support, including a lower-vertex tangency. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot
set_option Elab.async false

theorem segment_support (N : OpenSquare) (n : LeftInput N)
    (large : (1/3)*N.c≤N.s) :
    Scalars.a0 N.c N.s*N.loU+Scalars.b0 N.c N.s*N.loV≥ -(39/625) := by
  let a := Scalars.a0 N.c N.s
  let b := Scalars.b0 N.c N.s
  have ap : 0<a := by dsimp only [a,Scalars.a0]; linarith only [n.cosine,n.sine]
  have bp : 0<b := by dsimp only [b,Scalars.b0]; linarith only [n.cosine,n.canonical]
  have p := n.left
  have m := n.marker
  have h := n.inward
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero] at p m h
  have norm : (3*N.c+N.s)^2≤10 := by
    nlinarith only [N.unit_normal,sq_nonneg (N.c-3*N.s)]
  have comparison : (113/100)*N.c-(6/25)*N.s≤(63/200)*(3*N.c+N.s) := by
    linarith only [large]
  have short : (113/100)*N.c-(6/25)*N.s<1 := by
    have squared : ((63/200)*(3*N.c+N.s))^2<1 := by nlinarith only [norm]
    have bound : (63/200)*(3*N.c+N.s)<1 := by
      nlinarith only [squared,sq_nonneg ((63/200)*(3*N.c+N.s)-1)]
    linarith only [comparison,bound]
  let uE := -(6/25)*N.c-(13/100)*N.s
  let vE := (6/25)*N.s-(13/100)*N.c
  let uF := -(13/50)*N.s
  let vF := -(13/50)*N.c
  have eLowV : N.loV<vE := by dsimp only [vE]; linarith only [n.upperV,n.side,short]
  have eHighV : vE<N.loV+N.side := by dsimp only [vE]; linarith only [h.2.2.2,n.cosine,n.canonical]
  have eHighU : uE<N.loU+N.side := by dsimp only [uE]; linarith only [p.2.1,n.cosine,n.sine]
  have eFace : uE≤N.loU := by
    apply le_of_not_gt
    intro low
    have missing := n.segment 0 (by norm_num) (by norm_num)
    norm_num at missing
    apply missing
    dsimp only [uE,vE] at low eHighU eLowV eHighV
    exact ⟨by linarith only [low],by linarith only [eHighU],
      by linarith only [eLowV],by linarith only [eHighV]⟩
  have fHighU : uF<N.loU+N.side := by dsimp only [uF]; linarith only [m.2.1,n.cosine,n.sine]
  have fHighV : vF<N.loV+N.side := by dsimp only [vF]; linarith only [h.2.2.2,n.cosine]
  by_cases fFace : uF≤N.loU
  · have first := mul_nonneg ap.le (sub_nonneg.mpr fFace)
    have last := mul_nonneg bp.le (sub_nonneg.mpr n.lowerV)
    have angle := angle_upper N n
    have positive := mul_nonneg
      (show 0≤(3/4)*N.c-N.s by linarith only [angle,n.cosine])
      (show 0≤(467/5000)*N.c-(351/10000)*(N.s+(3/4)*N.c) by
        linarith only [n.canonical,n.cosine])
    have identity :
        (33/625)*N.c^2-(467/5000)*N.c*N.s+(351/10000)*N.s^2=
        (399/160000)*N.c^2+((3/4)*N.c-N.s)*
          ((467/5000)*N.c-(351/10000)*(N.s+(3/4)*N.c)) := by ring
    have margin : 0<(33/625)*N.c^2-(467/5000)*N.c*N.s+(351/10000)*N.s^2 := by
      nlinarith only [identity,positive,sq_pos_of_pos n.cosine]
    change a*N.loU+b*N.loV≥ -(39/625)
    dsimp only [a,b,uF,Scalars.a0,Scalars.b0] at first last ⊢
    nlinarith only [first,last,margin,N.unit_normal]
  · have fLowU : N.loU<uF := lt_of_not_ge fFace
    have fLowV : vF≤N.loV := by
      apply le_of_not_gt
      intro low
      have missing := n.segment 1 (by norm_num) le_rfl
      norm_num at missing
      apply missing
      dsimp only [uF,vF] at fLowU fHighU low fHighV
      exact ⟨by linarith only [fLowU],by linarith only [fHighU],
        by linarith only [low],by linarith only [fHighV]⟩
    have avoid (t : ℝ) (low : 0≤t) (high : t≤1) :
        ¬(N.loU<(1-t)*uE+t*uF ∧ (1-t)*uE+t*uF<N.loU+N.side ∧
          -(N.loV+N.side)<(1-t)*(-vE)+t*(-vF) ∧
          (1-t)*(-vE)+t*(-vF)< -N.loV) := by
      rintro ⟨a,b,c,d⟩
      apply n.segment t low high
      dsimp only [uE,vE,uF,vF] at a b c d
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [a,b,c,d]
    have corner := SegmentCorner.crossing_order N.loU (N.loU+N.side)
      (-(N.loV+N.side)) (-N.loV) uE (-vE) uF (-vF)
      eFace fLowU fHighU (by linarith only [eHighV]) (by linarith only [eLowV])
      (by linarith only [fLowV]) avoid
    dsimp only [uE,vE,uF,vF] at corner
    dsimp only [Scalars.a0,Scalars.b0]
    nlinarith only [corner,N.unit_normal]

theorem upperU_strict (N : OpenSquare) (n : LeftInput N)
    (large : (1/3)*N.c≤N.s) :
    Scalars.a0 N.c N.s+Scalars.b0 N.c N.s*(1-N.c)-39/625<
      Scalars.a0 N.c N.s*(N.loU+N.side) := by
  have support := segment_support N n large
  have ap : 0<Scalars.a0 N.c N.s := by dsimp only [Scalars.a0]; linarith only [n.cosine,n.sine]
  have bp : 0<Scalars.b0 N.c N.s := by dsimp only [Scalars.b0]; linarith only [n.cosine,n.canonical]
  have upper := mul_nonneg bp.le (sub_nonneg.mpr n.upperV)
  have extra := mul_pos (sub_pos.mpr n.side) (add_pos ap bp)
  nlinarith only [support,upper,extra]

end N12Compact.Completion.OtherCases.C976LeftTop
