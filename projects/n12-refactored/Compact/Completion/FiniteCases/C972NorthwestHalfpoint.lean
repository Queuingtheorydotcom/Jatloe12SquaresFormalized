import Compact.Completion.FiniteCases.C972NorthwestForward

/-! An NE-owned top origin forces the actual NW outer halfpoint.
The steep negative sector uses the whole left bar, with its same-square
support corner retained. The two isolated endpoints do not replace it. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem shallow_projection (c s : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (shallow : 17*s≤5*c) :
    (17/20)*c+(13/20)*s<1 := by
  have norm : (17*c+5*s)^2≤314 := by
    nlinarith only [unit,sq_nonneg (5*c-17*s)]
  have bound : 17*c+5*s<3140/177 := by
    by_contra bad
    have lower : 3140/177≤17*c+5*s := le_of_not_gt bad
    have product := mul_nonneg (sub_nonneg.mpr lower)
      (show 0≤17*c+5*s+3140/177 by linarith only [cp,sn])
    nlinarith only [norm,product]
  have compare : (17/20)*c+(13/20)*s≤(177/3140)*(17*c+5*s) := by
    linarith only [shallow]
  linarith only [compare,bound]

private theorem northwest_positive_half (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (forward : q.Inside 0 (13/50))
    (outer : q.Inside (2/5) 1) (near : q.Inside (13/50) 1)
    (left : ¬q.Inside (-7/20) (7/20)) (upper : ¬q.Inside (-1/10) (3/5)) :
    q.Inside (1/2) 1 := by
  have shallow : 17*q.s<5*q.c := by
    by_contra bad
    have steep : 5*q.c≤17*q.s := le_of_not_gt bad
    apply upper
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [forward.1,marker.2.1,forward.2.2.1,near.2.2.2,cp,sn,order,steep]
  have lower : -(7/20)*q.c+(7/20)*q.s≤q.loU := by
    apply le_of_not_gt
    intro own
    apply left
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [own,forward.2.1,forward.2.2.1,near.2.2.2,cp,sn,order]
  have short := shallow_projection q.c q.s cp sn q.unit_normal shallow.le
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [outer.1,cp]
  · linarith only [lower,side,short]
  · linarith only [marker.2.2.1,cp,order]
  · linarith only [near.2.2.2,sn]

private theorem right_support (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (lowU : q.loU+q.side≤q.c-(13/50)*t)
    (lowV : q.loV<t+(13/50)*q.c)
    (lowHighV : t+(13/50)*q.c<q.loV+q.side)
    (highLowU : q.loU<q.c-(4/5)*t)
    (highU : q.c-(4/5)*t<q.loU+q.side)
    (highV : q.loV+q.side≤t+(4/5)*q.c)
    (avoid : ∀ y : ℝ,13/50≤y → y≤4/5 → ¬q.Inside 1 y) :
    q.c*(q.loU+q.side)+t*(q.loV+q.side)≤1 := by
  let u0 := -(q.c-(13/50)*t)
  let v0 := -(t+(13/50)*q.c)
  let u1 := -(q.c-(4/5)*t)
  let v1 := -(t+(4/5)*q.c)
  have support := CommonCases.LowerSegmentSupport.support
    (-(q.loU+q.side)) (-q.loU) (-(q.loV+q.side)) (-q.loV) u0 v0 u1 v1
    (by dsimp [u0]; linarith only [lowU])
    (by dsimp [u1]; linarith only [highU])
    (by dsimp [u1]; linarith only [highLowU])
    (by dsimp [v0]; linarith only [lowHighV])
    (by dsimp [v0]; linarith only [lowV])
    (by dsimp [v1]; linarith only [highV])
    (by
      intro w wn wu own
      apply avoid ((1-w)*(13/50)+w*(4/5))
        (by linarith only [wn]) (by linarith only [wu])
      simp only [OpenSquare.Inside,InBands,signed,mul_one,neg_neg]
      dsimp [u0,v0,u1,v1] at own
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  dsimp [u0,v0,u1,v1] at support
  nlinarith only [support,unit]

private theorem northwest_negative_half (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (side : 1<q.side) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (marker : q.Inside (7/20) (7/20)) (forward : q.Inside 0 (13/50))
    (outer : q.Inside (2/5) 1) (near : q.Inside (13/50) 1)
    (origin : ¬q.Inside 0 1) (crosspoint : ¬q.Inside (1/2) 0)
    (upper : ¬q.Inside (-1/10) (3/5))
    (avoid : ∀ y : ℝ,13/50≤y → y≤4/5 → ¬q.Inside 1 y) :
    q.Inside (1/2) 1 := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds q.c t cp tn order unit
  have cu : q.c≤1 := bounds.2.1
  have cLow : 7/10<q.c := bounds.1
  have m := marker
  have f := forward
  have a := outer
  have g := near
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,mul_one,zero_add,add_zero]
    at m f a g origin crosspoint upper ⊢
  have lower : -t≤q.loU := by
    apply le_of_not_gt
    intro low
    apply origin
    refine ⟨low,?_,?_,?_⟩ <;>
      linarith only [g.2.1,m.2.2.1,a.2.2.2,cp,tn,order]
  by_contra missing
  have cap : q.loV+q.side≤t*(1/2)+q.c := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,high⟩ <;>
      linarith only [a.1,lower,side,cu,m.2.2.1,cp,tn]
  have upperU : q.loU+q.side≤q.c*(1/2) := by
    apply le_of_not_gt
    intro high
    apply crosspoint
    refine ⟨?_,high,?_,?_⟩ <;>
      linarith only [f.1,cap,side,cu,m.2.2.2,cp,tn,order]
  have span : 1<q.c/2+t := by linarith only [lower,upperU,side]
  have product := mul_pos (show 0<t-(1-q.c/2) by linarith only [span])
    (show 0<t+(1-q.c/2) by linarith only [tn,cu])
  have cHigh : q.c<4/5 := by
    by_contra bad
    have factor := mul_nonneg cp.le (show 0≤q.c-4/5 from sub_nonneg.mpr (le_of_not_gt bad))
    nlinarith only [product,unit,factor]
  have tLow : 3/5<t := by
    have square := mul_pos (sub_pos.mpr cHigh)
      (show 0<4/5+q.c by linarith only [cp])
    nlinarith only [unit,square,tn]
  have lowV : q.loV<t+(13/50)*q.c := by linarith only [f.2.2.1,tn]
  have lowHighV : t+(13/50)*q.c<q.loV+q.side := by
    linarith only [a.2.2.2,cp,order]
  have lowU : q.loU+q.side≤q.c-(13/50)*t := by
    apply le_of_not_gt
    intro high
    apply avoid (13/50) le_rfl (by norm_num)
    simp only [OpenSquare.Inside,InBands,signed,mul_one,neg_neg]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [f.1,cp,high,lowV,lowHighV]
  have highLowU : q.loU<q.c-(4/5)*t := by linarith only [f.1,cp,order]
  have highLowV : q.loV<t+(4/5)*q.c := by linarith only [m.2.2.1,cp,tn]
  have targetLow : q.loU< -(1/10)*q.c-(3/5)*t := by
    by_cases highU : q.c-(4/5)*t<q.loU+q.side
    · have highV : q.loV+q.side≤t+(4/5)*q.c := by
        apply le_of_not_gt
        intro high
        apply avoid (4/5) (by norm_num) le_rfl
        simp only [OpenSquare.Inside,InBands,signed,mul_one,neg_neg]
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [highLowU,highU,highLowV,high]
      have support := right_support q t signed lowU lowV lowHighV
        highLowU highU highV avoid
      have square : (q.c-1)^2≤9/100 := by
        have product := mul_nonneg (show 0≤q.c-7/10 by linarith only [cLow])
          (show 0≤1-q.c by linarith only [cu])
        nlinarith only [product,cLow]
      have cross : 21/50≤q.c*t := by
        have product := mul_nonneg (show 0≤q.c-7/10 by linarith only [cLow]) tn
        nlinarith only [product,tLow]
      have wide := mul_pos cp (sub_pos.mpr side)
      have top := mul_pos (show 0<t by linarith only [tLow])
        (show 0<q.loV+q.side-((2/5)*t+q.c) by linarith only [a.2.2.2])
      have multiplied : q.c*q.loU<q.c*(-(1/10)*q.c-(3/5)*t) := by
        nlinarith only [support,wide,top,unit,square,cross]
      exact (mul_lt_mul_left cp).mp multiplied
    · have endpoint : q.loU+q.side≤q.c-(4/5)*t := le_of_not_gt highU
      linarith only [endpoint,side,cHigh,tLow]
  apply upper
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [targetLow,f.2.1,f.2.2.1,g.2.2.2,cp,tn,order]

private theorem northwest_half_local (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (forward : q.Inside 0 (13/50))
    (outer : q.Inside (2/5) 1) (near : q.Inside (13/50) 1)
    (left : ¬q.Inside (-7/20) (7/20)) (origin : ¬q.Inside 0 1)
    (crosspoint : ¬q.Inside (1/2) 0) (upper : ¬q.Inside (-1/10) (3/5))
    (avoid : ∀ y : ℝ,13/50≤y → y≤4/5 → ¬q.Inside 1 y) :
    q.Inside (1/2) 1 := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have f := (same _ _).mpr forward
  have a := (same _ _).mpr outer
  have g := (same _ _).mpr near
  have u : ¬r.Inside (-1/10) (3/5) := fun own => upper ((same _ _).mp own)
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (northwest_positive_half r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m f a g
      (fun own => left ((same _ _).mp own)) u)
  · exact (same _ _).mp (northwest_negative_half r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) m f a g
      (fun own => origin ((same _ _).mp own))
      (fun own => crosspoint ((same _ _).mp own)) u
      (fun y low high own => avoid y low high ((same _ _).mp own)))

theorem northwest_halfpoint_of_northeast_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (origin : (owners p 7).Inside 2 3) :
    (owners p 8).Inside (3/2) 3 := by
  have h := fixed p hf
  have upper := northeast_upper_anchor _ (side p 7) h.northeastMarker origin
    (northeast_f7 p hf) (foreign p hf 7 3 (by decide) _ _ h.northeastCorner)
  have point := northwest_half_local ((pullX (owners p 8)).translated 2 2) (side p 8)
    (by norm_num [inside_translated_iff,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_translated_iff,inside_pullX]; exact northwest_forward p hf)
    (by norm_num [inside_translated_iff,inside_pullX]; exact (northwest_pair p hf).1)
    (by norm_num [inside_translated_iff,inside_pullX]; exact (northwest_pair p hf).2)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 7 (by decide) _ _ h.northeastMarker)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 7 (by decide) _ _ origin)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 5 (by decide) _ _ (southwest_west p hf))
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 7 (by decide) _ _ upper)
    (by
      intro y low high own
      have actual := (inside_translated_iff _ _ _ _ _).mp own
      rw [inside_pullX] at actual
      norm_num at actual
      exact foreign p hf 8 9 (by decide) _ _
        (left_bar p hf (2+y) (by linarith only [low]) (by linarith only [high])) actual)
  norm_num [inside_translated_iff,inside_pullX] at point
  exact point

theorem one_corner_of_northeast_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (origin : (owners p 7).Inside 2 3) :
    (owners p 1).Inside 1 1 := by
  by_contra missing
  exact left_missing_impossible p hf missing (northwest_halfpoint_of_northeast_origin p hf origin)

private theorem northwest_half_or_vertical_local (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (forward : q.Inside 0 (13/50))
    (outer : q.Inside (2/5) 1) (near : q.Inside (13/50) 1)
    (origin : ¬q.Inside 0 1) (crosspoint : ¬q.Inside (1/2) 0)
    (avoid : ∀ y : ℝ,13/50≤y → y≤4/5 → ¬q.Inside 1 y) :
    q.Inside (1/2) 1 ∨ (q.Inside 0 (2/5) ∧ q.Inside 0 (31/50)) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have f := (same _ _).mpr forward
  have a := (same _ _).mpr outer
  have g := (same _ _).mpr near
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using canonical
    have vertical : r.Inside 0 (2/5) ∧ r.Inside 0 (31/50) := by
      constructor <;> refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [f.1,m.2.1,f.2.2.1,g.2.2.2,cp,sign,order]
    exact Or.inr ⟨(same _ _).mp vertical.1,(same _ _).mp vertical.2⟩
  · have negative : r.s≤0 := (lt_of_not_ge sign).le
    have order : -r.s≤r.c := by simpa only [abs_of_nonpos negative] using canonical
    by_cases upper : r.Inside (-1/10) (3/5)
    · have vertical : r.Inside 0 (2/5) ∧ r.Inside 0 (31/50) := by
        constructor <;> refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [upper.1,f.2.1,f.2.2.1,g.2.2.2,cp,negative,order]
      exact Or.inr ⟨(same _ _).mp vertical.1,(same _ _).mp vertical.2⟩
    · exact Or.inl ((same _ _).mp (northwest_negative_half r (-r.s) (by ring)
        side' cp (by linarith only [negative]) order m f a g
        (fun own => origin ((same _ _).mp own))
        (fun own => crosspoint ((same _ _).mp own)) upper
        (fun y low high own => avoid y low high ((same _ _).mp own))))

/-- The complete orientation split supplies a real NW halfpoint or a
vertical segment long enough for the NE upper-point obstruction. -/
theorem northwest_half_or_vertical (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside (3/2) 3 ∨
      ((owners p 8).Inside 2 (12/5) ∧ (owners p 8).Inside 2 (131/50)) := by
  have h := fixed p hf
  have result := northwest_half_or_vertical_local
    ((pullX (owners p 8)).translated 2 2) (side p 8)
    (by norm_num [inside_translated_iff,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_translated_iff,inside_pullX]; exact northwest_forward p hf)
    (by norm_num [inside_translated_iff,inside_pullX]; exact (northwest_pair p hf).1)
    (by norm_num [inside_translated_iff,inside_pullX]; exact (northwest_pair p hf).2)
    (by norm_num [inside_translated_iff,inside_pullX]; exact northwest_missing_origin p hf)
    (by norm_num [inside_translated_iff,inside_pullX]
        exact foreign p hf 8 5 (by decide) _ _ (southwest_west p hf))
    (by
      intro y low high own
      have actual := (inside_translated_iff _ _ _ _ _).mp own
      rw [inside_pullX] at actual
      norm_num at actual
      exact foreign p hf 8 9 (by decide) _ _
        (left_bar p hf (2+y) (by linarith only [low]) (by linarith only [high])) actual)
  norm_num [inside_translated_iff,inside_pullX] at result
  exact result

end
#print axioms northwest_halfpoint_of_northeast_origin
#print axioms one_corner_of_northeast_origin
#print axioms northwest_half_or_vertical
end N12Compact.FiniteCases.C972
