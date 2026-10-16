import Compact.Geometry.ClosedFrames
import Compact.Completion.OtherCases.DerivedWalls
import Compact.Completion.OtherCases.MergedTopScalars

/-! The full merged-top obstruction uses the actual excluded segment.
In the negative sector that segment becomes a derived supporting line;
the two remaining marker bands follow from exact circle margins. -/
namespace N12Compact.Completion.OtherCases.MergedTopExclusion
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive (q : OpenSquare) (cp : 0<q.c)
    (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (33/20) (33/20)) (top : q.Inside (8/5) 3)
    (missingNE : ¬q.Inside (47/20) (47/20))
    (missingLeft : ¬q.Inside 1 (12/5)) : False := by
  have nLowU : q.loU<q.c*(47/20)+q.s*(47/20) := by
    linarith only [marker.1,cp,sn]
  have nLowV : q.loV< -q.s*(47/20)+q.c*(47/20) := by
    linarith only [marker.2.2.1,order]
  have nHighV : -q.s*(47/20)+q.c*(47/20)<q.loV+q.side := by
    linarith only [top.2.2.2,cp,sn]
  have nFace : q.loU+q.side≤q.c*(47/20)+q.s*(47/20) :=
    le_of_not_gt (fun h => missingNE ⟨nLowU,h,nLowV,nHighV⟩)
  have lHighU : q.c+q.s*(12/5)<q.loU+q.side := by
    linarith only [top.2.1,cp,sn]
  have lLowV : q.loV< -q.s+q.c*(12/5) := by
    linarith only [marker.2.2.1,cp,sn]
  have lHighV : -q.s+q.c*(12/5)<q.loV+q.side := by
    linarith only [top.2.2.2,order]
  have lFace : q.c+q.s*(12/5)≤q.loU := by
    apply le_of_not_gt
    intro h
    exact missingLeft (by
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro h (And.intro lHighU (And.intro lLowV lHighV)))
  linarith only [nFace,lFace,marker.2.2.1,top.2.2.2,sn]

private theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (side : 1<q.side) (cap : q.side≤1001/1000)
    (marker : q.Inside (33/20) (33/20)) (top : q.Inside (8/5) 3)
    (missingNE : ¬q.Inside (47/20) (47/20))
    (avoid : ∀ y : ℝ,113/50≤y → y≤12/5 → ¬q.Inside 1 y) : False := by
  have p := marker
  have h := top
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul,sub_eq_add_neg] at p h
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have span : (27/20)*q.c-(1/20)*t<1001/1000 := by
    linarith only [p.2.2.1,h.2.2.2,cap]
  have data := MergedTopScalars.steep_data q.c t cp tn order unit span
  have tp : 0<t := by linarith only [data.2.1]
  have lHighU : q.c-t*(12/5)<q.loU+q.side := by
    linarith only [p.2.1,cp,tn]
  have lLowV : q.loV<t+q.c*(12/5) := by
    linarith only [p.2.2.1,order,cp]
  have lHighV : t+q.c*(12/5)<q.loV+q.side := by
    linarith only [h.2.2.2,cp,tn]
  have uFace : q.c-t*(12/5)≤q.loU := by
    apply le_of_not_gt
    intro low
    exact avoid (12/5) (by norm_num) le_rfl (by
      simpa only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul,sub_eq_add_neg,mul_one] using
        And.intro low (And.intro lHighU (And.intro lLowV lHighV)))
  have jLowU : q.loU<q.c-t*(113/50) := by
    linarith only [h.1,data.1,cp]
  have jHighU : q.c-t*(113/50)<q.loU+q.side := by
    linarith only [p.2.1,cp,tn]
  have jHighV : t+q.c*(113/50)<q.loV+q.side := by
    linarith only [h.2.2.2,cp,tn]
  have vFace : t+q.c*(113/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    exact avoid (113/50) le_rfl (by norm_num) (by
      simpa only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul,sub_eq_add_neg,mul_one] using
        And.intro jLowU (And.intro jHighU (And.intro low jHighV)))
  have forbiddenLine : ∀ y : ℝ,¬q.Inside 1 y := by
    intro y own
    have point := own
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul,sub_eq_add_neg,mul_one] at point
    have low : 113/50<y := by
      apply (mul_lt_mul_iff_right₀ cp).mp
      linarith only [point.2.2.1,vFace]
    have high : y<12/5 := by
      apply (mul_lt_mul_iff_right₀ tp).mp
      nlinarith only [point.1,uFace]
    exact avoid y low.le high.le own
  have wall := DerivedWalls.vertical_right q (33/20) (33/20) 1 marker
    (by norm_num) forbiddenLine
  let X := q.c*q.loU+t*q.loV
  let Y := -t*q.loU+q.c*q.loV
  have closed : ClosedInside q X Y := by
    have point := WallProfile.vertex q q.loU q.loV
      ⟨le_rfl,by linarith only [q.side_pos]⟩
      ⟨le_rfl,by linarith only [q.side_pos]⟩
    rw [signed] at point
    convert point using 1 <;> dsimp only [X,Y] <;> ring
  have closedWall := DerivedWalls.closed_affine_bound q 1 0 1 (33/20) (33/20)
    (by
      intro x y own
      simpa only [one_mul,zero_mul,add_zero] using wall x y own)
    marker X Y closed
  have support : 1≤q.c*q.loU+t*q.loV := by
    simpa only [one_mul,zero_mul,add_zero,X] using closedWall
  have uMargin := MergedTopScalars.u_margin q.c t data.2.2.2.1 data.2.2.2.2
    data.2.1.le data.2.2.1.le unit
  have vMargin := MergedTopScalars.v_margin q.c t data.2.2.2.1
    data.2.1.le data.2.2.1.le
  have nLowU : q.loU<q.c*(47/20)-t*(47/20) := by
    linarith only [p.1,order]
  have nLowV : q.loV<t*(47/20)+q.c*(47/20) := by
    linarith only [p.2.2.1,cp,tn]
  have nHighU : q.c*(47/20)-t*(47/20)<q.loU+q.side := by
    by_contra bad
    have upper := mul_nonneg cp.le (sub_nonneg.mpr (le_of_not_gt bad))
    have strict := mul_pos tp (sub_pos.mpr p.2.2.1)
    have extra := mul_pos cp (sub_pos.mpr side)
    nlinarith only [support,upper,strict,extra,uMargin,unit]
  have nHighV : t*(47/20)+q.c*(47/20)<q.loV+q.side := by
    by_contra bad
    have upper := mul_nonneg tp.le (sub_nonneg.mpr (le_of_not_gt bad))
    have strict := mul_pos cp (sub_pos.mpr h.1)
    have extra := mul_pos tp (sub_pos.mpr side)
    nlinarith only [support,upper,strict,extra,vMargin,unit]
  apply missingNE
  simpa only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul,sub_eq_add_neg] using
    And.intro nLowU (And.intro nHighU (And.intro nLowV nHighV))

/-- Complete continuous obstruction with only two strict anchors, the
opposite marker exclusion, and the genuine foreign vertical segment. -/
theorem impossible (q : OpenSquare) (side : 1<q.side) (cap : q.side≤1001/1000)
    (marker : q.Inside (33/20) (33/20)) (top : q.Inside (8/5) 3)
    (missingNE : ¬q.Inside (47/20) (47/20))
    (avoid : ∀ y : ℝ,113/50≤y → y≤12/5 → ¬q.Inside 1 y) : False := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have marker' := (same _ _).mpr marker
  have top' := (same _ _).mpr top
  have missing' : ¬r.Inside (47/20) (47/20) :=
    fun h => missingNE ((same _ _).mp h)
  have avoid' : ∀ y : ℝ,113/50≤y → y≤12/5 → ¬r.Inside 1 y :=
    fun y low high h => avoid y low high ((same _ _).mp h)
  have bounds := abs_le.mp range
  by_cases sign : 0≤r.s
  · exact positive r cp sign bounds.2 marker' top' missing'
      (avoid' (12/5) (by norm_num) le_rfl)
  · exact negative r (-r.s) (by ring) cp (by linarith only [sign])
      (by linarith only [bounds.1]) (by simpa only [shape] using side)
      (by simpa only [shape] using cap) marker' top' missing' avoid'

#print axioms impossible
end N12Compact.Completion.OtherCases.MergedTopExclusion

