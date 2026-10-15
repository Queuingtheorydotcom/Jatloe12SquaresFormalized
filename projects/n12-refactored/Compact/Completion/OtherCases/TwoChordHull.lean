import Compact.Completion.OtherCases.TwoChordFaces
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.SegmentCorner

/-! Two genuine short chords force three strict points on the far side.
The additional excluded segment removes the opposite canonical sign
through the exact ordering of its two face crossings. -/
namespace N12Compact.Completion.OtherCases.TwoChordHull
open S12 S12Pilot
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (north : q.Inside (7/20) (7/20)) (faces : TwoChordFaces.Faces q)
    (x y : ℝ) (xLow : 7/20≤x) (yLow : 0≤y) (yHigh : y<7/20)
    (sumLarge : 7/10<x+y) (ySmall : y≤13/50)
    (vOrder : 13/50-y≤x) (vSmall : (x+13/50-y)*(99/140)<1)
    (derivative : (y+13/50)*(325/397)≤x*(228/397))
    (uSmall : x*(325/397)+(y+13/50)*(228/397)<1) : q.Inside x y := by
  have projection := CommonCases.CanonicalProjection.after q.c q.s (325/397) (228/397)
    x (y+13/50) q.unit_normal (by norm_num) faces.cutoff.le derivative
    (by
      have first := mul_nonneg (show 0≤x by linarith only [xLow]) (by norm_num : (0:ℝ)≤325/397)
      have last := mul_nonneg (show 0≤y+13/50 by linarith only [yLow])
        (by norm_num : (0:ℝ)≤228/397)
      linarith only [first,last])
  have upperU : x*q.c+(y+13/50)*q.s<1 := by linarith only [projection,uSmall]
  have lowerV := CommonCases.OutwardScalars.increasing_projection q.c q.s (13/50-y) x
    cp sn order q.unit_normal (by linarith only [ySmall]) vOrder
    (by linarith only [vSmall])
  have first := mul_pos cp (show 0<x+y-7/10 by linarith only [sumLarge])
  have last := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤7/20-y by linarith only [yHigh])
  have vFirst := mul_pos cp (show 0<7/20-y by linarith only [yHigh])
  have vLast := mul_nonneg sn (sub_nonneg.mpr xLow)
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [north.1,first,last]
  · linarith only [faces.lowerU,side,upperU]
  · linarith only [faces.upperV,side,lowerV]
  · nlinarith only [north.2.2.2,vFirst,vLast]

private theorem positive_points (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (north : q.Inside (7/20) (7/20)) (faces : TwoChordFaces.Faces q) :
    q.Inside (51/50) 0 ∧ q.Inside (51/50) (1/50) ∧ q.Inside (24/25) (11/100) := by
  refine ⟨positive_point q side cp sn order north faces (51/50) 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    positive_point q side cp sn order north faces (51/50) (1/50) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    positive_point q side cp sn order north faces (24/25) (11/100) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals norm_num

private theorem negative_segment_impossible (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (south : q.Inside (7/20) (-7/20)) (north : q.Inside (7/20) (7/20))
    (faces : TwoChordFaces.Faces q)
    (avoid : ∀ z : ℝ,0≤z → z≤1 →
      ¬q.Inside ((1-z)*(543/500)+z) (-(z*(13/50)))) : False := by
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have cu := bounds.2.1
  have b0Outside := avoid 0 (by norm_num) (by norm_num)
  norm_num at b0Outside
  have b0LowU : q.loU<q.c*(543/500) := by linarith only [south.1,cp,sn]
  have b0HighV : -q.s*(543/500)<q.loV+q.side := by
    linarith only [north.2.2.2,cp,sn]
  have short := CommonCases.OutwardScalars.increasing_projection q.c q.s (13/50) (543/500)
    cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
  have b0LowV : q.loV< -q.s*(543/500) := by
    linarith only [faces.upperV,short,side]
  have b0Face : q.loU+q.side≤q.c*(543/500) := by
    apply le_of_not_gt
    intro high
    exact b0Outside (by
      simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
        And.intro b0LowU (And.intro high (And.intro b0LowV b0HighV)))
  have b1LowU : q.loU<q.c-q.s*(13/50) := by
    linarith only [north.1,cp,order]
  have b1HighU : q.c-q.s*(13/50)<q.loU+q.side := by
    linarith only [faces.lowerU,side,cu]
  have crossing := SegmentCorner.crossing_order
    (-(q.loU+q.side)) (-q.loU) (-(q.loV+q.side)) (-q.loV)
    (-(q.c*(543/500))) (q.s*(543/500))
    (-(q.c-q.s*(13/50))) (q.s+q.c*(13/50))
    (by linarith only [b0Face]) (by linarith only [b1HighU])
    (by linarith only [b1LowU]) (by linarith only [b0HighV])
    (by linarith only [b0LowV]) (by linarith only [faces.lowerV])
    (by
      intro z low high point
      apply avoid z low high
      refine ⟨?_,?_,?_,?_⟩
      · nlinarith only [point.2.1]
      · nlinarith only [point.1]
      · nlinarith only [point.2.2.2]
      · nlinarith only [point.2.2.1])
  have crossBound :
      ((13/50)*q.c-(43/500)*q.s)*(q.loU+q.side)-
        ((13/50)*q.s+(43/500)*q.c)*q.loV≤(13/50)*(543/500) := by
    nlinarith only [crossing,q.unit_normal]
  have alpha : 0<(13/50)*q.c-(43/500)*q.s := by linarith only [order,cp]
  have beta : 0<(13/50)*q.s+(43/500)*q.c := by linarith only [cp,sn]
  have first := mul_nonneg alpha.le (show 0≤q.loU+(13/50)*q.s by
    linarith only [faces.lowerU])
  have last := mul_nonneg beta.le (show 0≤(13/50)*q.c-(q.loV+q.side) by
    linarith only [faces.upperV])
  have extra := mul_pos (sub_pos.mpr side) (show
      0<(13/50+43/500)*q.c+(13/50-43/500)*q.s by linarith only [cp,sn])
  have remainder := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤1-(13/50)*(q.c+q.s) by linarith only [bounds.2.2.2.1])
  have sineLarge : 12/25<q.s := by linarith only [faces.span,cu]
  have product := mul_pos (show 0<q.c-7/10 by linarith only [bounds.1]) faces.sinePositive
  have crossLarge : 43/500<(7/25)*q.c*q.s := by
    nlinarith only [sineLarge,product]
  nlinarith only [crossBound,first,last,extra,remainder,crossLarge,
    bounds.2.2.2.2,q.unit_normal]

/-- Complete Theorem6 of OTHER-GEOMETRY: four actual chord exclusions and
the one genuine segment force all three strict hull points, at every angle. -/
theorem points (q : OpenSquare) (side : 1<q.side)
    (south : q.Inside (7/20) (-7/20)) (north : q.Inside (7/20) (7/20))
    (missingF : ¬q.Inside 0 (-13/50)) (missingH : ¬q.Inside 0 (13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingG : ¬q.Inside 1 (13/50))
    (avoid : ∀ z : ℝ,0≤z → z≤1 →
      ¬q.Inside ((1-z)*(543/500)+z) (z*(13/50))) :
    q.Inside (51/50) 0 ∧ q.Inside (51/50) (1/50) ∧ q.Inside (24/25) (11/100) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have p := (same _ _).mpr south
  have n := (same _ _).mpr north
  have f : ¬r.Inside 0 (-13/50) := fun h => missingF ((same _ _).mp h)
  have h : ¬r.Inside 0 (13/50) := fun h => missingH ((same _ _).mp h)
  have j : ¬r.Inside 1 (-13/50) := fun h => missingJ ((same _ _).mp h)
  have g : ¬r.Inside 1 (13/50) := fun h => missingG ((same _ _).mp h)
  have avoid' : ∀ z : ℝ,0≤z → z≤1 →
      ¬r.Inside ((1-z)*(543/500)+z) (z*(13/50)) :=
    fun z low high own => avoid z low high ((same _ _).mp own)
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := (abs_le.mp range).2
    have faces := TwoChordFaces.positive r side' cp sign order p n f h j g
    have result := positive_points r side' cp sign order n faces
    exact ⟨(same _ _).mp result.1,(same _ _).mp result.2.1,(same _ _).mp result.2.2⟩
  · exfalso
    let reflected := pullY (r.translated 0 (-4))
    have cp' : 0<reflected.c := cp
    have sn : 0≤reflected.s := by change 0≤ -r.s; linarith only [sign]
    have order : reflected.s≤reflected.c := by
      change -r.s≤r.c
      linarith only [(abs_le.mp range).1]
    have p' : reflected.Inside (7/20) (-7/20) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      exact n
    have n' : reflected.Inside (7/20) (7/20) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      simpa only [neg_div] using p
    have f' : ¬reflected.Inside 0 (-13/50) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      exact h
    have h' : ¬reflected.Inside 0 (13/50) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      simpa only [neg_div] using f
    have j' : ¬reflected.Inside 1 (-13/50) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      exact g
    have g' : ¬reflected.Inside 1 (13/50) := by
      norm_num [reflected,inside_pullY,inside_translated_iff]
      simpa only [neg_div] using j
    have faces := TwoChordFaces.positive reflected side' cp' sn order p' n' f' h' j' g'
    apply negative_segment_impossible reflected side' cp' sn order p' n' faces
    intro z low high own
    apply avoid' z low high
    have back := own
    change (pullY (r.translated 0 (-4))).Inside _ _ at back
    rw [inside_pullY,inside_translated_iff] at back
    convert back using 1 <;> ring

#print axioms points
end N12Compact.Completion.OtherCases.TwoChordHull

