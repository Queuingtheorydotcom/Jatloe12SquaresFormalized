import Compact.Geometry.ClosedFrames
import S12.ShortCluster.Projections
import Compact.Completion.OtherCases.C1091.OriginalData

/-! A direct C1091 entrance lemma. The merged marker owner is not
treated as an ordinary mask256 square. Its two actual markers and two
points strictly owned by Q0 force F0, for every orientation. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceMergedLow
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (far : ¬q.Inside (3/5) 0)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    q.Inside 0 (37/50) := by
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have lowV : -(3/5)*q.s≤q.loV := by
    apply le_of_not_gt
    intro h
    apply far
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,left.2.2.2,marker.2.1,cp,sn,h]
  have short := (short_projections q (37/50) (3/5) (by norm_num)).2.1
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [left.1,cp,sn]
  · linarith only [marker.2.1,cp,sn,order]
  · linarith only [marker.2.2.1,cp,sn]
  · linarith only [lowV,short,side]

private theorem nonpositive (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (far : ¬q.Inside (3/5) 0)
    (cp : 0<q.c) (sn : q.s≤0) : q.Inside 0 (37/50) := by
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have upperU : q.loU+q.side≤(3/5)*q.c := by
    apply le_of_not_gt
    intro h
    apply far
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,left.2.2.1,marker.2.2.2,cp,sn,h]
  have short := (short_projections q (3/5) (-(37/50)) (by norm_num)).2.1
  have lowerU : q.loU<(37/50)*q.s := by
    linarith only [upperU,short,side]
  have upperV : (37/50)*q.c<q.loV+q.side := by
    by_contra failure
    have high : q.loV+q.side≤(37/50)*q.c := le_of_not_gt failure
    have cosine : q.c≤1 := by
      have bound := (short_projections q 1 0 (by norm_num)).2.1
      simpa only [mul_one,mul_zero,add_zero] using bound
    apply near
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [left.1,cp]
    · linarith only [marker.2.1,marker.2.2.2,high,cp]
    · linarith only [high,cosine,side,sn]
    · linarith only [marker.2.2.2,cp,sn]
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_comm] using lowerU
  · linarith only [marker.2.1,cp,sn]
  · linarith only [left.2.2.1,cp,sn]
  · simpa only [mul_comm] using upperV

/-- Every frame, including axial and diagonal ties, retains the same
physical merged square. Omissions are weak and no side cap is used. -/
theorem point (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (far : ¬q.Inside (3/5) 0) :
    q.Inside 0 (37/50) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have rs : 1<r.side := by simpa only [shape] using side
  have rl := (same _ _).mpr left
  have rm := (same _ _).mpr marker
  have rn : ¬r.Inside (3/25) 0 := fun own => near ((same _ _).mp own)
  have rf : ¬r.Inside (3/5) 0 := fun own => far ((same _ _).mp own)
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact positive r rs rl rm rf cp sign (abs_le.mp range).2
  · exact nonpositive r rs rl rm rn rf cp (le_of_not_ge sign)

theorem original (p : NormalizedPacking)
    (hf : codedMarkerFamily p=OriginalData.family) :
    (OriginalData.owners p 4).Inside 1 (87/50) := by
  let q := OriginalData.owners p 4
  have markers := OriginalData.merged_markers p hf
  have near := OriginalData.seed p hf 0 (28/25,1) (by decide +kernel)
  have far := OriginalData.seed p hf 0 (87/50,1) (by decide +kernel)
  norm_num at near far
  have middle : (OriginalData.owners p 0).Inside (8/5) 1 :=
    CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ near far
      (by norm_num) (by norm_num) (by norm_num)
  have missingNear : ¬q.Inside (28/25) 1 :=
    fun own => OriginalData.apart p hf 4 0 (by decide) _ _ ⟨own,near⟩
  have missingMiddle : ¬q.Inside (8/5) 1 :=
    fun own => OriginalData.apart p hf 4 0 (by decide) _ _ ⟨own,middle⟩
  have localLeft : (q.translated 1 1).Inside (-(43/500)) 0 := by
    norm_num only [inside_translated_iff]
    exact markers.1
  have localMarker : (q.translated 1 1).Inside (13/20) (13/20) := by
    norm_num only [inside_translated_iff]
    exact markers.2
  have localNear : ¬(q.translated 1 1).Inside (3/25) 0 := by
    norm_num only [inside_translated_iff]
    exact missingNear
  have localFar : ¬(q.translated 1 1).Inside (3/5) 0 := by
    norm_num only [inside_translated_iff]
    exact missingMiddle
  have result := point (q.translated 1 1) (OriginalData.side p 4)
    localLeft localMarker localNear localFar
  norm_num only [inside_translated_iff] at result
  exact result

#print axioms point
#print axioms original

/-- The actual left-wall marker rules out the other signed canonical
sector even without knowing which square owns the inner corner. -/
private theorem nonpositive_wall_impossible (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c) : False := by
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have upperU : q.loU+q.side≤(3/25)*q.c := by
    apply le_of_not_gt
    intro high
    apply near
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,left.2.2.1,marker.2.2.2,cp,sn,high]
  have lowerU : -(43/500)*q.c+q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply wall
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.2.1,left.2.2.1,marker.2.1,marker.2.2.2,
        upperU,cp,sn,low]
  have short := (short_projections q (603/1000) (-(603/1000)) (by norm_num)).2.1
  linarith only [lowerU,upperU,short,order,side]

private theorem positive_profile (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    -(3/25)*q.s≤q.loV ∧ 2*q.s<q.c := by
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have lowerV : -(3/25)*q.s≤q.loV := by
    apply le_of_not_gt
    intro low
    apply near
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,left.2.2.2,marker.2.1,cp,sn,low]
  have upperV : q.loV+q.side≤q.c+(43/500)*q.s := by
    apply le_of_not_gt
    intro high
    apply wall
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,left.2.2.1,marker.2.1,cp,sn,order,high]
  have necessary : 1<q.c+(103/500)*q.s := by
    linarith only [lowerV,upperV,side]
  have slope : 2*q.s<q.c := by
    by_contra failure
    have large : q.c≤2*q.s := le_of_not_gt failure
    have sp : 0<q.s := by linarith only [cp,large]
    have margin : 0<(1-(103/500:ℝ)^2)*q.s-(206/500)*q.c := by
      linarith only [cp,large]
    have product := mul_pos sp margin
    have square : 1<(q.c+(103/500)*q.s)^2 := by
      nlinarith only [necessary,sq_nonneg (q.c+(103/500)*q.s-1)]
    nlinarith only [q.unit_normal,product,square]
  exact ⟨lowerV,slope⟩

private theorem positive_inner (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    q.Inside (23/50) (99/100) := by
  have profile := positive_profile q side left marker near wall cp sn order
  have lowerV := profile.1
  have slope := profile.2
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have cosine : q.c≤1 := by
    have bound := (short_projections q 1 0 (by norm_num)).2.1
    simpa only [mul_one,mul_zero,add_zero] using bound
  simp only [OpenSquare.Inside,InBands]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [left.1,cp,sn]
  · linarith only [marker.2.1,slope,cp]
  · linarith only [left.2.2.1,slope,cp]
  · linarith only [lowerV,side,cosine,sn]

/-- A compact five-point implication. The two merged anchors and the
actual singleton/left-wall omissions force the inward duplicate point.
Unlike the sharper halfpoint lemma, this needs no omitted inner corner. -/
theorem inner (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1) :
    q.Inside (23/50) (99/100) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have rs : 1<r.side := by simpa only [shape] using side
  have rl := (same _ _).mpr left
  have rm := (same _ _).mpr marker
  have rn : ¬r.Inside (3/25) 0 := fun own => near ((same _ _).mp own)
  have rw : ¬r.Inside (-(43/500)) 1 := fun own => wall ((same _ _).mp own)
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact positive_inner r rs rl rm rn rw cp sign (abs_le.mp range).2
  · exact False.elim (nonpositive_wall_impossible r rs rl rm rn rw cp
      (le_of_not_ge sign) (by linarith only [(abs_le.mp range).1]))

theorem inner_original (p : NormalizedPacking)
    (hf : codedMarkerFamily p=OriginalData.family) :
    (OriginalData.owners p 4).Inside (73/50) (199/100) := by
  let q := OriginalData.owners p 4
  have markers := OriginalData.merged_markers p hf
  have near := OriginalData.seed p hf 0 (28/25,1) (by decide +kernel)
  have wall := OriginalData.seed p hf 8 (457/500,2) (by decide +kernel)
  norm_num at near wall
  have localLeft : (q.translated 1 1).Inside (-(43/500)) 0 := by
    norm_num only [inside_translated_iff]; exact markers.1
  have localMarker : (q.translated 1 1).Inside (13/20) (13/20) := by
    norm_num only [inside_translated_iff]; exact markers.2
  have localNear : ¬(q.translated 1 1).Inside (3/25) 0 := by
    norm_num only [inside_translated_iff]
    exact fun own => OriginalData.apart p hf 4 0 (by decide) _ _ ⟨own,near⟩
  have localWall : ¬(q.translated 1 1).Inside (-(43/500)) 1 := by
    norm_num only [inside_translated_iff]
    exact fun own => OriginalData.apart p hf 4 8 (by decide) _ _ ⟨own,wall⟩
  have result := inner (q.translated 1 1) (OriginalData.side p 4)
    localLeft localMarker localNear localWall
  norm_num only [inside_translated_iff] at result
  exact result

#print axioms inner
#print axioms inner_original

private theorem positive_alternative (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    q.Inside (1/2) 1 ∨ q.Inside (23/50) (101/100) := by
  have profile := positive_profile q side left marker near wall cp sn order
  have lowerV := profile.1
  have slope := profile.2
  have cosine : q.c≤1 := by
    have bound := (short_projections q 1 0 (by norm_num)).2.1
    simpa only [mul_one,mul_zero,add_zero] using bound
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  by_cases steep : q.c≤34*q.s
  · right
    simp only [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [left.1,cp,sn]
    · linarith only [marker.2.1,slope,cp]
    · linarith only [left.2.2.1,slope,cp]
    · linarith only [lowerV,side,cosine,steep]
  · left
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [left.1,cp,sn]
    · linarith only [marker.2.1,steep,cp]
    · linarith only [left.2.2.1,slope,cp]
    · linarith only [lowerV,side,cosine,sn]

/-- The two exact targets used by the mixed-sign sector. The upper
target has y=1.01, not .99: reflection of the strong inward theorem
really puts its point above the central horizontal line. -/
theorem alternative (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (-(43/500)) 0)
    (marker : q.Inside (13/20) (13/20))
    (near : ¬q.Inside (3/25) 0) (wall : ¬q.Inside (-(43/500)) 1) :
    q.Inside (1/2) 1 ∨ q.Inside (23/50) (101/100) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have rs : 1<r.side := by simpa only [shape] using side
  have rl := (same _ _).mpr left
  have rm := (same _ _).mpr marker
  have rn : ¬r.Inside (3/25) 0 := fun own => near ((same _ _).mp own)
  have rw : ¬r.Inside (-(43/500)) 1 := fun own => wall ((same _ _).mp own)
  by_cases sign : 0≤r.s
  · rcases positive_alternative r rs rl rm rn rw cp sign (abs_le.mp range).2 with own|own
    · exact Or.inl ((same _ _).mp own)
    · exact Or.inr ((same _ _).mp own)
  · exact False.elim (nonpositive_wall_impossible r rs rl rm rn rw cp
      (le_of_not_ge sign) (by linarith only [(abs_le.mp range).1]))

theorem alternative_original (p : NormalizedPacking)
    (hf : codedMarkerFamily p=OriginalData.family) :
    (OriginalData.owners p 4).Inside (3/2) 2 ∨
      (OriginalData.owners p 4).Inside (73/50) (201/100) := by
  let q := OriginalData.owners p 4
  have markers := OriginalData.merged_markers p hf
  have near := OriginalData.seed p hf 0 (28/25,1) (by decide +kernel)
  have wall := OriginalData.seed p hf 8 (457/500,2) (by decide +kernel)
  norm_num at near wall
  have localLeft : (q.translated 1 1).Inside (-(43/500)) 0 := by
    norm_num only [inside_translated_iff]; exact markers.1
  have localMarker : (q.translated 1 1).Inside (13/20) (13/20) := by
    norm_num only [inside_translated_iff]; exact markers.2
  have localNear : ¬(q.translated 1 1).Inside (3/25) 0 := by
    norm_num only [inside_translated_iff]
    exact fun own => OriginalData.apart p hf 4 0 (by decide) _ _ ⟨own,near⟩
  have localWall : ¬(q.translated 1 1).Inside (-(43/500)) 1 := by
    norm_num only [inside_translated_iff]
    exact fun own => OriginalData.apart p hf 4 8 (by decide) _ _ ⟨own,wall⟩
  have result := alternative (q.translated 1 1) (OriginalData.side p 4)
    localLeft localMarker localNear localWall
  norm_num only [inside_translated_iff] at result
  exact result

#print axioms alternative_original
end N12Compact.Completion.OtherCases.C1091.EntranceMergedLow
