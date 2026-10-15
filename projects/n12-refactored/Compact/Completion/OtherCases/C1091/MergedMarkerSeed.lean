import Compact.Geometry.ClosedFrames
import S12.ShortCluster.Projections
import S12.Diagonal

/-! The local theorem in C1091-merged-marker-seed.md. Both original
markers remain strict in one square. The two omissions are weak, and
canonicalization changes only that square's face labels. This source
translation has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  left : q.Inside (-(43/500)) 0
  marker : q.Inside (13/20) (13/20)
  origin : ¬q.Inside 0 0
  upper : ¬q.Inside (37/50) 1

theorem Input.reframe {q r : OpenSquare} (h : Input q)
    (shape : r.side=q.side) (same : ∀ x y,r.Inside x y↔q.Inside x y) : Input r where
  side := by simpa only [shape] using h.side
  left := (same _ _).mpr h.left
  marker := (same _ _).mpr h.marker
  origin := fun own => h.origin ((same _ _).mp own)
  upper := fun own => h.upper ((same _ _).mp own)

/-- The nonpositive canonical sign would put the origin strictly
between the two anchors in both face coordinates, even at a sign tie. -/
theorem nonpositive_impossible (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c) : False := by
  have left := h.left
  have marker := h.marker
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  apply h.origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [left.1,left.2.2.1,marker.2.1,marker.2.2.2,cp,sn,order]

/-- The omitted origin and upper point select the actual lower V-face
and upper U-face. No face choice is an additional premise. -/
theorem positive_faces (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    0<q.s ∧ 0≤q.loV ∧ q.loU+q.side≤(37/50)*q.c+q.s := by
  have left := h.left
  have marker := h.marker
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  have lowerV : 0≤q.loV := by
    apply le_of_not_gt
    intro low
    apply h.origin
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
    refine ⟨?_,?_,low,?_⟩ <;>
      linarith only [left.1,left.2.2.2,marker.2.1,cp,sn]
  have sp : 0<q.s := by linarith only [lowerV,left.2.2.1]
  have cosine : q.c≤1 := by
    have bound := (short_projections q 1 0 (by norm_num)).2.1
    simpa only [mul_one,mul_zero,add_zero] using bound
  have upperU : q.loU+q.side≤(37/50)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply h.upper
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [left.1,marker.2.2.1,high,lowerV,h.side,cosine,cp,sn,order]
  exact ⟨sp,lowerV,upperU⟩

/-- The target's four strict bands use the two actual face bounds and
the exact squared norms .9773 and .8145, both less than one. -/
theorem positive_point (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    q.Inside (-(6/25)) (87/100) := by
  obtain ⟨_,lowerV,upperU⟩ := positive_faces q h cp sn order
  have shortU := (short_projections q (49/50) (13/100) (by norm_num)).2.1
  have shortV := (short_projections q (-(6/25)) (87/100) (by norm_num)).2.2.2
  have left := h.left
  have marker := h.marker
  simp only [OpenSquare.Inside,InBands,mul_zero,add_zero] at left marker
  simp only [OpenSquare.Inside,InBands]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [upperU,shortU,h.side]
  · linarith only [marker.2.1,cp,order]
  · linarith only [left.2.2.1,cp,sn]
  · linarith only [lowerV,shortV,h.side]

/-- Full arbitrary-angle local conclusion, including axial and diagonal
canonical representatives and boundary contact at either omitted point. -/
theorem point (q : OpenSquare) (h : Input q) : q.Inside (-(6/25)) (87/100) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe shape same
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (positive_point r data cp sign
      (by simpa only [abs_of_nonneg sign] using range))
  · exact False.elim (nonpositive_impossible r data cp (le_of_not_ge sign)
      (by linarith only [(abs_le.mp range).1]))

/-- Original coordinates: the merged square owns both (.914,1) and
(1.65,1.65). Neither marker is declared absent or treated as a singleton. -/
theorem point_original (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside (457/500) 1) (marker : q.Inside (33/20) (33/20))
    (origin : ¬q.Inside 1 1) (upper : ¬q.Inside (87/50) 2) :
    q.Inside (19/25) (187/100) := by
  have data : Input (q.translated 1 1) where
    side := side
    left := by norm_num only [inside_translated_iff]; exact left
    marker := by norm_num only [inside_translated_iff]; exact marker
    origin := by norm_num only [inside_translated_iff]; exact origin
    upper := by norm_num only [inside_translated_iff]; exact upper
  have target := point (q.translated 1 1) data
  norm_num only [inside_translated_iff] at target
  exact target

#print axioms point
#print axioms point_original
end N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed
