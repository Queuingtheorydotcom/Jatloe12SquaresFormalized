import Compact.Completion.OtherCases.InnerCornerObstruction.Faces

/-! The complete four-isolated-exclusion obstruction and its original
inner-corner corollary. No foreign segment, wall or common side is needed.
This is uncompiled source for INNER-CORNER-FOUR-EXCLUSIONS.md. -/
namespace N12Compact.Completion.OtherCases.InnerCornerObstruction
open S12 S12Pilot
set_option Elab.async false

theorem positive_four_impossible (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (missingFar : ¬q.Inside (1/2) 1) : False := by
  obtain ⟨lowerU,lowerV⟩ := positive_faces q h cp sn order
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have o := h.origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add] at o
  have m := h.marker
  have fLowerU : q.loU<q.c/2+q.s := by linarith only [o.1,cp,sn]
  have fLowerV : q.loV<q.c-q.s/2 := by linarith only [m.2.2.1,cp,sn]
  have fUpperV : q.c-q.s/2<q.loV+q.side := by
    linarith only [lowerV,h.side,cu,sn]
  have upperU : q.loU+q.side≤q.c/2+q.s := by
    apply le_of_not_gt
    intro high
    apply missingFar
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowerU,high,fLowerV,fUpperV]
  have steep : q.c<2*q.s := by
    apply lt_of_not_ge
    intro shallow
    have short := OrdinaryBarCrosspoint.Scalars.before_half q.c q.s cp sn
      q.unit_normal shallow
    linarith only [upperU,lowerU,h.side,short]
  have rLowerU : q.loU< -(43/500)*q.c+q.s := by
    linarith only [o.1,steep,cp]
  have rUpperU : -(43/500)*q.c+q.s<q.loU+q.side := by
    linarith only [m.2.1,cp,order]
  have rLowerV : q.loV<(43/500)*q.s+q.c := by
    linarith only [m.2.2.1,cp,sn]
  have upperV : q.loV+q.side≤(43/500)*q.s+q.c := by
    apply le_of_not_gt
    intro high
    apply h.missingUpper
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowerU,rUpperU,rLowerV,high]
  have short := OrdinaryBarCrosspoint.Scalars.after_half q.c q.s cp sn
    q.unit_normal steep.le
  linarith only [lowerV,upperV,h.side,short]

theorem four_impossible (q : OpenSquare) (h : Input q)
    (missingFar : ¬q.Inside (1/2) 1) : False := by
  obtain ⟨r,cp,range,side,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side same
  by_cases sign : 0≤r.s
  · exact positive_four_impossible r data cp sign
      (by simpa only [abs_of_nonneg sign] using range)
      (fun own => missingFar ((same _ _).mp own))
  · exact negative_impossible r data (-r.s) (by ring) cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

theorem corner_excluded (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (13/20) (13/20))
    (missingLeft : ¬q.Inside (-43/500) 0)
    (missingNear : ¬q.Inside (3/25) 0)
    (missingUpper : ¬q.Inside (-43/500) 1)
    (missingFar : ¬q.Inside (1/2) 1) : ¬q.Inside 0 0 := by
  intro origin
  exact four_impossible q ⟨side,origin,marker,missingLeft,missingNear,missingUpper⟩ missingFar

/-- Each of the four actual exclusions remains separate. In particular
the absent original marker is not assigned to the singleton owner. -/
theorem corner_excluded_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (33/20) (33/20))
    (missingLeft : ¬q.Inside (457/500) 1)
    (missingNear : ¬q.Inside (28/25) 1)
    (missingUpper : ¬q.Inside (457/500) 2)
    (missingFar : ¬q.Inside (3/2) 2) : ¬q.Inside 1 1 := by
  have result := corner_excluded (q.translated 1 1) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact missingLeft)
    (by norm_num [inside_translated_iff]; exact missingNear)
    (by norm_num [inside_translated_iff]; exact missingUpper)
    (by norm_num [inside_translated_iff]; exact missingFar)
  simpa only [inside_translated_iff,add_zero] using result

#print axioms four_impossible
#print axioms corner_excluded_original
end N12Compact.Completion.OtherCases.InnerCornerObstruction
