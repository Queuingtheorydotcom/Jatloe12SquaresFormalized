import Compact.Completion.C981.HalfAngle
import Compact.Geometry.ClosedFrames

/-! C981-COMMON-CYCLE Theorem 1 and Corollary 4. The short-chord face
tables follow directly from the original strict marker/top anchor and
four endpoint exclusions; no chord formula or extra center is assumed. -/
namespace N12Compact.C981CompletionUpperPoint

open S12 S12Pilot
set_option Elab.async false

private theorem positive_faces (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (lowerLeft : ¬ q.Inside 2 (12/5)) (upperLeft : ¬ q.Inside 2 3)
    (lowerRight : ¬ q.Inside 3 (12/5)) (upperRight : ¬ q.Inside 3 3) :
    2*q.c+(12/5)*q.s ≤ q.loU ∧ q.loU+q.side ≤ 3*q.c+3*q.s ∧
      -3*q.s+(12/5)*q.c ≤ q.loV ∧ q.loV+q.side ≤ -2*q.s+3*q.c := by
  have cone : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have llUhi : 2*q.c+(12/5)*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hc,order]
  have llVlo : q.loV < -2*q.s+(12/5)*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have llVhi : -2*q.s+(12/5)*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs,order]
  have lowU : 2*q.c+(12/5)*q.s ≤ q.loU :=
    le_of_not_gt (fun u => lowerLeft ⟨by linarith only [u],by linarith only [llUhi],by linarith only [llVlo],by linarith only [llVhi]⟩)
  have urUlo : q.loU < 3*q.c+3*q.s := by
    linarith only [marker.1,hc,hs]
  have urVlo : q.loV < -3*q.s+3*q.c := by
    linarith only [marker.2.2.1,order]
  have urVhi : -3*q.s+3*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hs]
  have highU : q.loU+q.side ≤ 3*q.c+3*q.s :=
    le_of_not_gt (fun u => upperRight ⟨by linarith only [urUlo],by linarith only [u],by linarith only [urVlo],by linarith only [urVhi]⟩)
  have ulUlo : q.loU < 2*q.c+3*q.s := by
    linarith only [highU,side,cone]
  have ulUhi : 2*q.c+3*q.s < q.loU+q.side := by
    linarith only [top.2.1,hc]
  have ulVlo : q.loV < -2*q.s+3*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have highV : q.loV+q.side ≤ -2*q.s+3*q.c :=
    le_of_not_gt (fun v => upperLeft ⟨by linarith only [ulUlo],by linarith only [ulUhi],by linarith only [ulVlo],by linarith only [v]⟩)
  have lrUlo : q.loU < 3*q.c+(12/5)*q.s := by
    linarith only [marker.1,hc,hs]
  have lrUhi : 3*q.c+(12/5)*q.s < q.loU+q.side := by
    linarith only [lowU,side,cone]
  have lrVhi : -3*q.s+(12/5)*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have lowV : -3*q.s+(12/5)*q.c ≤ q.loV :=
    le_of_not_gt (fun v => lowerRight ⟨by linarith only [lrUlo],by linarith only [lrUhi],by linarith only [v],by linarith only [lrVhi]⟩)
  exact ⟨lowU,highU,lowV,highV⟩

/-- In a nonnegative canonical frame the extra actual right-wall point
forces half-angle greater than 7/18 and the common strict point. -/
theorem positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (lowerLeft : ¬ q.Inside 2 (12/5)) (upperLeft : ¬ q.Inside 2 3)
    (lowerRight : ¬ q.Inside 3 (12/5)) (upperRight : ¬ q.Inside 3 3)
    (extraRight : ¬ q.Inside 3 (64/25)) :
    7/18 < C981CompletionHalfAngle.half q.c q.s ∧ q.Inside 2 (131/50) := by
  have faces := positive_faces q side hc hs order marker top
    lowerLeft upperLeft lowerRight upperRight
  have width : 1 < q.s+(3/5)*q.c := by
    linarith only [faces.2.2.1,faces.2.2.2,side]
  have quarter := C981CompletionHalfAngle.quarter_lt q.c q.s hc.le hs order
    q.unit_normal width
  have data := C981CompletionHalfAngle.data q.c q.s hc.le hs order q.unit_normal
  have sine : 0 < q.s := by
    by_contra no
    have zero : q.s=0 := by linarith only [hs,no]
    rw [zero] at quarter
    simp only [C981CompletionHalfAngle.half,zero_div] at quarter
    linarith only [quarter]
  have short16 := C981CompletionHalfAngle.short_of_half q.c q.s (4/25) hc.le sine
    q.unit_normal (by linarith only [quarter])
  have rUlo : q.loU < 3*q.c+(64/25)*q.s := by
    linarith only [marker.1,hc,hs]
  have rUhi : 3*q.c+(64/25)*q.s < q.loU+q.side := by
    linarith only [faces.1,short16,side]
  have rVhi : -3*q.s+(64/25)*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have extraV : -3*q.s+(64/25)*q.c ≤ q.loV :=
    le_of_not_gt (fun v => extraRight ⟨by linarith only [rUlo],by linarith only [rUhi],by linarith only [v],by linarith only [rVhi]⟩)
  have steepWidth : 1 < q.s+(11/25)*q.c := by
    linarith only [extraV,faces.2.2.2,side]
  have steep := C981CompletionHalfAngle.steep_lt q.c q.s hc.le hs order
    q.unit_normal steepWidth
  have short38 := C981CompletionHalfAngle.short_of_half q.c q.s (19/50) hc.le sine
    q.unit_normal (by linarith only [steep])
  have sineShort := C981CompletionHalfAngle.sine38_short q.c q.s hc.le hs order
    q.unit_normal
  have uLow : q.loU < 2*q.c+(131/50)*q.s := by
    linarith only [faces.2.1,short38,side]
  have uHigh : 2*q.c+(131/50)*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hc,order]
  have vLow : q.loV < -2*q.s+(131/50)*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have vHigh : -2*q.s+(131/50)*q.c < q.loV+q.side := by
    linarith only [faces.2.2.1,sineShort,hc,side]
  exact ⟨steep,⟨by linarith only [uLow],by linarith only [uHigh],by linarith only [vLow],by linarith only [vHigh]⟩⟩

private theorem negative_faces (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (lowerLeft : ¬ q.Inside 2 (12/5)) (upperLeft : ¬ q.Inside 2 3)
    (lowerRight : ¬ q.Inside 3 (12/5)) (upperRight : ¬ q.Inside 3 3) :
    2*q.c+3*q.s ≤ q.loU ∧ q.loU+q.side ≤ 3*q.c+(12/5)*q.s ∧
      -2*q.s+(12/5)*q.c ≤ q.loV ∧ q.loV+q.side ≤ -3*q.s+3*q.c := by
  have cone : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have ulUhi : 2*q.c+3*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hc,hs]
  have ulVlo : q.loV < -2*q.s+3*q.c := by
    linarith only [marker.2.2.1,hc,order]
  have ulVhi : -2*q.s+3*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hs]
  have lowU : 2*q.c+3*q.s ≤ q.loU :=
    le_of_not_gt (fun u => upperLeft ⟨by linarith only [u],by linarith only [ulUhi],by linarith only [ulVlo],by linarith only [ulVhi]⟩)
  have lrUlo : q.loU < 3*q.c+(12/5)*q.s := by
    linarith only [marker.1,hc,order]
  have lrVlo : q.loV < -3*q.s+(12/5)*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have lrModes : q.loU+q.side ≤ 3*q.c+(12/5)*q.s ∨
      q.loV+q.side ≤ -3*q.s+(12/5)*q.c := by
    by_cases u : q.loU+q.side ≤ 3*q.c+(12/5)*q.s
    · exact Or.inl u
    · exact Or.inr (le_of_not_gt (fun v => lowerRight
        ⟨by linarith only [lrUlo],by linarith only [u],by linarith only [lrVlo],by linarith only [v]⟩))
  have llUhi : 2*q.c+(12/5)*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hc,hs]
  have llVhi : -2*q.s+(12/5)*q.c < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have llUlo : q.loU < 2*q.c+(12/5)*q.s := by
    apply lt_of_not_ge
    intro lower
    rcases lrModes with u | v
    · linarith only [lower,u,side,cone]
    · linarith only [lower,v,top.1,top.2.2.2,hc]
  have lowV : -2*q.s+(12/5)*q.c ≤ q.loV :=
    le_of_not_gt (fun v => lowerLeft ⟨by linarith only [llUlo],by linarith only [llUhi],by linarith only [v],by linarith only [llVhi]⟩)
  have highU : q.loU+q.side ≤ 3*q.c+(12/5)*q.s := by
    rcases lrModes with u | v
    · exact u
    · exfalso; linarith only [lowV,v,side,order,cone]
  have urUlo : q.loU < 3*q.c+3*q.s := by
    linarith only [marker.1,order]
  have urUhi : 3*q.c+3*q.s < q.loU+q.side := by
    linarith only [lowU,side,cone]
  have urVlo : q.loV < -3*q.s+3*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have highV : q.loV+q.side ≤ -3*q.s+3*q.c :=
    le_of_not_gt (fun v => upperRight ⟨by linarith only [urUlo],by linarith only [urUhi],by linarith only [urVlo],by linarith only [v]⟩)
  exact ⟨lowU,highU,lowV,highV⟩

/-- The other canonical sign owns the same point; no steep-angle claim is
made for this sign. This also excludes an axial square by its width. -/
theorem nonpositive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (lowerLeft : ¬ q.Inside 2 (12/5)) (upperLeft : ¬ q.Inside 2 3)
    (lowerRight : ¬ q.Inside 3 (12/5)) (upperRight : ¬ q.Inside 3 3) :
    q.Inside 2 (131/50) := by
  have faces := negative_faces q side hc hs order marker top
    lowerLeft upperLeft lowerRight upperRight
  let t := -q.s
  have tp : 0 ≤ t := by dsimp [t]; linarith only [hs]
  have tc : t ≤ q.c := order
  have unit : q.c^2+t^2=1 := by dsimp [t]; nlinarith only [q.unit_normal]
  have width : 1 < t+(3/5)*q.c := by
    dsimp [t]
    linarith only [faces.2.2.1,faces.2.2.2,side]
  have quarter := C981CompletionHalfAngle.quarter_lt q.c t hc.le tp tc unit width
  have positive : 0 < t := by
    by_contra no
    have zero : t=0 := by linarith only [tp,no]
    rw [zero] at quarter
    simp only [C981CompletionHalfAngle.half,zero_div] at quarter
    linarith only [quarter]
  have short22 := C981CompletionHalfAngle.short_of_half q.c t (11/50) hc.le positive
    unit (by linarith only [quarter])
  have sineShort := C981CompletionHalfAngle.sine38_short q.c t hc.le tp tc unit
  have cone : q.c ≤ 1 := by nlinarith only [unit,sq_nonneg t,sq_nonneg (q.c-1)]
  dsimp [t] at short22 sineShort
  have uLow : q.loU < 2*q.c+(131/50)*q.s := by
    linarith only [faces.2.1,short22,side]
  have uHigh : 2*q.c+(131/50)*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hc,hs]
  have vLow : q.loV < -2*q.s+(131/50)*q.c := by
    linarith only [faces.2.2.2,sineShort,side]
  have vHigh : -2*q.s+(131/50)*q.c < q.loV+q.side := by
    linarith only [faces.2.2.1,cone,side]
  exact ⟨by linarith only [uLow],by linarith only [uHigh],by linarith only [vLow],by linarith only [vHigh]⟩

/-- Same physical upper square, with all canonical signs and endpoints. -/
theorem point (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (lowerLeft : ¬ q.Inside 2 (12/5)) (upperLeft : ¬ q.Inside 2 3)
    (lowerRight : ¬ q.Inside 3 (12/5)) (upperRight : ¬ q.Inside 3 3)
    (extraRight : ¬ q.Inside 3 (64/25)) : q.Inside 2 (131/50) := by
  obtain ⟨r,hc,order,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rMarker := (equivalent _ _).mpr marker
  have rTop := (equivalent _ _).mpr top
  have rLL : ¬ r.Inside 2 (12/5) := fun h => lowerLeft ((equivalent _ _).mp h)
  have rUL : ¬ r.Inside 2 3 := fun h => upperLeft ((equivalent _ _).mp h)
  have rLR : ¬ r.Inside 3 (12/5) := fun h => lowerRight ((equivalent _ _).mp h)
  have rUR : ¬ r.Inside 3 3 := fun h => upperRight ((equivalent _ _).mp h)
  by_cases positiveSign : 0 ≤ r.s
  · exact (equivalent _ _).mp ((positive r rSide hc positiveSign
      (by simpa only [abs_of_nonneg positiveSign] using order)
      rMarker rTop rLL rUL rLR rUR
      (fun h => extraRight ((equivalent _ _).mp h))).2)
  · have negativeSign : r.s ≤ 0 := le_of_lt (lt_of_not_ge positiveSign)
    exact (equivalent _ _).mp (nonpositive r rSide hc negativeSign
      (by simpa only [abs_of_nonpos negativeSign] using order)
      rMarker rTop rLL rUL rLR rUR)

#print axioms point
end N12Compact.C981CompletionUpperPoint
