import Compact.Completion.OtherCases.OrdinaryCentralReductionGeometry
import Compact.Completion.C1092.MPPMEntrance

/-! Theorem 1 of C1092-MPPM-ORDINARY-CENTRAL-REDUCTION, in the original
packing. Each application moves its central square and its foreign wall
square by the same physical chart. The lower omitted point comes from
the strict segment in the preceding actual wall owner. The complete
upper bar comes from that wall's marker and the hypothetically owned
inner auxiliary, not from a postulated support cap.

Only the ordinary wall point used by the corresponding row is required;
the other endpoint is the actual MPPM wall auxiliary. All four statements
are source translations and have not been compiled. -/
namespace N12Compact.Completion.OtherCases.OrdinaryCentralReduction
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

private def leftChart (q : OpenSquare) : OpenSquare := q.translated 1 1
private def bottomChart (q : OpenSquare) : OpenSquare :=
  (pullSwap (pullX q)).translated 1 1
private def rightChart (q : OpenSquare) : OpenSquare :=
  (pullY (pullX q)).translated 1 1
private def topChart (q : OpenSquare) : OpenSquare :=
  (pullSwap (pullY q)).translated 1 1

private theorem left_actual (q : OpenSquare) (x y : ℝ) :
    (leftChart q).Inside x y ↔ q.Inside (1+x) (1+y) :=
  inside_translated_iff q 1 1 x y

private theorem bottom_actual (q : OpenSquare) (x y : ℝ) :
    (bottomChart q).Inside x y ↔ q.Inside (3-y) (1+x) := by
  simp only [bottomChart,inside_translated_iff,inside_pullSwap,inside_pullX]
  rw [show (4:ℝ)-(1+y)=3-y by ring]

private theorem right_actual (q : OpenSquare) (x y : ℝ) :
    (rightChart q).Inside x y ↔ q.Inside (3-x) (3-y) := by
  simp only [rightChart,inside_translated_iff,inside_pullY,inside_pullX]
  rw [show (4:ℝ)-(1+x)=3-x by ring,show (4:ℝ)-(1+y)=3-y by ring]

private theorem top_actual (q : OpenSquare) (x y : ℝ) :
    (topChart q).Inside x y ↔ q.Inside (1+y) (3-x) := by
  simp only [topChart,inside_translated_iff,inside_pullSwap,inside_pullY]
  rw [show (4:ℝ)-(1+x)=3-x by ring]

/-- F0 in Q4 excludes G3 from actual Q8. The lower segment belongs
throughout to actual Q9; the upper segment belongs throughout to Q8. -/
theorem left_inner_absent (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (centralF0 : (owners p 4).Inside 1 (87/50)) :
    ¬(owners p 8).Inside (87/50) 2 := by
  intro inner
  have markC : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have markW : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  have lower := inside_segment (owners p 9) (8/5) 1 (87/50) 1 (5/14)
    bottomF (wall_auxiliaries p hb).2.1 (by norm_num) (by norm_num)
  norm_num at lower
  apply foreign_bar_impossible (leftChart (owners p 4)) (leftChart (owners p 8))
    (side_gt p 4)
  · apply (left_actual _ _ _).mpr; norm_num; exact centralF0
  · apply (left_actual _ _ _).mpr; norm_num; exact markC
  · intro own
    have point := (left_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨point,corner⟩
  · intro own
    have point := (left_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨point,lower⟩
  · apply (left_actual _ _ _).mpr; norm_num; exact markW
  · apply (left_actual _ _ _).mpr; norm_num; exact inner
  · intro x y own
    exact owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(left_actual _ _ _).mp own.1,(left_actual _ _ _).mp own.2⟩

/-- G5 in Q5 excludes F4 from actual Q9, with the Q10 foreign lower
segment and Q9 upper bar simultaneously expressed in the same chart. -/
theorem bottom_inner_absent (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (rightG : (owners p 10).Inside 3 (8/5))
    (centralG5 : (owners p 5).Inside (113/50) 1) :
    ¬(owners p 9).Inside 2 (87/50) := by
  intro inner
  have markC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have markW : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have lower := inside_segment (owners p 10) 3 (8/5) 3 (87/50) (5/14)
    rightG (wall_auxiliaries p hb).2.2.1 (by norm_num) (by norm_num)
  norm_num at lower
  apply foreign_bar_impossible (bottomChart (owners p 5)) (bottomChart (owners p 9))
    (side_gt p 5)
  · apply (bottom_actual _ _ _).mpr; norm_num; exact centralG5
  · apply (bottom_actual _ _ _).mpr; norm_num; exact markC
  · intro own
    have point := (bottom_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨point,corner⟩
  · intro own
    have point := (bottom_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨point,lower⟩
  · apply (bottom_actual _ _ _).mpr; norm_num; exact markW
  · apply (bottom_actual _ _ _).mpr; norm_num; exact inner
  · intro x y own
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨(bottom_actual _ _ _).mp own.1,(bottom_actual _ _ _).mp own.2⟩

/-- F9 in Q6 excludes G6 from actual Q10. The complete configuration,
including both separate foreign owners, is rotated by a half-turn. -/
theorem right_inner_absent (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (topF : (owners p 11).Inside (12/5) 3)
    (centralF9 : (owners p 6).Inside 3 (113/50)) :
    ¬(owners p 10).Inside (113/50) 2 := by
  intro inner
  have markC : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markW : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have lower := inside_segment (owners p 11) (12/5) 3 (113/50) 3 (5/14)
    topF (wall_auxiliaries p hb).2.2.2 (by norm_num) (by norm_num)
  norm_num at lower
  apply foreign_bar_impossible (rightChart (owners p 6)) (rightChart (owners p 10))
    (side_gt p 6)
  · apply (right_actual _ _ _).mpr; norm_num; exact centralF9
  · apply (right_actual _ _ _).mpr; norm_num; exact markC
  · intro own
    have point := (right_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨point,corner⟩
  · intro own
    have point := (right_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨point,lower⟩
  · apply (right_actual _ _ _).mpr; norm_num; exact markW
  · apply (right_actual _ _ _).mpr; norm_num; exact inner
  · intro x y own
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨(right_actual _ _ _).mp own.1,(right_actual _ _ _).mp own.2⟩

/-- G4 in Q7 excludes F5 from actual Q11. The Q8 lower segment and
the Q11 marker-to-inner upper segment remain distinct actual owners. -/
theorem top_inner_absent (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (leftG : (owners p 8).Inside 1 (12/5))
    (centralG4 : (owners p 7).Inside (87/50) 3) :
    ¬(owners p 11).Inside 2 (113/50) := by
  intro inner
  have markC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markW : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  have lower := inside_segment (owners p 8) 1 (12/5) 1 (113/50) (5/14)
    leftG (wall_auxiliaries p hb).1 (by norm_num) (by norm_num)
  norm_num at lower
  apply foreign_bar_impossible (topChart (owners p 7)) (topChart (owners p 11))
    (side_gt p 7)
  · apply (top_actual _ _ _).mpr; norm_num; exact centralG4
  · apply (top_actual _ _ _).mpr; norm_num; exact markC
  · intro own
    have point := (top_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 7 3 (by decide) _ _ ⟨point,corner⟩
  · intro own
    have point := (top_actual _ _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨point,lower⟩
  · apply (top_actual _ _ _).mpr; norm_num; exact markW
  · apply (top_actual _ _ _).mpr; norm_num; exact inner
  · intro x y own
    exact owners_disjoint p hf 7 11 (by decide) _ _
      ⟨(top_actual _ _ _).mp own.1,(top_actual _ _ _).mp own.2⟩

end
#print axioms left_inner_absent
#print axioms bottom_inner_absent
#print axioms right_inner_absent
#print axioms top_inner_absent
end N12Compact.Completion.OtherCases.OrdinaryCentralReduction
