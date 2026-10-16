import Compact.Completion.OtherCases.SouthwestSupportPoint.Positive
import Compact.Completion.OtherCases.SouthwestSupportPoint.Negative
import Compact.Completion.OtherCases.SouthwestSupportPoint.SegmentSupport

/-! C974-C976-SW-SUPPORT-POINT, Theorem 1. Canonicalization only reindexes
the actual square. The final theorem has the paper's original coordinates
and literal point/segment exclusions, without a side upper bound or wall. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint
open S12 S12Pilot
set_option Elab.async false

theorem point_centered (q : OpenSquare) (h : Input q) :
    q.Inside (-73/100) (-1/25) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe shape same
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using canonical
    exact positive r data cp sign order (SegmentSupport.positive r data cp sign order)
  · have order : -r.s≤r.c := by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical
    have sn : 0≤ -r.s := by linarith only [sign]
    exact negative r data (-r.s) (by ring) cp sn order
      (SegmentSupport.negative r data (-r.s) (by ring) cp sn order)

theorem point (A : OpenSquare) (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (inwardSouth : A.Inside 2 (87/50)) (inwardWest : A.Inside (87/50) 2)
    (west : A.Inside (3/2) 2) (south : A.Inside 2 (3/2))
    (missingNorth : ¬A.Inside (33/20) (47/20))
    (missingEast : ¬A.Inside (47/20) (33/20))
    (missingBottom : ¬A.Inside 2 1)
    (missingLeftLow : ¬A.Inside 1 (8/5)) (missingLeftHigh : ¬A.Inside 1 (87/50))
    (bottomSegment : ∀ x : ℝ,3/2≤x → x≤87/50 → ¬A.Inside x 1)
    (southeastSegment : ∀ t : ℝ,0≤t → t≤1 →
      ¬A.Inside (47/20-(9/100)*t) (33/20+(7/20)*t)) :
    A.Inside (127/100) (49/25) := by
  let q : OpenSquare :=
    ⟨A.c,A.s,A.loU-2*(A.c+A.s),A.loV-2*(A.c-A.s),A.side,A.unit_normal,A.side_pos⟩
  have same (x y : ℝ) : q.Inside x y ↔ A.Inside (x+2) (y+2) := by
    dsimp only [q,OpenSquare.Inside,InBands]
    constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]
  let h : Input q := {
    side := side
    marker := (same _ _).mpr (by norm_num; exact marker)
    inwardSouth := (same _ _).mpr (by norm_num; exact inwardSouth)
    inwardWest := (same _ _).mpr (by norm_num; exact inwardWest)
    west := (same _ _).mpr (by norm_num; exact west)
    south := (same _ _).mpr (by norm_num; exact south)
    missingNorth := fun p => missingNorth (by convert (same _ _).mp p using 1 <;> norm_num)
    missingEast := fun p => missingEast (by convert (same _ _).mp p using 1 <;> norm_num)
    missingBottom := fun p => missingBottom (by convert (same _ _).mp p using 1 <;> norm_num)
    missingLeftLow := fun p => missingLeftLow (by convert (same _ _).mp p using 1 <;> norm_num)
    missingLeftHigh := fun p => missingLeftHigh (by convert (same _ _).mp p using 1 <;> norm_num)
    bottomSegment := by
      intro x low high owned
      apply bottomSegment (x+2) (by linarith only [low]) (by linarith only [high])
      simpa only [show (-1:ℝ)+2=1 by norm_num] using (same _ _).mp owned
    southeastSegment := by
      intro t low high owned
      apply southeastSegment t low high
      convert (same _ _).mp owned using 1 <;> ring
  }
  have result := (same _ _).mp (point_centered q h)
  norm_num at result
  exact result

/-- An application interface retaining two separately specified actual
neighbours for the two excluded segments. -/
theorem point_of_neighbours (A B R : OpenSquare) (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (inwardSouth : A.Inside 2 (87/50)) (inwardWest : A.Inside (87/50) 2)
    (west : A.Inside (3/2) 2) (south : A.Inside 2 (3/2))
    (missingNorth : ¬A.Inside (33/20) (47/20))
    (missingBottom : ¬A.Inside 2 1)
    (missingLeftLow : ¬A.Inside 1 (8/5)) (missingLeftHigh : ¬A.Inside 1 (87/50))
    (bottomLeft : B.Inside (3/2) 1) (bottomRight : B.Inside (87/50) 1)
    (southeastMarker : R.Inside (47/20) (33/20)) (southeastElbow : R.Inside (113/50) 2)
    (apartBottom : ∀ x y,¬(A.Inside x y ∧ B.Inside x y))
    (apartSoutheast : ∀ x y,¬(A.Inside x y ∧ R.Inside x y)) :
    A.Inside (127/100) (49/25) := by
  apply point A side marker inwardSouth inwardWest west south missingNorth
    (fun p => apartSoutheast _ _ ⟨p,southeastMarker⟩)
    missingBottom missingLeftLow missingLeftHigh
  · intro x low high own
    let t := (x-3/2)/(6/25)
    have tn : 0≤t := div_nonneg (by linarith only [low]) (by norm_num)
    have tu : t≤1 := (div_le_one (by norm_num)).mpr (by linarith only [high])
    have foreign : B.Inside x 1 := by
      convert inside_segment B (3/2) 1 (87/50) 1 t bottomLeft bottomRight tn tu using 1
      · dsimp only [t]; ring
      · ring
    exact apartBottom _ _ ⟨own,foreign⟩
  · intro t low high own
    have foreign : R.Inside (47/20-(9/100)*t) (33/20+(7/20)*t) := by
      convert inside_segment R (47/20) (33/20) (113/50) 2 t
        southeastMarker southeastElbow low high using 1 <;> ring
    exact apartSoutheast _ _ ⟨own,foreign⟩

#print axioms point_centered
#print axioms point
#print axioms point_of_neighbours
end N12Compact.Completion.OtherCases.SouthwestSupportPoint
