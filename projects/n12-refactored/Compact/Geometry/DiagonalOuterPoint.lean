import Compact.Geometry.ClosedFrames

/-! The two diagonal boundary points cannot both avoid their adjacent outer
points. The missing inner points select actual square faces. A unit-normal
identity then rules out the only orientation sector where the other outer
point could leave the square. There is no side upper bound or container
assumption. -/
namespace N12Compact.DiagonalOuterPoint

open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem shallow (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (hsc : q.s ≤ q.c)
    (top : q.Inside (113/50) 3) (right : q.Inside 3 (113/50))
    (missingInner : ¬ q.Inside 2 (113/50))
    (missingRight : ¬ q.Inside 3 (12/5)) : q.Inside (12/5) 3 := by
  have innerUhi : q.c*2+q.s*(113/50) < q.loU+q.side := by
    linarith only [top.2.1,hc,hs]
  have innerVlo : q.loV < -q.s*2+q.c*(113/50) := by
    linarith only [right.2.2.1,hs]
  have innerVhi : -q.s*2+q.c*(113/50) < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hsc]
  have innerFace : q.c*2+q.s*(113/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingInner ⟨h,innerUhi,innerVlo,innerVhi⟩)
  have outerUlo : q.loU < q.c*3+q.s*(12/5) := by
    linarith only [right.1,hs]
  have outerVlo : q.loV < -q.s*3+q.c*(12/5) := by
    linarith only [right.2.2.1,hc]
  have outerVhi : -q.s*3+q.c*(12/5) < q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have outerFace : q.loU+q.side ≤ q.c*3+q.s*(12/5) :=
    le_of_not_gt (fun h => missingRight ⟨outerUlo,h,outerVlo,outerVhi⟩)
  have width : q.side ≤ q.c+(7/50)*q.s := by
    linarith only [innerFace,outerFace]
  have angle : 3*q.s < q.c := by
    apply lt_of_not_ge
    intro steep
    have product := mul_nonneg hs (sub_nonneg.mpr steep)
    have smallProjection : (q.c+(7/50)*q.s)^2 ≤ 1 := by
      nlinarith only [q.unit_normal,product,sq_nonneg q.s]
    have greater : 1 < q.c+(7/50)*q.s := ha.trans_le width
    have positive := mul_pos (sub_pos.mpr greater)
      (show 0 < q.c+(7/50)*q.s+1 by linarith only [greater])
    nlinarith only [smallProjection,positive]
  exact ⟨by linarith only [top.1,hc],
    by linarith only [right.2.1,angle,hc],
    by linarith only [right.2.2.1,hc,hs],
    by linarith only [top.2.2.2,hs]⟩

/-- Every orientation is covered by exchanging the two coordinates in the
steep positive frame. The two original endpoints and both missing inner
points refer to the physical square. -/
theorem point (q : OpenSquare) (ha : 1 < q.side)
    (top : q.Inside (113/50) 3) (right : q.Inside 3 (113/50))
    (missingLeft : ¬ q.Inside 2 (113/50))
    (missingLow : ¬ q.Inside (113/50) 2) :
    q.Inside (12/5) 3 ∨ q.Inside 3 (12/5) := by
  obtain ⟨r,hc,hs,hside,hi,_⟩ := ClosedFrames.positive_frame q
  have rTop := (hi _ _).mpr top
  have rRight := (hi _ _).mpr right
  have rMissingLeft : ¬ r.Inside 2 (113/50) :=
    fun h => missingLeft ((hi _ _).mp h)
  have rMissingLow : ¬ r.Inside (113/50) 2 :=
    fun h => missingLow ((hi _ _).mp h)
  have ra : 1 < r.side := by simpa only [hside] using ha
  by_cases hsc : r.s ≤ r.c
  · by_cases outer : r.Inside 3 (12/5)
    · exact Or.inr ((hi _ _).mp outer)
    · exact Or.inl ((hi _ _).mp
        (shallow r ra hc hs hsc rTop rRight rMissingLeft outer))
  · by_cases outer : r.Inside (12/5) 3
    · exact Or.inl ((hi _ _).mp outer)
    · have swapped := shallow (pullSwap r)
        (by simpa only [pullSwap] using ra)
        (by simpa only [pullSwap] using hc.trans (lt_of_not_ge hsc))
        (by simpa only [pullSwap] using hc.le)
        (by simpa only [pullSwap] using (lt_of_not_ge hsc).le)
        ((inside_pullSwap r _ _).mpr rRight)
        ((inside_pullSwap r _ _).mpr rTop)
        (fun h => rMissingLow ((inside_pullSwap r _ _).mp h))
        (fun h => outer ((inside_pullSwap r _ _).mp h))
      exact Or.inr ((hi _ _).mp ((inside_pullSwap r _ _).mp swapped))

/-- A complete local exclusion with no upper bound on the side. -/
theorem impossible (q : OpenSquare) (ha : 1 < q.side)
    (top : q.Inside (113/50) 3) (right : q.Inside 3 (113/50))
    (missingLeft : ¬ q.Inside 2 (113/50))
    (missingLow : ¬ q.Inside (113/50) 2)
    (missingTop : ¬ q.Inside (12/5) 3)
    (missingRight : ¬ q.Inside 3 (12/5)) : False := by
  exact (point q ha top right missingLeft missingLow).elim missingTop missingRight

#print axioms point
#print axioms impossible
end N12Compact.DiagonalOuterPoint
