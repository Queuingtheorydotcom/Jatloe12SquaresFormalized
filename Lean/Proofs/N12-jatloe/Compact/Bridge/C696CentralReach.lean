import Compact.Bridge.C696WallCycle
import Compact.Geometry.FourSquareANarrow
import Compact.Geometry.ClosedFrames

/-! Four new strict central points from the actual original C696 packing.
The foreign high points come from actual singleton seed segments. No saved
pose state, corner-root choice, numerical propagation or center cut is used.
This is a simultaneous geometric consequence, not a case exclusion. -/
namespace N12Compact.C696CentralReach

open S12 S12Pilot S12Completion.C696 SideSignPacking FourSquareAnchors
set_option Elab.async false

def centralOwner : Fin 4 → Fin 12 := ![7,7,6,6]
def foreignOwner : Fin 4 → Fin 12 := ![4,3,1,0]

noncomputable def frame (q : OpenSquare) (i : Fin 4) : OpenSquare :=
  ![q,pullSwap q,pullX (pullY q),pullX (pullY (pullSwap q))] i

private theorem frame_inside (q : OpenSquare) (i : Fin 4) (P : ℚ × ℚ) :
    (frame q i).Inside P.1 P.2 ↔
      q.Inside (C696WallCycle.wallPoint i P).1 (C696WallCycle.wallPoint i P).2 := by
  fin_cases i <;>
    simp [frame,C696WallCycle.wallPoint,inside_pullX,inside_pullY,inside_pullSwap]

private theorem frame_side (q : OpenSquare) (i : Fin 4) :
    (frame q i).side = q.side := by fin_cases i <;> rfl

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (different : i ≠ j) :
    ∀ x y, ¬ ((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have hi := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  exact different (AuxiliaryNecessity.ownerMasks_injective
    (hi.symm.trans ((congrArg (markerCode p) equal).trans hj)))

private theorem frame_apart (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 4) :
    ∀ x y, ¬ ((frame (owners p (centralOwner i)) i).Inside x y ∧
      (frame (owners p (foreignOwner i)) i).Inside x y) := by
  have original := apart p hf (centralOwner i) (foreignOwner i)
    (by fin_cases i <;> decide)
  intro x y h
  fin_cases i <;>
    simp [frame,centralOwner,foreignOwner,inside_pullX,inside_pullY,inside_pullSwap] at h <;>
    exact original _ _ h

private theorem central_inside (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (P : ℚ × ℚ)
    (checked : ∀ i : Fin 4, C696WallCycle.wallPoint i P ∈
      queryInsidePoints (ownerMasks (centralOwner i)) 2 (auxiliaryVector (centralOwner i)))
    (i : Fin 4) : (frame (owners p (centralOwner i)) i).Inside P.1 P.2 :=
  (frame_inside _ i P).mpr (C696WallCycle.inside_query p hf _ _ (checked i))

private theorem central_missing (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (P : ℚ × ℚ)
    (checked : ∀ i : Fin 4, C696WallCycle.wallPoint i P ∈
      queryOutsidePoints (ownerMasks (centralOwner i)) 2 (auxiliaryVector (centralOwner i)))
    (i : Fin 4) : ¬ (frame (owners p (centralOwner i)) i).Inside P.1 P.2 :=
  fun h => C696WallCycle.outside_query p hf _ _ (checked i) ((frame_inside _ i P).mp h)

private theorem foreign_inside (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (P : ℚ × ℚ)
    (checked : ∀ i : Fin 4, C696WallCycle.wallPoint i P ∈
      queryInsidePoints (ownerMasks (foreignOwner i)) 2 (auxiliaryVector (foreignOwner i)))
    (i : Fin 4) : (frame (owners p (foreignOwner i)) i).Inside P.1 P.2 :=
  (frame_inside _ i P).mpr (C696WallCycle.inside_query p hf _ _ (checked i))

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

theorem frame_reach (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 4) : (frame (owners p (centralOwner i)) i).Inside 2 (5/2) := by
  let A := frame (owners p (centralOwner i)) i
  let R := frame (owners p (foreignOwner i)) i
  have aP : ClosedInside A 2 (113/50) := close (by
    simpa using central_inside p hf ((2,113/50) : ℚ × ℚ) (by decide +kernel) i)
  have aQ : ClosedInside A (113/50) 2 := close (by
    simpa using central_inside p hf ((113/50,2) : ℚ × ℚ) (by decide +kernel) i)
  have aT : ClosedInside A (47/20) (47/20) := close (by
    simpa using central_inside p hf ((47/20,47/20) : ℚ × ℚ) (by decide +kernel) i)
  have missingF : ¬ A.Inside (33/20) (33/20) := by
    simpa using central_missing p hf ((33/20,33/20) : ℚ × ℚ) (by decide +kernel) i
  have missingG : ¬ A.Inside (47/20) (33/20) := by
    simpa using central_missing p hf ((47/20,33/20) : ℚ × ℚ) (by decide +kernel) i
  have missingB : ¬ A.Inside (33/20) (47/20) := by
    simpa using central_missing p hf ((33/20,47/20) : ℚ × ℚ) (by decide +kernel) i
  have rLow : ClosedInside R 3 (12/5) := close (by
    simpa using foreign_inside p hf ((3,12/5) : ℚ × ℚ) (by decide +kernel) i)
  have rHigh : ClosedInside R 3 (72/25) := close (by
    simpa using foreign_inside p hf ((3,72/25) : ℚ × ℚ) (by decide +kernel) i)
  have rMiddle : ClosedInside R 3 (5/2) := by
    have point := ClosedPointExclusion.closed_segment R 3 (12/5) 3 (72/25)
      (5/24) rLow rHigh (by norm_num) (by norm_num)
    convert point using 1 <;> norm_num
  have missingR := ClosedPointExclusion.outside_of_closed A R _ _ (frame_apart p hf i) rLow
  have missingRhigh := ClosedPointExclusion.outside_of_closed A R _ _ (frame_apart p hf i) rMiddle
  obtain ⟨q,hc,hs,side,inside,closed⟩ := ClosedFrames.positive_frame A
  apply (inside _ _).mp
  apply FourSquareANarrow.point_of_higher_R q
    (by rw [side]; dsimp [A]; rw [frame_side]; exact C696WallCycle.side_gt p (centralOwner i)) hc hs
    ((closed _ _).mpr aP) ((closed _ _).mpr aQ) ((closed _ _).mpr aT)
  · exact fun h => missingF ((inside _ _).mp h)
  · exact fun h => missingG ((inside _ _).mp h)
  · exact fun h => missingB ((inside _ _).mp h)
  · exact fun h => missingR ((inside _ _).mp h)
  · exact fun h => missingRhigh ((inside _ _).mp h)

/-- Simultaneous strict points on the two opposite central squares, before
choosing either missing-corner root. -/
theorem central_points (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 7).Inside 2 (5/2) ∧ (owners p 7).Inside (5/2) 2 ∧
    (owners p 6).Inside 2 (3/2) ∧ (owners p 6).Inside (3/2) 2 := by
  have h₀ := frame_reach p hf 0
  have h₁ := frame_reach p hf 1
  have h₂ := frame_reach p hf 2
  have h₃ := frame_reach p hf 3
  change (pullX (pullY (owners p 6))).Inside 2 (5/2) at h₂
  change (pullX (pullY (pullSwap (owners p 6)))).Inside 2 (5/2) at h₃
  norm_num [frame,centralOwner,inside_pullX,inside_pullY,inside_pullSwap] at h₀ h₁ h₂ h₃
  exact ⟨h₀,h₁,h₂,h₃⟩

#print axioms central_points

end N12Compact.C696CentralReach
