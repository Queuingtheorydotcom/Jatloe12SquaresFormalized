import Compact.Completion.C981.ShortOutwardLock
import Compact.Completion.CommonCases.ShortOutwardPoint
import Compact.Completion.CommonCases.InwardPoint

/-! The shorter-wall common ending. The whole top segment is supplied
by its one actual owner; every other premise names a genuine strict
anchor or a weak absence of one of the two actual central squares. -/
namespace N12Compact.C981CompletionShortWallCycle

open S12 S12Pilot
set_option Elab.async false

theorem impossible (a b : OpenSquare) (side : 1 < a.side)
    (same : a.side=b.side)
    (aMarker : a.Inside (47/20) (33/20))
    (aInward : a.Inside 2 (87/50)) (aElbow : a.Inside (113/50) 2)
    (aMissingSW : ¬ a.Inside (33/20) (33/20))
    (aMissingNE : ¬ a.Inside (47/20) (47/20))
    (aMissingBottom : ¬ a.Inside (12/5) 1)
    (bMarker : b.Inside (47/20) (47/20))
    (bElbow : b.Inside 3 (113/50)) (bHigh : b.Inside 3 (12/5))
    (bMissingRight : ¬ b.Inside (1543/500) 2)
    (bMissingF : ¬ b.Inside (113/50) 3)
    (bMissingT : ¬ b.Inside (273/100) 3)
    (bMissingCorner : ¬ b.Inside 3 3)
    (bMissingHighCorner : ¬ b.Inside (1543/500) 3)
    (bAvoidTop : ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → ¬ b.Inside z 3)
    (apart : ∀ x y, ¬ (a.Inside x y ∧ b.Inside x y)) : False := by
  have pointA := CommonCases.InwardPoint.strong_original a side aMarker aInward aElbow
    aMissingSW aMissingNE aMissingBottom
  have bSide : 1 < b.side := by simpa only [same] using side
  have bMissingG : ¬ b.Inside (113/50) 2 := by
    intro point
    exact apart _ _ ⟨aElbow,point⟩
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame b
  have rSide : 1 < r.side := by simpa only [shape] using bSide
  by_cases sign : 0 ≤ r.s
  · have pointB := CommonCases.ShortOutwardPoint.positive_point_original r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon)
      ((equivalent _ _).mpr bMarker) ((equivalent _ _).mpr bElbow)
      (fun h => bMissingG ((equivalent _ _).mp h))
      (fun h => bMissingRight ((equivalent _ _).mp h))
      (fun h => bMissingF ((equivalent _ _).mp h))
      (fun h => bMissingT ((equivalent _ _).mp h))
      (fun h => bMissingCorner ((equivalent _ _).mp h))
      (fun h => bMissingHighCorner ((equivalent _ _).mp h))
    exact apart _ _ ⟨pointA,(equivalent _ _).mp pointB⟩
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    have rOrder : -r.s ≤ r.c := by simpa only [abs_of_nonpos negative] using canon
    have marker : (pullY r).Inside (47/20) (33/20) := by
      apply (inside_pullY _ _ _).mpr
      convert (equivalent _ _).mpr bMarker using 1 <;> norm_num
    have high : (pullY r).Inside 3 (8/5) := by
      apply (inside_pullY _ _ _).mpr
      convert (equivalent _ _).mpr bHigh using 1 <;> norm_num
    have corner : ¬ (pullY r).Inside 3 1 := by
      intro point
      have h := (inside_pullY _ _ _).mp point
      norm_num at h
      exact bMissingCorner ((equivalent _ _).mp h)
    have right : ¬ (pullY r).Inside (1543/500) 2 := by
      intro point
      have h := (inside_pullY _ _ _).mp point
      norm_num at h
      exact bMissingRight ((equivalent _ _).mp h)
    have elbow : ¬ (pullY r).Inside (113/50) 2 := by
      intro point
      have h := (inside_pullY _ _ _).mp point
      norm_num at h
      exact bMissingG ((equivalent _ _).mp h)
    have avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → ¬ (pullY r).Inside z 1 := by
      intro z lo hi point
      have h := (inside_pullY _ _ _).mp point
      norm_num at h
      exact bAvoidTop z lo hi ((equivalent _ _).mp h)
    exact C981CompletionShortOutwardLock.nonnegative_impossible (pullY r) rSide
      hc (by change 0 ≤ -r.s; linarith only [negative]) rOrder
      marker high corner right elbow avoid

#print axioms impossible
end N12Compact.C981CompletionShortWallCycle
