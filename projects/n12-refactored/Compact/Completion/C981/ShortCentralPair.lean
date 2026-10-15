import Compact.Completion.C981.ShortOutwardLock
import Compact.Completion.C981.NegativePair

/-! A northeast central owner and the actual southeast outward owner.
The genuine bottom-wall segment forces the outward owner's canonical sign;
a half turn then gives the existing negative/negative pair obstruction. -/
namespace N12Compact.C981CompletionShortCentralPair

open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private noncomputable def reverse (q : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (pullX (pullY q)))

@[simp] private theorem reverse_c (q : OpenSquare) : (reverse q).c=q.c := by
  simp [reverse,turnFrame,pullX,pullY]
@[simp] private theorem reverse_s (q : OpenSquare) : (reverse q).s=q.s := by
  simp [reverse,turnFrame,pullX,pullY]
@[simp] private theorem reverse_side (q : OpenSquare) : (reverse q).side=q.side := rfl

private theorem inside_reverse (q : OpenSquare) (x y : ℝ) :
    (reverse q).Inside x y ↔ q.Inside (4-x) (4-y) := by
  simp [reverse,inside_pullX,inside_pullY]

/-- Zero central angle is included. The outward square has no assumed
orientation: its nonnegative canonical sector is excluded geometrically. -/
theorem impossible (C B : OpenSquare)
    (cp : 0 < C.c) (cn : C.s ≤ 0) (canon : |C.s| ≤ C.c)
    (side : 1 < C.side) (same : C.side=B.side)
    (center : C.Inside 2 2) (north : C.Inside 2 (5/2))
    (central : C.Inside (47/20) (47/20))
    (missingNW : ¬ C.Inside (33/20) (47/20))
    (marker : B.Inside (47/20) (33/20)) (outward : B.Inside 3 (8/5))
    (missingCorner : ¬ B.Inside 3 1)
    (missingWall : ¬ B.Inside (1543/500) 2)
    (missingInward : ¬ B.Inside (113/50) 2)
    (missingBottom : ¬ B.Inside (12/5) 1)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → ¬ B.Inside z 1)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : False := by
  obtain ⟨D,dp,dcanon,dside,di,_⟩ := ClosedFrames.canonical_frame B
  have ds : 1 < D.side := by simpa only [dside,←same] using side
  have negative : D.s < 0 := by
    apply lt_of_not_ge
    intro positive
    exact C981CompletionShortOutwardLock.nonnegative_impossible D ds dp positive
      (by simpa only [abs_of_nonneg positive] using dcanon)
      ((di _ _).mpr marker) ((di _ _).mpr outward)
      (fun h => missingCorner ((di _ _).mp h))
      (fun h => missingWall ((di _ _).mp h))
      (fun h => missingInward ((di _ _).mp h))
      (fun z lo hi h => avoid z lo hi ((di _ _).mp h))
  have cnormal : Normal C.c (-C.s) :=
    ⟨neg_nonneg.mpr cn,by linarith only [(abs_le.mp canon).1],
      by nlinarith only [C.unit_normal]⟩
  have dnormal : Normal D.c (-D.s) :=
    ⟨neg_nonneg.mpr negative.le,by linarith only [(abs_le.mp dcanon).1],
      by nlinarith only [D.unit_normal]⟩
  apply C981CompletionNegativePair.impossible (reverse C) (reverse D) (-C.s) (-D.s)
    (by simp) (by simpa only [reverse_c] using cnormal)
    (by simp) (by simpa only [reverse_c] using dnormal)
    (by simpa only [reverse_side] using side)
    (by simpa only [reverse_side,dside] using same)
  · apply (inside_reverse C _ _).mpr
    norm_num
    exact center
  · apply (inside_reverse C _ _).mpr
    norm_num
    exact north
  · apply (inside_reverse C _ _).mpr
    norm_num
    exact central
  · intro h
    apply missingNW
    have point := (inside_reverse C _ _).mp h
    norm_num at point
    exact point
  · apply (inside_reverse D _ _).mpr
    norm_num
    exact (di _ _).mpr marker
  · apply (inside_reverse D _ _).mpr
    norm_num
    exact (di _ _).mpr outward
  · intro h
    apply missingBottom
    have point := (inside_reverse D _ _).mp h
    norm_num at point
    exact (di _ _).mp point
  · intro h
    apply missingCorner
    have point := (inside_reverse D _ _).mp h
    norm_num at point
    exact (di _ _).mp point
  · intro h
    apply missingWall
    have point := (inside_reverse D _ _).mp h
    norm_num at point
    exact (di _ _).mp point
  · intro x y h
    exact apart (4-x) (4-y)
      ⟨(inside_reverse C _ _).mp h.1,(di _ _).mp ((inside_reverse D _ _).mp h.2)⟩

#print axioms impossible
end N12Compact.C981CompletionShortCentralPair
