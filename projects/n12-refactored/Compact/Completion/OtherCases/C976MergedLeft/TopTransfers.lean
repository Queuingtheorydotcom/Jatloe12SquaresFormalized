import Compact.Completion.OtherCases.C976MergedLeft.TopOnlyReach
import Compact.Completion.C981.ShallowWall

/-! Literal actual-coordinate top advances for the two northeast
alternatives. Reflection changes the physical coordinates and the frame
sign explicitly; no canonical choice is silently transferred. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open S12 S12Pilot
set_option Elab.async false

noncomputable def reflectedTop (q : OpenSquare) : OpenSquare :=
  (turnFrame (turnFrame (pullX q))).translated 2 3

theorem reflectedTop_inside (q : OpenSquare) (x y : ℝ) :
    (reflectedTop q).Inside x y↔q.Inside (2-x) (3+y) := by
  dsimp only [reflectedTop]
  rw [inside_translated_iff,turnFrame_inside,turnFrame_inside,inside_pullX]
  rw [show (4:ℝ)-(2+x)=2-x by ring]

theorem mixed_top_advance (N W : OpenSquare)
    (nSide : 1<N.side) (wSide : 1<W.side)
    (cp : 0<N.c) (sn : 0≤N.s) (order : N.s≤N.c)
    (elbow : N.Inside (113/50) 3) (inward : N.Inside 2 (113/50))
    (missing : ¬N.Inside (113/50) 2)
    (marker : W.Inside 2 (1543/500)) (anchor : W.Inside (8/5) 3)
    (wall : ∀ x y,W.Inside x y → y≤4)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) : W.Inside (127/100) 3 := by
  have cap := C981CompletionShallowCap.negative_cap (reflectedTop N) nSide
    (by simpa only [reflectedTop,OpenSquare.translated,turnFrame,pullX,neg_neg] using cp)
    (by dsimp only [reflectedTop,OpenSquare.translated,turnFrame,pullX]; linarith only [sn])
    (by dsimp only [reflectedTop,OpenSquare.translated,turnFrame,pullX]; linarith only [order])
    ((reflectedTop_inside _ _ _).mpr (by convert elbow using 1 <;> norm_num))
    ((reflectedTop_inside _ _ _).mpr (by convert inward using 1 <;> norm_num))
    (by
      intro own
      apply missing
      convert (reflectedTop_inside _ _ _).mp own using 1 <;> norm_num)
  have point := C981CompletionShallowWall.point (reflectedTop W) wSide
    (by
      intro x y own
      have bound := wall (2-x) (3+y) ((reflectedTop_inside _ _ _).mp own)
      linarith only [bound])
    ((reflectedTop_inside _ _ _).mpr (by convert marker using 1 <;> norm_num))
    ((reflectedTop_inside _ _ _).mpr (by convert anchor using 1 <;> norm_num))
    (by
      intro x y region own
      exact apart (2-x) (3+y) ⟨(reflectedTop_inside _ _ _).mp (cap x y region),
        (reflectedTop_inside _ _ _).mp own⟩)
  convert (reflectedTop_inside _ _ _).mp point using 1 <;> norm_num

theorem top_only_advance (N W : OpenSquare)
    (nSide : 1<N.side) (wSide : 1<W.side)
    (cp : 0<N.c) (sn : 0≤N.s) (order : N.s≤N.c)
    (marker : N.Inside (47/20) (47/20)) (elbow : N.Inside (113/50) 3)
    (sharp : N.Inside (101/40) (17/8)) (missingF : ¬N.Inside 2 (113/50))
    (missingC : ¬N.Inside 3 3)
    (bar : ∀ y : ℝ,113/50≤y → y≤64/25 → ¬N.Inside 3 y)
    (origin : W.Inside 2 3) (wall : ∀ x y,W.Inside x y → y≤4)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) : W.Inside (6/5) 3 := by
  have missingP : ¬N.Inside 2 3 := fun own => apart 2 3 ⟨own,origin⟩
  have inward := TopOnlyLeftPoint.point_original N nSide marker elbow sharp missingF missingP missingC bar
  have tip := positive_tip (N.translated 2 2) nSide cp sn order
    (by norm_num only [inside_translated_iff]; exact marker)
    (by norm_num only [inside_translated_iff]; exact elbow)
    (by norm_num only [inside_translated_iff]; exact missingF)
    (by norm_num only [inside_translated_iff]; exact missingP)
    (by norm_num only [inside_translated_iff]; exact missingC)
    (by
      intro y low high own
      apply bar (2+y) (by linarith only [low]) (by linarith only [high])
      convert (inside_translated_iff _ _ _ _ _).mp own using 1 <;> ring)
  have tipOriginal : N.Inside (1013/500) 3 := by
    convert (inside_translated_iff _ _ _ _ _).mp tip using 1 <;> norm_num
  have reach := top_only_reach (reflectedTop W) wSide
    (by
      intro x y own
      have bound := wall (2-x) (3+y) ((reflectedTop_inside _ _ _).mp own)
      linarith only [bound])
    ((reflectedTop_inside _ _ _).mpr (by convert origin using 1 <;> norm_num))
    (by
      intro own
      apply apart (1013/500) 3 ⟨tipOriginal,?_⟩
      convert (reflectedTop_inside _ _ _).mp own using 1 <;> norm_num)
    (by
      intro own
      apply apart 2 (131/50) ⟨inward,?_⟩
      convert (reflectedTop_inside _ _ _).mp own using 1 <;> norm_num)
  convert (reflectedTop_inside _ _ _).mp reach using 1 <;> norm_num

#print axioms mixed_top_advance
#print axioms top_only_advance
end N12Compact.Completion.OtherCases.C976MergedLeft
