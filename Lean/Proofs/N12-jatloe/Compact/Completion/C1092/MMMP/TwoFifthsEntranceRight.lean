import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNortheast
import Compact.Completion.CommonCases.OriginalOwners

/-! The entire short bar, the real right wall and the closed MMMP center
sign of one actual Q10. Neither G8 status of Q5 is assumed. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

theorem right_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50)) :
    C1092TwoFifths.Right ((owners p 10).translated 2 2) := by
  let R := (owners p 10).translated 2 2
  have actual (x y : ℝ) : R.Inside x y↔(owners p 10).Inside (2+x) (2+y) :=
    inside_translated_iff _ _ _ _ _
  have cut : 2≤centerY (owners p 10) := by
    have h : 2≤centerY (pullX (owners p 10)) := by
      simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 2).1
    have center : centerY (pullX (owners p 10))=centerY (owners p 10) := by
      dsimp [centerY,pullX]
      ring
    rwa [center] at h
  have shifted : centerY R=centerY (owners p 10)-2 := by
    dsimp [R,OpenSquare.translated,centerY]
    linear_combination -2*(owners p 10).unit_normal
  refine ⟨?_,?_,?_⟩
  · intro y low high
    apply (actual _ _).mpr
    norm_num
    exact CommonCases.OriginalOwners.vertical_segment _ _ _ _ _
      near (C1092MMMPRightFar.point p hf hb) (by norm_num)
      (by linarith only [low]) (by linarith only [high])
  · intro x y own
    have box := p.contained _ _ _ ((actual x y).mp own)
    linarith only [box.2.1]
  · rw [shifted]
    linarith only [cut]

/-- Reassembling already produced actual profiles introduces no new
geometric assumption: both disjointness relations and side equalities
come from the original normalized packing. -/
theorem input_of_profiles (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (E N : OpenSquare) (eSide : E.side=(owners p 5).side)
    (eActual : ∀ x y,E.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (np : C1092MMMPNortheastActualSign.PositiveActual p N)
    (e : C1092TwoFifths.Southeast E) (halfHigh : 3*N.s≤1+N.c) :
    C1092TwoFifths.Input E N ((owners p 10).translated 2 2) where
  southeast := e
  northeast := (northeast_core p hf hb N np).complete halfHigh
  right := right_profile p hf hb near
  sameER := eSide.trans (side_same p 5 10)
  sameNR := np.side.trans (side_same p 6 10)
  apartER := by
    intro x y own
    exact owners_disjoint p hf 5 10 (by decide) _ _
      ⟨(eActual x y).mp own.1,(inside_translated_iff _ _ _ _ _).mp own.2⟩
  apartNR := by
    intro x y own
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨(np.actual x y).mp own.1,(inside_translated_iff _ _ _ _ _).mp own.2⟩

#print axioms right_profile
#print axioms input_of_profiles
end N12Compact.C1092MMMPTwoFifthsEntrance
