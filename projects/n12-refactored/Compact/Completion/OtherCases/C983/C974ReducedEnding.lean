import Compact.Completion.OtherCases.C983.C974LowerFace
import Compact.Completion.OtherCases.C983.C974CornerEnding
import Compact.Completion.OtherCases.C983.C974LocalData

/-! Join of C974-THREE-SQUARE-ENDING §§2–4. The cited positive-frame,
angle, and face reductions remain explicit. This is not the full local
Theorem 1 from raw owned/excluded points alone. -/
namespace N12Compact.Completion.OtherCases.C983.C974ReducedEnding
open S12 S12Pilot
set_option Elab.async false

theorem impossible (K W C : OpenSquare) (h : C974LowerFace.Input K W)
    (far : W.Inside (9/5) 0) (same : W.side=C.side)
    (walls : ∀ x y,C.Inside x y → x≤3 ∧ -1≤y)
    (corner : C.Inside 2 0) (missing : ¬C.Inside 2 (1/2))
    (apart : ∀ x y,¬(W.Inside x y ∧ C.Inside x y)) : False := by
  let B := W.translated 1 0
  let D := C.translated 1 0
  have lower := C974LowerFace.lower_face K W h
  have wall : C974WallReach.Data B :=
    { sideLarge := h.sideLarge
      cosine := lt_of_lt_of_le h.wSine h.wCanonical
      sine := h.wSine
      canonical := h.wCanonical
      slope := h.wSlope
      origin := by dsimp only [B]; norm_num only [inside_translated_iff]; exact h.wO
      far := by dsimp only [B]; norm_num only [inside_translated_iff]; exact far
      upperU := by simpa only [B,OpenSquare.translated,mul_one,mul_zero,add_zero] using h.wUpperU
      upperV := by
        dsimp only [B,OpenSquare.translated]
        linarith only [h.wUpperV]
      lowerFace := by
        simpa only [B,OpenSquare.translated,mul_one,mul_zero,add_zero] using lower }
  apply C974CornerEnding.impossible B D wall same
  · intro x y own
    have original : C.Inside (1+x) y := by
      simpa only [D,inside_translated_iff,zero_add] using own
    have bound := walls _ _ original
    constructor <;> linarith only [bound.1,bound.2]
  · dsimp only [D]
    norm_num only [inside_translated_iff]
    exact corner
  · dsimp only [D]
    norm_num only [inside_translated_iff]
    exact missing
  · intro x y both
    exact apart (1+x) y
      ⟨by simpa only [B,inside_translated_iff,zero_add] using both.1,
       by simpa only [D,inside_translated_iff,zero_add] using both.2⟩

/-- The raw manuscript contract plus the separately translated positive
reductions, kept visibly separate until their prerequisite chapters join. -/
theorem of_raw_and_reductions (K W C : OpenSquare)
    (raw : C974LocalData.Input K W C) (reduced : C974LowerFace.Input K W) : False :=
  impossible K W C reduced raw.farW (raw.sameKW.symm.trans raw.sameKC)
    raw.cornerWalls raw.corner raw.missingCorner raw.apartWC

#print axioms impossible
#print axioms of_raw_and_reductions
end N12Compact.Completion.OtherCases.C983.C974ReducedEnding
