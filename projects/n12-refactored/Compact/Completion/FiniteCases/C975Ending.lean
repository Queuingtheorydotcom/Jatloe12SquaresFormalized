import Compact.Completion.FiniteCases.C975NortheastSign

/-! Complete actual C975 ending. The two genuine singleton roots first
restrict the one merged top. Both NE alternatives and every canonical
sign then close continuously. This source proof retains all original
owners, strict interiors and weak boundary contacts. It is uncompiled. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

/-- With the lower strict anchor, marker and elbow, the omitted upper
point can exit only at lower-u. This is a point-to-face consequence,
not an assumed support bound. -/
theorem mixed_lower_face (N : OpenSquare) (s : ℝ) (signed : N.s= -s)
    (cp : 0<N.c) (sp : 0<s)
    (marker : N.Inside (7/20) (-13/20)) (inward : N.Inside 0 (-37/50))
    (elbow : N.Inside (13/50) 0) (missing : ¬N.Inside 0 (-1/2)) :
    (1/2)*s≤N.loU := by
  have m := marker
  have f := inward
  have g := elbow
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,
    zero_add,add_zero] at m f g
  apply le_of_not_gt
  intro low
  apply missing
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,
    zero_add,add_zero]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [low,m.2.1,f.2.2.1,g.2.2.2,cp,sp]

/-- The original twelve-square family is impossible. In particular the
northwest marker is never separated from its actual top34816 owner. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨R,cp,canonicalR,shapeR,insideR,_⟩ := ClosedFrames.canonical_frame (owner p 1024)
  have sn := northeast_negative p hf R shapeR insideR cp canonicalR
  have order : -R.s≤R.c := by linarith only [(abs_le.mp canonicalR).1]
  obtain ⟨W,wp,canonicalW,shapeW,insideW,_⟩ := ClosedFrames.canonical_frame (owner p 34816)
  have topSign := top_negative_shallow p hf R W shapeR insideR cp sn order
    shapeW insideW wp canonicalW
  have lower : (owner p 34816).Inside 2 (5/2) :=
    (insideW _ _).mp (negative_top_lower p hf W wp topSign.1.le
      (by linarith only [(abs_le.mp canonicalW).1]) shapeW insideW)
  let N := R.translated 2 3
  have nInside (x y : ℝ) : N.Inside x y↔(owner p 1024).Inside (2+x) (3+y) :=
    (inside_translated_iff R 2 3 x y).trans (insideR (2+x) (3+y))
  have nSide : 1<N.side := by simpa only [N,OpenSquare.translated,shapeR] using side p 1024
  have signed : N.s= -(-R.s) := by dsimp only [N,OpenSquare.translated]; ring
  have positive : 0< -R.s := by linarith only [sn]
  have marker : N.Inside (7/20) (-13/20) :=
    (nInside _ _).mpr (by convert (fixed p hf).northeastMarker using 1 <;> norm_num)
  have elbow : N.Inside (13/50) 0 :=
    (nInside _ _).mpr (by convert (northeast_selection p hf).1 using 1 <;> norm_num)
  have origin : ¬N.Inside 0 0 := by
    intro own
    apply foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (top_origin p hf)
    convert (nInside _ _).mp own using 1 <;> norm_num
  have right : ¬N.Inside 1 (-11/25) := by
    intro own
    apply foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (C975IncomingCut.right_high p hf)
    convert (nInside _ _).mp own using 1 <;> norm_num
  have alternative := negative_alternative p hf N nInside
  have profile := C976NegativeTop.faces N (-R.s) signed nSide cp positive order
    marker elbow origin right alternative
  rcases alternative with outer | mixed
  · have upper : (owner p 34816).Inside 2 (131/50) :=
      vertical_segment _ 2 (5/2) 3 (131/50) lower (top_origin p hf)
        (by norm_num) (by norm_num) (by norm_num)
    apply apart _ p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) 2 (131/50) ⟨?_,upper⟩
    convert (nInside _ _).mp outer.1 using 1 <;> norm_num
  · have missing : ¬N.Inside 0 (-1/2) := by
      intro own
      apply foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ lower
      convert (nInside _ _).mp own using 1 <;> norm_num
    have face := mixed_lower_face N (-R.s) signed cp positive marker mixed.1 elbow missing
    have cu : N.c≤1 := by nlinarith only [N.unit_normal,sq_nonneg N.s,cp]
    linarith only [face,profile.upperU,nSide,cu,positive]

end
#print axioms mixed_lower_face
#print axioms impossible
end N12Compact.FiniteCases.C975Selection
