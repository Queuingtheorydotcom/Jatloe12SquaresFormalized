import Compact.Completion.OtherCases.MergedPending.SingletonBars
import Compact.Completion.CommonCases.WallSignFromSingleton

/-! Literal original-owner wall cuts for pending merged families.
The upper/right cuts are half-turns of the same physical wall, together
with its actual container wall and foreign singleton point. In particular
the right result requires actual singleton32: it cannot be applied to
C867 or used to manufacture a right-wall owner for C683.
Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
open CommonCases.WallSignFromSingleton
set_option Elab.async false
noncomputable section

theorem left_wall (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 4096∈family) (two : 2∈family) :
    2<centerY (owner p 4096) ∧
      ∀ y : ℝ,111/50≤y → y≤239/100 → (owner p 4096).Inside 1 y := by
  have mark := seed family p hf 4096 member (457/500,2) (by decide +kernel)
  have sw := missing_marker family p hf 4096 member 8 (by decide +kernel)
  have nw := missing_marker family p hf 4096 member 11 (by decide +kernel)
  have foreign := singleton_left family p hf two (87/50) (by norm_num) le_rfl
  norm_num [S12.marker] at mark sw nw
  exact left_chord _ (side p 4096) (fun x y own => (box p 4096 x y own).1)
    mark sw nw (fun own => apart family p hf 4096 2 member two (by decide) _ _ ⟨own,foreign⟩)

theorem bottom_wall (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 8192∈family) (one : 1∈family) :
    2<centerX (owner p 8192) ∧
      ∀ x : ℝ,111/50≤x → x≤239/100 → (owner p 8192).Inside x 1 :=
  original_bottom family p hf 8192 member one (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem top_wall (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 32768∈family) (sixteen : 16∈family) :
    centerX (owner p 32768)<2 ∧
      ∀ x : ℝ,161/100≤x → x≤89/50 → (owner p 32768).Inside x 3 := by
  let W := owner p 32768
  let Q := pullY (pullX W)
  have actual (x y : ℝ) : Q.Inside x y ↔ W.Inside (4-x) (4-y) := by
    simp only [Q,inside_pullY,inside_pullX]
  have mark := seed family p hf 32768 member (2,1543/500) (by decide +kernel)
  have ne := missing_marker family p hf 32768 member 10 (by decide +kernel)
  have nw := missing_marker family p hf 32768 member 11 (by decide +kernel)
  have foreign := singleton_top family p hf sixteen (113/50) le_rfl (by norm_num)
  norm_num [S12.marker] at mark ne nw
  have cut := bottom_chord Q (side p 32768)
    (fun x y own => by
      have wall := (box p 32768 _ _ ((actual x y).mp own)).2.2.2
      linarith only [wall])
    (by rw [actual]; norm_num; exact mark)
    (by rw [actual]; norm_num; exact ne)
    (by rw [actual]; norm_num; exact nw)
    (by rw [actual]; norm_num
        exact fun own => apart family p hf 32768 16 member sixteen (by decide) _ _ ⟨own,foreign⟩)
  constructor
  · have sign := cut.1
    simp only [Q,center_pullY_x,center_pullX_x] at sign
    linarith only [sign]
  · intro x low high
    have point := cut.2 (4-x) (by linarith only [high]) (by linarith only [low])
    have original := (actual _ _).mp point
    convert original using 1 <;> ring

theorem right_wall (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 16384∈family) (thirtytwo : 32∈family) :
    centerY (owner p 16384)<2 ∧
      ∀ y : ℝ,161/100≤y → y≤89/50 → (owner p 16384).Inside 3 y := by
  let W := owner p 16384
  let Q := pullY (pullX W)
  have actual (x y : ℝ) : Q.Inside x y ↔ W.Inside (4-x) (4-y) := by
    simp only [Q,inside_pullY,inside_pullX]
  have mark := seed family p hf 16384 member (1543/500,2) (by decide +kernel)
  have ne := missing_marker family p hf 16384 member 10 (by decide +kernel)
  have se := missing_marker family p hf 16384 member 9 (by decide +kernel)
  have foreign := singleton_right family p hf thirtytwo (113/50) le_rfl (by norm_num)
  norm_num [S12.marker] at mark ne se
  have cut := left_chord Q (side p 16384)
    (fun x y own => by
      have wall := (box p 16384 _ _ ((actual x y).mp own)).2.1
      linarith only [wall])
    (by rw [actual]; norm_num; exact mark)
    (by rw [actual]; norm_num; exact ne)
    (by rw [actual]; norm_num; exact se)
    (by rw [actual]; norm_num
        exact fun own => apart family p hf 16384 32 member thirtytwo (by decide) _ _ ⟨own,foreign⟩)
  constructor
  · have sign := cut.1
    simp only [Q,center_pullY_y,center_pullX_y] at sign
    linarith only [sign]
  · intro y low high
    have point := cut.2 (4-y) (by linarith only [high]) (by linarith only [low])
    have original := (actual _ _).mp point
    convert original using 1 <;> ring

end
#print axioms left_wall
#print axioms top_wall
#print axioms right_wall
end N12Compact.MergedPending
