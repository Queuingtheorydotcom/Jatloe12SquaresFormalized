import Compact.Cases.C868.NonnegativeSector
import Compact.Cases.C868.UpperNegativeCapGeometry
import Compact.Cases.C868.ActualTopBar
import Compact.Assembly.RowIdentity

/-! Complete original-owner C868 source assembly. The canonical upper
frame has two exhaustive signs. In the negative sign, the genuine
southwest near point, the same outward southeast square and the actual
top-wall bar feed the closed-point ending. No conditional orientation
sector is substituted for the original family. Source only, uncompiled. -/
namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic S12Completion
set_option Elab.async false

theorem negative_upper_frames_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) : False := by
  let N := H.translated 2 2
  have input : UpperNegativeCap.Data N := {
    toInput := negative_upper_input p hf H normal shape inside
    nearFloor := negative_upper_near_lower p hf H normal inside
    topCap := negative_upper_top_cap p hf H normal shape inside
    nearCap := (negative_upper_southeast_caps p hf H normal shape inside).2.1 }
  obtain ⟨T,tc,ts,st,it,_⟩ := ClosedFrames.positive_frame
    ((owner p 32768).translated 2 2)
  have size : 1<T.side := by
    rw [st]
    change 1<(owner p 32768).side
    rw [show (owner p 32768).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have ti (x y : ℝ) : T.Inside x y↔(owner p 32768).Inside (x+2) (y+2) := by
    simpa only [inside_translated_iff,add_comm] using it x y
  have far : T.Inside (-4/5) 1 := by
    apply (ti _ _).mpr
    norm_num only
    exact top_bar p hf (6/5) (by norm_num) (by norm_num)
  have marker : T.Inside 0 (543/500) := by
    apply (ti _ _).mpr
    norm_num only
    simpa using seed_inside p hf 32768 (by decide +kernel)
      (2,1543/500) (by decide +kernel)
  have disjoint (x y : ℝ) : ¬(N.Inside x y ∧ T.Inside x y) := by
    rintro ⟨hn,ht⟩
    have actual : H.Inside (x+2) (y+2) := by
      simpa only [add_comm] using (inside_translated_iff H 2 2 x y).mp hn
    exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (x+2) (y+2) ⟨(inside _ _).mp actual,(ti _ _).mp ht⟩
  exact UpperNegativeCap.impossible N T input size tc ts far marker disjoint

theorem family_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨H,hc,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame (owner p 3072)
  have negative := upper_negative_required p hf H hc canonical shape inside
  have normal : Normal H.c (-H.s) :=
    ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
      by nlinarith only [H.unit_normal]⟩
  exact negative_upper_frames_impossible p hf H normal shape inside

theorem family_excluded : ExcludesFamily family := family_impossible

/-- The unchanged original table places C868 at position 455. The
inherited retained-row identity theorem supplies coverage of every row
with this historical ID; the geometry does not replace that obligation. -/
private theorem row_lookup :
    (RowIdentity.rowAt 455).originalId=868 ∧
      (RowIdentity.rowAt 455).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=868 → r.groups=family :=
  RowIdentity.family_at 455 868 family row_lookup

theorem case_excluded : ExcludesCase 868 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms negative_upper_frames_impossible
#print axioms family_impossible
#print axioms case_excluded
end N12Compact.C868
