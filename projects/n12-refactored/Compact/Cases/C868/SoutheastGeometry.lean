import Compact.Cases.C868.ActualBars
import Compact.Completion.OtherCases.CrossedElbow
import Compact.Completion.OtherCases.OutwardBarPoint
import Compact.Completion.CommonCases.OutwardPoint

/-! Both surviving southeast configurations retain the same physical
B512.  Its inward-G branch reaches the right crosspoint; its omitted-G
branch has a derived negative frame and two strict outward support points.
Neither branch is asserted to exclude the original C868 family. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_size (p : NormalizedPacking) : 1<(owner p 512).side := by
  rw [show (owner p 512).side=p.commonSide from p.congruent _]
  exact p.side_gt_one

private theorem southeast_marker (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : (owner p 512).Inside (47/20) (33/20) := by
  simpa using seed_inside p hf 512 (by decide +kernel)
    (47/20,33/20) (by decide +kernel)

private theorem southeast_f8 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : (owner p 512).Inside 3 (87/50) := by
  simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 7

private theorem southeast_foreign (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (hm : mask∈family)
    (hne : 512≠mask) (P : ℚ×ℚ) (hp : P∈seedPoints (maskSupport mask)) :
    ¬(owner p 512).Inside P.1 P.2 := fun own =>
  apart p hf 512 mask (by decide +kernel) hm hne _ _
    ⟨own,seed_inside p hf mask hm P hp⟩

private theorem southeast_avoids_bottom (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (x : ℝ) (low : 113/50≤x) (high : x≤14/5) :
    ¬(owner p 512).Inside x 1 := fun own =>
  apart p hf 512 8192 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨own,bottom_bar p hf x low high⟩

/-- The far endpoint comes from the actual full bottom bar.  The other
excluded crosspoint belongs to A256 by its singleton-segment proof. -/
theorem southeast_right_crosspoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (inward : (owner p 512).Inside (113/50) 2) :
    (owner p 512).Inside (5/2) 2 := by
  by_contra missing
  apply Completion.OtherCases.CrossedElbow.impossible_original (owner p 512)
    (4/5) (southeast_size p) (by norm_num) le_rfl
    (southeast_marker p hf) inward (southeast_f8 p hf) missing
  · intro own
    exact apart p hf 256 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨(southwest_crosspoints p hf).2,own⟩
  · norm_num only
    exact southeast_avoids_bottom p hf _ (by norm_num) le_rfl

/-- The sign conclusion is for a reindexing of B512, with every owned
point unchanged.  No sign of A256, H3072 or the actual bottom wall is used. -/
theorem southeast_outward_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    ∃ B : OpenSquare,0<B.c ∧ B.s<0 ∧ -B.s≤B.c ∧
      B.side=(owner p 512).side ∧
      (∀ x y,B.Inside x y↔(owner p 512).Inside x y) := by
  obtain ⟨B,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame (owner p 512)
  have side : 1<B.side := by simpa only [shape] using southeast_size p
  have sign : B.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    apply C981CompletionOutwardAnchor.nonnegative_impossible B side cp nonnegative
      (by simpa only [abs_of_nonneg nonnegative] using canonical)
      ((inside _ _).mpr (southeast_marker p hf))
      ((inside _ _).mpr (southeast_g8 p hf))
    · intro own
      exact southeast_foreign p hf 12 (by decide +kernel) (by decide +kernel)
        (3,1) (by decide +kernel) ((inside _ _).mp own)
    · intro own
      exact southeast_foreign p hf 16416 (by decide +kernel) (by decide +kernel)
        (1543/500,2) (by decide +kernel) ((inside _ _).mp own)
    · exact fun own => missing ((inside _ _).mp own)
    · intro x low high own
      exact southeast_avoids_bottom p hf x low high ((inside _ _).mp own)
  exact ⟨B,cp,sign,by simpa only [abs_of_neg sign] using canonical,shape,inside⟩

/-- The two literal strict support points follow from the whole bottom
bar and the paired southeast corner.  Reflection is applied to every
premise, including both genuine corner markers. -/
theorem southeast_outward_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    (owner p 512).Inside (123/50) (201/100) ∧
      (owner p 512).Inside (101/40) (17/8) := by
  let q := pullY (owner p 512)
  have marker : q.Inside (47/20) (47/20) := by
    norm_num only [q,inside_pullY]
    exact southeast_marker p hf
  have outward : q.Inside 3 (113/50) := by
    norm_num only [q,inside_pullY]
    exact southeast_f8 p hf
  have upper : q.Inside 3 (12/5) := by
    norm_num only [q,inside_pullY]
    exact southeast_g8 p hf
  have inward : ¬q.Inside (113/50) 2 := by
    norm_num only [q,inside_pullY]
    exact missing
  have wall : ¬q.Inside (1543/500) 2 := by
    norm_num only [q,inside_pullY]
    exact southeast_foreign p hf 16416 (by decide +kernel) (by decide +kernel)
      (1543/500,2) (by decide +kernel)
  have corner : ¬q.Inside 3 3 := by
    norm_num only [q,inside_pullY]
    exact southeast_foreign p hf 12 (by decide +kernel) (by decide +kernel)
      (3,1) (by decide +kernel)
  have cornerMarker : ¬q.Inside (1543/500) 3 := by
    norm_num only [q,inside_pullY]
    exact southeast_foreign p hf 12 (by decide +kernel) (by decide +kernel)
      (1543/500,1) (by decide +kernel)
  have bar (x : ℝ) (low : 113/50≤x) (high : x≤14/5) : ¬q.Inside x 3 := by
    norm_num only [q,inside_pullY]
    exact southeast_avoids_bottom p hf x low high
  have first := CommonCases.OutwardPoint.point_original q (southeast_size p)
    marker outward upper inward wall corner cornerMarker bar
  have second := Completion.OtherCases.OutwardBarPoint.point_original q (southeast_size p)
    marker outward upper inward wall corner cornerMarker bar
  norm_num only [q,inside_pullY] at first second
  exact ⟨first,second⟩

#print axioms southeast_right_crosspoint
#print axioms southeast_outward_frame
#print axioms southeast_outward_points
end
end N12Compact.C868
