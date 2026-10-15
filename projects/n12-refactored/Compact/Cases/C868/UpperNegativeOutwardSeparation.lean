import Compact.Cases.C868.UpperNegativeOutwardProfile
import Compact.Cases.C868.UpperNegativeOutwardScalars
import Compact.Cases.C868.UpperNegativeInward
import Compact.Completion.C981.SupportForms

/-! Exhaustive actual-square separation in the lower-U top-marker branch.
The three rejected axes are proved from full support; the remaining H-U
face is stated explicitly, not silently discarded. -/
namespace N12Compact.C868.UpperNegativeOutward
open S12 S12Pilot C977CornerCubic FourSquareAnchors ThreeSquare ABTransverse
open MergedPending.NegativeUpperFaces
set_option Elab.async false
noncomputable section

private theorem projection (H B : OpenSquare) (h : Input H)
    (floor : (543/500)*H.s≤H.loU) (sharp : B.Inside (21/40) (1/8))
    (apart : ∀ x y,¬(H.Inside x y ∧ B.Inside x y)) :
    1000<525*H.c-961*H.s := by
  have angle := top_lower_tilt H h floor
  have bounds := normal_bounds h.normal
  apply lt_of_not_ge
  intro cap
  exact apart _ _ ⟨sharp_point H h floor
    (by linarith only [angle,bounds.1]) cap,sharp⟩

theorem right_axis_overlap (H B : OpenSquare) (h : Input H) (b : Faces B)
    (same : H.side=B.side) (floor : (543/500)*H.s≤H.loU)
    (sharp : B.Inside (21/40) (1/8))
    (apart : ∀ x y,¬(H.Inside x y ∧ B.Inside x y)) :
    B.loU<upper H B.c B.s := by
  have project := projection H B h floor sharp apart
  have project' : 1000<525*H.c+961*(-H.s) := by nlinarith only [project]
  have span' : 1<B.c+(143/500)*(-B.s) := by nlinarith only [b.upperSpan]
  have steep := UpperNegativeOutwardScalars.steep_of_projection H.c (-H.s) h.normal project'
  have small := UpperNegativeOutwardScalars.outward_sine_cap B.c (-B.s) b.normal span'
  have hb := normal_bounds h.normal
  have bb := normal_bounds b.normal
  let P := B.c*H.c+B.s*H.s
  let Q := -B.c*H.s+B.s*H.c
  have pn : 0≤P := by
    have first := mul_nonneg (show 0≤B.c by linarith only [bb.1])
      (show 0≤H.c by linarith only [hb.1])
    have last := mul_nonneg b.normal.1 h.normal.1
    dsimp only [P]; nlinarith only [first,last]
  have qn : 0≤Q := by
    have ordered := CommonCases.UnitCircleChord.cross_order
      (show 0≤B.c by linarith only [bb.1])
      (show 0≤H.c by linarith only [hb.1]) b.normal.2.2 h.normal.2.2
      b.normal.1 h.normal.1 (by linarith only [small,steep.1])
    dsimp only [Q]; linarith only [ordered]
  have formula : upper H B.c B.s=P*(H.loU+H.side)+Q*(H.loV+H.side) := by
    rw [C981CompletionSupportForms.upper_in_bands]
    change P*(H.loU+H.side/2)+Q*(H.loV+H.side/2)+
      H.side/2*(|P|+|Q|)=P*(H.loU+H.side)+Q*(H.loV+H.side)
    rw [abs_of_nonneg pn,abs_of_nonneg qn]
    ring
  have lowerV := lower_v H h
  have u := mul_nonneg pn (sub_nonneg.mpr floor)
  have v := mul_nonneg qn (sub_nonneg.mpr lowerV)
  have length := mul_nonneg (show 0≤1+P+Q by linarith only [pn,qn])
    (show 0≤H.side-1 by linarith only [h.side])
  have margin := UpperNegativeOutwardScalars.right_axis_margin
    H.c (-H.s) B.c (-B.s) h.normal b.normal project' span'
  have cap : B.loU+H.side≤B.c-B.s := by simpa only [same] using b.upperU
  rw [formula]
  dsimp only [P,Q] at u v length ⊢
  nlinarith only [u,v,length,margin,cap]

/-- The only remaining separating face is the merged square's own U
face. Its use in a later top-wall argument must retain the same B. -/
theorem separation (H B : OpenSquare) (h : Input H) (b : Faces B)
    (same : H.side=B.side) (floor : (543/500)*H.s≤H.loU)
    (marker : B.Inside (7/20) (-7/20)) (sharp : B.Inside (21/40) (1/8))
    (apart : ∀ x y,¬(H.Inside x y ∧ B.Inside x y)) :
    H.loU+H.side≤lower B H.c H.s := by
  have hb := normal_bounds h.normal
  have bb := normal_bounds b.normal
  have hcp : 0<H.c := by linarith only [hb.1]
  have bcp : 0<B.c := by linarith only [bb.1]
  have hAngle : 9*H.c≤ -35*H.s := by
    have angle := top_lower_tilt H h floor
    linarith only [angle,hcp]
  have bAngle : 9*B.c≤ -35*B.s := by
    linarith only [b.lowerSpan,bb.2.1,bcp]
  have reverse (c s : ℝ) (cp : 0<c) (sn : 0≤s) (unit : c^2+s^2=1) :
      ¬upper B c (-s)≤lower H c (-s) := by
    have u : c^2+(-s)^2=1 := by nlinarith only [unit]
    have first := strict_bounds B _ _ c (-s) u marker
    have last := strict_bounds H _ _ c (-s) u h.northwest
    intro sep
    nlinarith only [first.2,last.1,sep,cp,sn]
  have transverse (c s : ℝ) (cp : 0<c) (unit : c^2+s^2=1)
      (angle : 9*c≤35*s) :
      ¬(upper H s c≤lower B s c ∨ upper B s c≤lower H s c) := by
    have u : s^2+c^2=1 := by nlinarith only [unit]
    have nw := strict_bounds H _ _ s c u h.northwest
    have ne := strict_bounds H _ _ s c u h.northeast
    have bm := strict_bounds B _ _ s c u marker
    have bs := strict_bounds B _ _ s c u sharp
    rintro (sep | sep)
    · nlinarith only [ne.2,bm.1,sep,cp]
    · nlinarith only [nw.1,bs.2,sep,angle]
  have axes := CongruentSAT.faceSeparation_of_disjoint H B same apart
  change pairRadius H B≤|H.c*(centerX B-centerX H)+H.s*(centerY B-centerY H)| ∨
    pairRadius H B≤|-H.s*(centerX B-centerX H)+H.c*(centerY B-centerY H)| ∨
    pairRadius B H≤|B.c*(centerX B-centerX H)+B.s*(centerY B-centerY H)| ∨
    pairRadius B H≤|-B.s*(centerX B-centerX H)+B.c*(centerY B-centerY H)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius H nx ny+supportRadius B nx ny=R)
      (sep : R≤|nx*(centerX B-centerX H)+ny*(centerY B-centerY H)|) :=
    separated H B nx ny (by rwa [identity])
  rcases axes with hu | hv | bu | bv
  · rcases separateAxis _ _ _ (parallel_radius H B) hu with sep | sep
    · simpa only [(ownU H).2] using sep
    · exact False.elim (reverse H.c (-H.s) hcp h.normal.1 h.normal.2.2 (by simpa using sep))
  · exact False.elim (transverse H.c (-H.s) hcp h.normal.2.2
      (by nlinarith only [hAngle])
      (separateAxis _ _ _ (transverse_radius H B) hv))
  · have identity : supportRadius H B.c B.s+supportRadius B B.c B.s=pairRadius B H := by
      rw [add_comm]; exact parallel_radius B H
    rcases separateAxis _ _ _ identity bu with sep | sep
    · have bound := right_axis_overlap H B h b same floor sharp apart
      rw [(ownU B).1] at sep
      exact False.elim (not_le_of_gt bound sep)
    · exact False.elim (reverse B.c (-B.s) bcp b.normal.1 b.normal.2.2 (by simpa using sep))
  · have identity : supportRadius H (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B H := by
      rw [add_comm]; exact transverse_radius B H
    exact False.elim (transverse B.c (-B.s) bcp b.normal.2.2
      (by nlinarith only [bAngle])
      (separateAxis _ _ _ identity bv))

#print axioms right_axis_overlap
#print axioms separation
end
end N12Compact.C868.UpperNegativeOutward

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic ABTransverse
set_option Elab.async false
noncomputable section

/-- Actual-owner version of the surviving face. The existential frame is
a reindexing of B512, preserving its side, every point, and all four faces. -/
theorem negative_upper_outward_separation (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shapeH : H.side=(owner p 3072).side)
    (insideH : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y)
    (missing : ¬(owner p 512).Inside (113/50) 2)
    (floor : (543/500)*H.s≤(H.translated 2 2).loU) :
    ∃ B : OpenSquare,B.side=(owner p 512).side ∧
      (∀ x y,B.Inside x y↔(owner p 512).Inside x y) ∧
      UpperNegativeOutward.Faces (B.translated 2 2) ∧
      (H.translated 2 2).loU+H.side≤lower (B.translated 2 2) H.c H.s := by
  obtain ⟨B,shapeB,insideB,faces⟩ := southeast_outward_profile p hf missing
  have h := negative_upper_input p hf H normal shapeH insideH
  have same : (H.translated 2 2).side=(B.translated 2 2).side := by
    change H.side=B.side
    rw [shapeH,shapeB,show (owner p 3072).side=p.commonSide from p.congruent _,
      show (owner p 512).side=p.commonSide from p.congruent _]
  refine ⟨B,shapeB,insideB,faces,?_⟩
  apply UpperNegativeOutward.separation (H.translated 2 2) (B.translated 2 2)
    h faces same floor
  · norm_num only [inside_translated_iff]
    apply (insideB _ _).mpr
    simpa using seed_inside p hf 512 (by decide +kernel)
      (47/20,33/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    exact (insideB _ _).mpr (southeast_outward_points p hf missing).2
  · intro x y own
    exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (2+x) (2+y)
      ⟨(insideH _ _).mp ((inside_translated_iff H 2 2 x y).mp own.1),
        (insideB _ _).mp ((inside_translated_iff B 2 2 x y).mp own.2)⟩

#print axioms negative_upper_outward_separation
end
end N12Compact.C868
