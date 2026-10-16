import Compact.Cases.C868.SoutheastGeometry
import Compact.Completion.OtherCases.OutwardBarFrame
import Compact.Geometry.C977CornerCubic

/-! Full southeast support in the negative-H outward branch. All four
faces refer to one reindexing of the actual B512. The reflected foreign
segment is the actual bottom owner's entire bar. -/
namespace N12Compact.C868.UpperNegativeOutward
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure Faces (B : OpenSquare) : Prop where
  normal : Normal B.c (-B.s)
  side : 1<B.side
  lowerU : (13/50)*B.c≤B.loU
  lowerV : -(4/5)*B.s-B.c≤B.loV
  upperU : B.loU+B.side≤B.c-B.s
  upperV : B.loV+B.side≤-(543/500)*B.s
  upperSpan : 1<B.c-(143/500)*B.s
  lowerSpan : 1<(37/50)*B.c-B.s

/-- Reflection carries the whole outward-bar theorem, including both
corner markers, into the original southeast frame. -/
theorem faces_original (B : OpenSquare) (normal : Normal B.c (-B.s))
    (side : 1<B.side)
    (marker : B.Inside (47/20) (33/20))
    (outward : B.Inside 3 (87/50))
    (missingG : ¬B.Inside (113/50) 2)
    (missingR : ¬B.Inside (1543/500) 2)
    (missingP : ¬B.Inside 3 1)
    (missingH : ¬B.Inside (1543/500) 1)
    (avoid : ∀ x : ℝ,113/50≤x → x≤14/5 → ¬B.Inside x 1) :
    Faces (B.translated 2 2) := by
  have bounds := normal_bounds normal
  have facts := Completion.OtherCases.OutwardBarFrame.faces_original (pullY B) side
    (by change 0<B.c; linarith only [bounds.1]) normal.1 normal.2.1
    (by norm_num only [inside_pullY]; exact marker)
    (by norm_num only [inside_pullY]; exact outward)
    (by norm_num only [inside_pullY]; exact missingG)
    (by norm_num only [inside_pullY]; exact missingR)
    (by norm_num only [inside_pullY]; exact missingP)
    (by norm_num only [inside_pullY]; exact missingH)
    (by intro x low high; norm_num only [inside_pullY]; exact avoid x low high)
  have loU := facts.lowerU
  have loV := facts.lowerV
  have hiU := facts.upperU
  have hiV := facts.upperV
  have short := facts.upperSpan
  have long := facts.lowerSpan
  dsimp only [pullY,OpenSquare.translated] at loU loV hiU hiV short long
  refine ⟨normal,side,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [OpenSquare.translated]
  · linarith only [loU]
  · linarith only [hiV]
  · linarith only [hiU]
  · linarith only [loV]
  · linarith only [short]
  · linarith only [long]

end N12Compact.C868.UpperNegativeOutward

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

/-- The profile is constructed for the very frame supplied by the actual
outward sign theorem; it never substitutes a separately chosen square. -/
theorem southeast_outward_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    ∃ B : OpenSquare,B.side=(owner p 512).side ∧
      (∀ x y,B.Inside x y↔(owner p 512).Inside x y) ∧
      UpperNegativeOutward.Faces (B.translated 2 2) := by
  obtain ⟨B,cp,sn,order,shape,inside⟩ := southeast_outward_frame p hf missing
  have normal : Normal B.c (-B.s) :=
    ⟨by linarith only [sn],order,by nlinarith only [B.unit_normal]⟩
  have size : 1<B.side := by
    rw [shape,show (owner p 512).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have foreign (mask : Nat) (hm : mask∈family) (different : 512≠mask)
      (P : ℚ×ℚ) (hp : P∈seedPoints (maskSupport mask)) :
      ¬B.Inside P.1 P.2 := fun own =>
    apart p hf 512 mask (by decide +kernel) hm different _ _
      ⟨(inside _ _).mp own,seed_inside p hf mask hm P hp⟩
  refine ⟨B,shape,inside,?_⟩
  apply UpperNegativeOutward.faces_original B normal size
  · apply (inside _ _).mpr
    simpa using seed_inside p hf 512 (by decide +kernel)
      (47/20,33/20) (by decide +kernel)
  · apply (inside _ _).mpr
    simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 7
  · exact fun own => missing ((inside _ _).mp own)
  · simpa using foreign 16416 (by decide +kernel) (by decide +kernel)
      (1543/500,2) (by decide +kernel)
  · simpa using foreign 12 (by decide +kernel) (by decide +kernel)
      (3,1) (by decide +kernel)
  · simpa using foreign 12 (by decide +kernel) (by decide +kernel)
      (1543/500,1) (by decide +kernel)
  · intro x low high own
    exact apart p hf 512 8192 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x 1
      ⟨(inside _ _).mp own,bottom_bar p hf x low high⟩

#print axioms southeast_outward_profile
end
end N12Compact.C868
