import Compact.Completion.FiniteCases.C975TopOrigin
import Compact.Completion.OtherCases.OutwardBarFrame
import Compact.Completion.OtherCases.OutwardPair
import Compact.Completion.OtherCases.UpperBarPoint

/-! Further actual C975 cuts after the genuine merged-top origin.
The full outward-versus-mixed support argument needs only exclusions
of the northwest marker and top origin from NE1024. Both exclusions
come from the same actual merged34816, which is retained throughout.
No distinct northwest square or C1090 early table is constructed.
Source translation only; this is not a whole-family exclusion. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases C1092WallProfileScalars
set_option Elab.async false
noncomputable section

/-- The complete strict right segment stays in actual16384. -/
theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 113/50≤y) (high : y≤64/25) :
    (owner p 16384).Inside 3 y := by
  let t := (10/3)*(y-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (owner p 16384) 3 (113/50) 3 (64/25) t
    (fixed p hf).rightF9 (C975IncomingCut.right_high p hf) tn tu using 1 <;>
      dsimp only [t] <;> ring

/-- Omission of S's G6 derives the same physical frame and all of its
continuous outward bounds from actual corner12 and bottom8192. -/
theorem southeast_outward_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=(owner p 512).side ∧
      (∀ x y,r.Inside x y↔(pullY (owner p 512)).Inside x y) ∧
      OutwardBarPoint.Faces (r.translated 2 2) := by
  have h := selection_input p hf
  exact OutwardBarFrame.frame_original (pullY (owner p 512)) (side p 512)
    (by norm_num [inside_pullY]; exact h.markerS)
    (by norm_num [inside_pullY]; exact h.f8)
    (by norm_num [inside_pullY]; exact h.g8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact h.rightMarker)
    (by norm_num [inside_pullY]; exact h.corner)
    (by norm_num [inside_pullY]; exact h.cornerMarker)
    (by
      intro x low high own
      norm_num [inside_pullY] at own
      exact h.bottom x low high own)

/-- In the top-only NE alternative the sharp point uses actual34816's
new origin, actual corner48, and the whole actual16384 right segment. -/
theorem northeast_upper_sharp (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missingF5 : ¬(owner p 1024).Inside 2 (113/50)) :
    (owner p 1024).Inside (101/40) (17/8) := by
  have corner : (owner p 48).Inside 3 3 := by
    convert seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
      using 1 <;> norm_num
  exact UpperBarPoint.point_original (owner p 1024) (side p 1024)
    (fixed p hf).northeastMarker (northeast_f7_point p hf) missingF5
    (foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (top_origin p hf))
    (foreign p hf 1024 48 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ corner)
    (fun y low high => foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (right_bar p hf y low high))

/-- The mixed NE alternative excludes an outward S by the complete
two-square support theorem. Northwest marker and top origin are distinct
points of the one merged top34816; they need no distinct foreign owners. -/
theorem outward_mixed_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missingG6 : ¬(owner p 512).Inside (113/50) 2)
    (f5 : (owner p 1024).Inside 2 (113/50)) : False := by
  obtain ⟨r,cp,sn,order,shape,same,faces⟩ := southeast_outward_frame p hf missingG6
  let A := (pullY r).translated 2 2
  let N := (owner p 1024).translated 2 2
  have aInside (x y : ℝ) : A.Inside x y↔(owner p 512).Inside (2+x) (2+y) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY,same,inside_pullY,
      show (4:ℝ)-(4-(2+y))=2+y by ring]
  have nInside (x y : ℝ) : N.Inside x y↔(owner p 1024).Inside (2+x) (2+y) :=
    inside_translated_iff (owner p 1024) 2 2 x y
  have side' : 1<r.side := by simpa only [shape] using side p 512
  have actualSame : A.side=N.side := by
    change r.side=(owner p 1024).side
    exact shape.trans ((p.congruent _).trans (p.congruent _).symm)
  have upperU : A.loU+A.side≤A.c+r.s := by
    have bound := faces.upperU
    dsimp only [A,pullY,OpenSquare.translated] at bound ⊢
    linarith only [bound]
  have lowerV : -A.c+(4/5)*r.s≤A.loV := by
    have bound := faces.upperV
    dsimp only [A,pullY,OpenSquare.translated] at bound ⊢
    linarith only [bound]
  have halfHigh : half A.c r.s<143/500 :=
    SharpPointScalars.half_upper r.c r.s (143/500) cp faces.sinePositive
      r.unit_normal faces.upperSpan
  have halfLow : 13/87<half A.c r.s := by
    have lower := SharpPointScalars.half_lower r.c r.s (37/50)
      cp sn order r.unit_normal faces.lowerSpan
    change 13/87<half r.c r.s
    linarith only [lower]
  have southMarker : A.Inside (7/20) (-7/20) := by
    apply (aInside _ _).mpr
    norm_num
    exact (fixed p hf).southeastMarker
  have southSharp : A.Inside (21/40) (1/8) := by
    apply (aInside _ _).mpr
    norm_num
    exact southeast_outward_sharp p hf missingG6
  apply OutwardPair.impossible A N r.s side' actualSame rfl cp sn order
    halfLow halfHigh upperU lowerV southMarker southSharp
  · apply (nInside _ _).mpr; norm_num; exact (fixed p hf).northeastMarker
  · apply (nInside _ _).mpr; norm_num; exact f5
  · apply (nInside _ _).mpr; norm_num; exact (northeast_selection p hf).1
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    exact foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (fixed p hf).northwestMarker actual
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    exact foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (top_origin p hf) actual
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    have corner : (owner p 48).Inside 3 3 := by
      convert seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
        using 1 <;> norm_num
    exact foreign p hf 1024 48 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ corner actual
  · intro x y both
    exact apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨(aInside _ _).mp both.1,(nInside _ _).mp both.2⟩

/-- Both genuine NE alternatives now rule out an outward S. -/
theorem southeast_g6_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 512).Inside (113/50) 2 := by
  by_contra missingG6
  by_cases f5 : (owner p 1024).Inside 2 (113/50)
  · exact outward_mixed_impossible p hf missingG6 f5
  · exact apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _
        ⟨southeast_outward_sharp p hf missingG6,northeast_upper_sharp p hf f5⟩

theorem southeast_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    16∈auxiliaries p 512 := by
  apply (auxiliary_exact p 512 16 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using southeast_g6_point p hf

theorem not_northeast_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    16∉auxiliaries p 1024 := by
  intro own
  exact foreign p hf 1024 512 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ (southeast_g6_point p hf)
    (by simpa [auxPoints,fPoints,gPoints] using aux_point p 1024 16 (by norm_num) own)

/-- S's optional F5 gives the same strict sharp point as top-only NE.
Its crosspoint omission is the genuine strict SW256 halfpoint. -/
theorem not_southeast_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    5∉auxiliaries p 512 := by
  intro own
  have f5 : (owner p 512).Inside 2 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 512 5 (by norm_num) own
  have missing := foreign p hf 1024 512 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ f5
  have south := CrossedElbow.point_original (owner p 512) (side p 512)
    (fixed p hf).southeastMarker (southeast_g6_point p hf) (fixed p hf).southeastF8 f5
    (foreign p hf 512 256 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (southwest_south p hf))
  exact apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨south,northeast_upper_sharp p hf missing⟩

#print axioms southeast_g6
#print axioms not_northeast_g6
#print axioms not_southeast_f5
end
end N12Compact.FiniteCases.C975Selection
