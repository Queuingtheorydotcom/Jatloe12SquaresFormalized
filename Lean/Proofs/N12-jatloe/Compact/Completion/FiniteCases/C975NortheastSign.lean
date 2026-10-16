import Compact.Completion.FiniteCases.C975CornerReduction
import Compact.Completion.OtherCases.C976MergedLeft.TopTransfers
import Compact.Completion.OtherCases.C976NegativeTop.Main
import Compact.Completion.C981.CornerAdvance

/-! The actual C975 northeast sign and consequent top angle. Both
actual northeast alternatives remain until their respective proofs.
The top's omitted left point is derived from its omitted halfpoint by
convexity in that same merged34816, not supplied by a fictitious NW owner.
Source only; no original-case exclusion is asserted in this module. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem nonnegative_northeast_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (N : OpenSquare)
    (shape : N.side=(owner p 1024).side)
    (inside : ∀ x y,N.Inside x y↔(owner p 1024).Inside x y)
    (cp : 0<N.c) (sn : 0≤N.s) (order : N.s≤N.c) : False := by
  have nSide : 1<N.side := by simpa only [shape] using side p 1024
  have wall : ∀ x y,(owner p 34816).Inside x y → y≤4 :=
    fun x y own => (box p 34816 x y own).2.2.2
  have disjoint : ∀ x y,¬(N.Inside x y ∧ (owner p 34816).Inside x y) :=
    fun x y both => apart _ p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x y ⟨(inside x y).mp both.1,both.2⟩
  have origin := top_origin p hf
  by_cases mixed : (owner p 1024).Inside 2 (113/50)
  · have topF : (owner p 34816).Inside (8/5) 3 := by
      simpa [auxPoints,fPoints,gPoints] using aux_point p 34816 3 (by norm_num)
        (C975IncomingCut.top_left p hf)
    have advance := C976MergedLeft.mixed_top_advance N (owner p 34816) nSide
      (side p 34816) cp sn order ((inside _ _).mpr (northeast_selection p hf).1)
      ((inside _ _).mpr mixed)
      (fun own => foreign p hf 1024 512 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (southeast_g6_point p hf) ((inside _ _).mp own))
      (fixed p hf).topMarker topF wall disjoint
    exact top_halfpoint_excluded p hf (horizontal_segment _ (127/100) 2 3 (3/2)
      advance origin (by norm_num) (by norm_num) (by norm_num))
  · have corner : (owner p 48).Inside 3 3 := by
      convert seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
        using 1 <;> norm_num
    have advance := C976MergedLeft.top_only_advance N (owner p 34816) nSide
      (side p 34816) cp sn order ((inside _ _).mpr (fixed p hf).northeastMarker)
      ((inside _ _).mpr (northeast_selection p hf).1)
      ((inside _ _).mpr (northeast_upper_sharp p hf mixed))
      (fun own => mixed ((inside _ _).mp own))
      (fun own => foreign p hf 1024 48 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ corner ((inside _ _).mp own))
      (fun y low high own => foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (right_bar p hf y low high) ((inside _ _).mp own))
      origin wall disjoint
    exact top_halfpoint_excluded p hf (horizontal_segment _ (6/5) 2 3 (3/2)
      advance origin (by norm_num) (by norm_num) (by norm_num))

theorem northeast_negative (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (N : OpenSquare) (shape : N.side=(owner p 1024).side)
    (inside : ∀ x y,N.Inside x y↔(owner p 1024).Inside x y)
    (cp : 0<N.c) (canonical : |N.s|≤N.c) : N.s<0 := by
  apply lt_of_not_ge
  intro sign
  exact nonnegative_northeast_impossible p hf N shape inside cp sign (abs_le.mp canonical).2

/-- The two actual alternatives in the common chart (x-2,y-3).
The mixed excluded interval belongs entirely to actual southeast512. -/
theorem negative_alternative (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (N : OpenSquare)
    (inside : ∀ x y,N.Inside x y↔(owner p 1024).Inside (2+x) (3+y)) :
    C976NegativeTop.Alternative N := by
  by_cases mixed : (owner p 1024).Inside 2 (113/50)
  · right
    refine ⟨(inside _ _).mpr (by convert mixed using 1 <;> norm_num),?_⟩
    intro x low high own
    have south := horizontal_segment (owner p 512) (113/50) (5/2) 2 (2+x)
      (southeast_g6_point p hf) (southeast_east p hf) (by norm_num)
      (by linarith only [low]) (by linarith only [high])
    apply apart _ p hf 1024 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (2+x) 2 ⟨?_,south⟩
    convert (inside _ _).mp own using 1 <;> norm_num
  · left
    have corner : (owner p 48).Inside 3 3 := by
      convert seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
        using 1 <;> norm_num
    have inward := TopOnlyLeftPoint.point_original (owner p 1024) (side p 1024)
      (fixed p hf).northeastMarker (northeast_selection p hf).1
      (northeast_upper_sharp p hf mixed) mixed
      (foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (top_origin p hf))
      (foreign p hf 1024 48 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ corner)
      (fun y low high => foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (right_bar p hf y low high))
    refine ⟨(inside _ _).mpr (by convert inward using 1 <;> norm_num),?_⟩
    intro own
    apply mixed
    convert (inside _ _).mp own using 1 <;> norm_num

/-- An omitted halfpoint implies omission of every farther point on
the same side of the strict origin, with no assertion of another owner. -/
theorem top_left_excluded (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owner p 34816).Inside (32/25) 3 := by
  intro left
  exact top_halfpoint_excluded p hf (horizontal_segment _ (32/25) 2 3 (3/2)
    left (top_origin p hf) (by norm_num) (by norm_num) (by norm_num))

/-- The full negative-NE/top theorem forces the actual top's negative
canonical sign. The top left exclusion stays in that same physical T. -/
theorem top_negative_shallow (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (R W : OpenSquare)
    (shapeR : R.side=(owner p 1024).side)
    (insideR : ∀ x y,R.Inside x y↔(owner p 1024).Inside x y)
    (cp : 0<R.c) (sn : R.s<0) (order : -R.s≤R.c)
    (shapeW : W.side=(owner p 34816).side)
    (insideW : ∀ x y,W.Inside x y↔(owner p 34816).Inside x y)
    (wp : 0<W.c) (canonical : |W.s|≤W.c) :
    W.s<0 ∧ -W.s<(2/3)*W.c := by
  let N := R.translated 2 3
  let T := W.translated 2 3
  have nInside (x y : ℝ) : N.Inside x y↔(owner p 1024).Inside (2+x) (3+y) :=
    (inside_translated_iff R 2 3 x y).trans (insideR (2+x) (3+y))
  have tInside (x y : ℝ) : T.Inside x y↔(owner p 34816).Inside (2+x) (3+y) :=
    (inside_translated_iff W 2 3 x y).trans (insideW (2+x) (3+y))
  have nSide : 1<N.side := by simpa only [N,OpenSquare.translated,shapeR] using side p 1024
  have same : N.side=T.side := by
    change R.side=W.side
    exact (shapeR.trans (p.congruent _)).trans (shapeW.trans (p.congruent _)).symm
  have marker : N.Inside (7/20) (-13/20) :=
    (nInside _ _).mpr (by convert (fixed p hf).northeastMarker using 1 <;> norm_num)
  have elbow : N.Inside (13/50) 0 :=
    (nInside _ _).mpr (by convert (northeast_selection p hf).1 using 1 <;> norm_num)
  have right : ¬N.Inside 1 (-11/25) := by
    intro own
    apply foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (C975IncomingCut.right_high p hf)
    convert (nInside _ _).mp own using 1 <;> norm_num
  have alternative := negative_alternative p hf N nInside
  have origin : T.Inside 0 0 :=
    (tInside _ _).mpr (by convert top_origin p hf using 1 <;> norm_num)
  have left : ¬T.Inside (-18/25) 0 := by
    intro own
    apply top_left_excluded p hf
    convert (tInside _ _).mp own using 1 <;> norm_num
  have wall : ∀ x y,T.Inside x y → y≤1 := by
    intro x y own
    have bound := (box p 34816 (2+x) (3+y) ((tInside _ _).mp own)).2.2.2
    linarith only [bound]
  have disjoint : ∀ x y,¬(N.Inside x y ∧ T.Inside x y) :=
    fun x y both => apart _ p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (2+x) (3+y) ⟨(nInside _ _).mp both.1,(tInside _ _).mp both.2⟩
  by_cases sign : 0≤W.s
  · have result := C976NegativeTop.angle N T (-R.s)
      (by dsimp only [N,OpenSquare.translated]; ring) nSide same cp
      (by linarith only [sn]) order wp.le sign marker elbow right alternative origin left
      (C981CompletionCornerAdvance.upper_wall T wall) disjoint
    have topOrder := (abs_le.mp canonical).2
    change 0<W.s ∧ W.c<(2/3)*W.s at result
    exact False.elim (by linarith only [result.1,result.2,topOrder])
  · have negative : W.s<0 := lt_of_not_ge sign
    have turnedWall : ∀ x y,(turnFrame T).Inside x y → y≤1 :=
      fun x y own => wall x y ((turnFrame_inside T x y).mp own)
    have result := C976NegativeTop.angle N (turnFrame T) (-R.s)
      (by dsimp only [N,OpenSquare.translated]; ring) nSide
      (by simpa only [turnFrame_side] using same) cp (by linarith only [sn]) order
      (by dsimp only [turnFrame,T,OpenSquare.translated]; linarith only [negative])
      wp.le marker elbow right alternative ((turnFrame_inside T _ _).mpr origin)
      (fun own => left ((turnFrame_inside T _ _).mp own))
      (C981CompletionCornerAdvance.upper_wall (turnFrame T) turnedWall)
      (fun x y both => disjoint x y ⟨both.1,(turnFrame_inside T x y).mp both.2⟩)
    change 0<W.c ∧ -W.s<(2/3)*W.c at result
    exact ⟨negative,result.2⟩

#print axioms northeast_negative
#print axioms top_negative_shallow
end
end N12Compact.FiniteCases.C975Selection
