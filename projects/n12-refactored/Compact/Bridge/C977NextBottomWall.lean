import Compact.Bridge.C977PositiveWallOwnedWest
import Compact.Geometry.NegativeBottomNextWall
import Compact.Geometry.NegativeBottomInnerWall

/-! The actual bottom-wall and southeast-pair chain excludes a shallow
negative bottom singleton in C977. The negative next-wall sign receives
its inner point from the positive-wall theorem applied to the entire
transposed packing. Its corner reach therefore uses the genuine global
right wing, never an independently assigned local corner. Source only,
uncompiled. -/
namespace N12Compact.C977NextBottomWall

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private noncomputable def swapFrame (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

private theorem inside_swapFrame (q : OpenSquare) (x y : ℝ) :
    (swapFrame q).Inside x y↔q.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

/-- The owner identity is proved from actual transformed marker codes.
No permutation of square poses is assumed independently of the packing. -/
theorem transposed_wall_owner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) :
    orderedOwner (transposePacking p) 8=orderedOwner p 9 := by
  apply markerCode_injective (transposePacking p)
  rw [ordered_owner_code _ (transpose_family p hf) 8,transpose_code p hf,
    ordered_owner_code p hf 9]
  decide

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∀ x y, ¬((p.square (orderedOwner p 0)).Inside x y ∧
      (p.square (orderedOwner p 9)).Inside x y) := by
  apply p.disjoint
  exact fun h => (by decide : (0 : Fin 12)≠9) (ordered_owner_injective p hf h)

/-- Every nonpositive canonical frame of the actual bottom wall owns
its inward row point. This uses the full original transposed packing and
its genuine paired-corner reach, with no central or singleton premise. -/
theorem negative_frame_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (D : OpenSquare) (r : ℝ)
    (signed : D.s=-r) (normal : Normal D.c r)
    (shape : D.side=(p.square (orderedOwner p 9)).side)
    (equivalent : ∀ x y, D.Inside x y↔(p.square (orderedOwner p 9)).Inside x y) :
    D.Inside 2 1 := by
  have swappedNormal : Normal (swapFrame D).c (swapFrame D).s := by
    simpa only [swapFrame,signed,neg_neg] using normal
  have swappedShape : (swapFrame D).side=
      ((transposePacking p).square (orderedOwner (transposePacking p) 8)).side := by
    rw [transposed_wall_owner p hf,transpose_square]
    exact shape
  have swappedEquivalent : ∀ x y, (swapFrame D).Inside x y↔
      ((transposePacking p).square (orderedOwner (transposePacking p) 8)).Inside x y := by
    intro x y
    rw [transposed_wall_owner p hf,transpose_inside,inside_swapFrame]
    exact equivalent y x
  have point := C977PositiveWallOwnedWest.frame_point
    (transposePacking p) (transpose_family p hf) (swapFrame D)
    swappedNormal swappedShape swappedEquivalent
  exact (inside_swapFrame D 1 2).mp point

/-- Both signs of the actual next bottom wall are exhausted. The
quantitative singleton premise is supplied separately by original central
geometry; this theorem does not infer it from marker data alone. -/
theorem excludes_of_small_bottom (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (O : OpenSquare) (t : ℝ)
    (os : O.s=-t) (on : Normal O.c t) (small : t≤1/5)
    (shape : O.side=(p.square (orderedOwner p 0)).side)
    (equivalent : ∀ x y, O.Inside x y↔(p.square (orderedOwner p 0)).Inside x y)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1) : False := by
  obtain ⟨D,_,canonical,dShape,dEquivalent,_⟩ :=
    ClosedFrames.canonical_frame (p.square (orderedOwner p 9))
  have same : O.side=D.side := by rw [shape,dShape,p.congruent,p.congruent]
  have side : 1<O.side := by rw [shape,p.congruent]; exact p.side_gt_one
  have box : InsideContainer O := fun x y h => p.contained _ x y ((equivalent x y).mp h)
  have dBox : InsideContainer D := fun x y h => p.contained _ x y ((dEquivalent x y).mp h)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have anchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have oMarker : O.Inside 1 (457/500) := (equivalent _ _).mpr (by
    have h := (om 0).mpr (by decide)
    simpa [Owns,marker] using h)
  have oNear := (equivalent _ _).mpr anchors.near_point
  have oMiddle := (equivalent _ _).mpr anchors.horizontal_point
  have oFar := (equivalent _ _).mpr anchors.lower_point
  have oMissing : ¬O.Inside 1 1 := fun h => missingCorner ((equivalent _ _).mp h)
  have dMarker : D.Inside 2 (457/500) := (dEquivalent _ _).mpr (by
    have h := (dm 13).mpr (by decide)
    simpa [Owns,marker] using h)
  have dMissing : ¬D.Inside 3 (457/500) := by
    intro h
    have absent : (2 : Marker)∉maskSupport (auxiliaryCode 9) := by decide
    exact absent ((dm 2).mp (by simpa [Owns,marker] using (dEquivalent _ _).mp h))
  have od : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y) := fun x y h =>
    apart p hf x y ⟨(equivalent _ _).mp h.1,(dEquivalent _ _).mp h.2⟩
  by_cases nonnegative : 0≤D.s
  · have dn : Normal D.c D.s :=
      ⟨nonnegative,(le_abs_self D.s).trans canonical,D.unit_normal⟩
    exact NegativeBottomNextWall.impossible O D t os on dn small same side
      box dBox oMarker oNear oMiddle oFar oMissing dMarker dMissing od
  · have negative : D.s<0 := lt_of_not_ge nonnegative
    let r : ℝ := -D.s
    have ds : D.s=-r := by dsimp [r]; ring
    have dn : Normal D.c r := ⟨by dsimp [r]; linarith only [negative],
      by simpa only [r,abs_of_neg negative] using canonical,
      by dsimp [r]; nlinarith only [D.unit_normal]⟩
    have swappedNormal : Normal (swapFrame D).c (swapFrame D).s := by
      simpa only [swapFrame,r] using dn
    have swappedShape : (swapFrame D).side=
        ((transposePacking p).square (orderedOwner (transposePacking p) 8)).side := by
      rw [transposed_wall_owner p hf,transpose_square]
      change D.side=(p.square (orderedOwner p 9)).side
      exact dShape
    have swappedEquivalent : ∀ x y, (swapFrame D).Inside x y↔
        ((transposePacking p).square (orderedOwner (transposePacking p) 8)).Inside x y := by
      intro x y
      rw [transposed_wall_owner p hf,transpose_inside,inside_swapFrame]
      exact dEquivalent y x
    have swappedPoint := C977PositiveWallOwnedWest.frame_point
      (transposePacking p) (transpose_family p hf) (swapFrame D)
      swappedNormal swappedShape swappedEquivalent
    have inner : D.Inside 2 1 := (inside_swapFrame D 1 2).mp swappedPoint
    exact NegativeBottomInnerWall.impossible O D t r os ds on dn small same side
      box oMarker oNear oMiddle oFar oMissing dMarker inner od

#print axioms transposed_wall_owner
#print axioms negative_frame_point
#print axioms excludes_of_small_bottom
end N12Compact.C977NextBottomWall
