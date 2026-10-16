import Compact.Completion.FiniteCases.C975IncomingCut
import Compact.Geometry.C849Negative
import Compact.Geometry.C849Positive
import Compact.Completion.C1092.MixedSpan

/-! The original C975 incoming branch reuses the complete continuous
merged-top argument. Its missing top endpoint is an explicit branch
hypothesis; the complementary ownership alternative remains live. -/
namespace N12Compact.FiniteCases.C975IncomingPair
open S12 S12Pilot FourSquareAnchors C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

private theorem positive (A B : OpenSquare)
    (bc : 0<B.c) (bs : 0≤B.s) (bsc : B.s≤B.c)
    (same : A.side=B.side) (side : 1<B.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20)) (aHigh : A.Inside 2 (5/2))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (missingR : ¬A.Inside 3 (12/5))
    (bT : ClosedInside B (33/20) (47/20)) (bP : ClosedInside B (8/5) 3)
    (bH : B.Inside 2 (1543/500))
    (missingC : ¬B.Inside (113/50) 3) (missingE : ¬B.Inside 1 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ B.Inside x y)) : False := by
  have lower := C849PositiveAbove.b_lower_face B bc bs bT bH
    (fun h => apart _ _ ⟨aHigh,h⟩)
  have lowSlope : 3*B.c≤7*B.s := by linarith only [lower,bT.2.2.1]
  obtain ⟨A',ac,aNonneg,shape,inside,closed⟩ := ClosedFrames.positive_frame A
  rcases PositiveBLeftReduction.upper_left_marker_modes B bc bs side bT bP lower missingE with
    lowerU | ⟨upperV,height,_⟩
  · have cUlo : B.loU<(113/50)*B.c+3*B.s := by
      linarith only [bP.1,bc]
    have cVlo : B.loV< -(113/50)*B.s+3*B.c := by
      linarith only [bT.2.2.1,bsc,bc]
    have cVhi : -(113/50)*B.s+3*B.c<B.loV+B.side := by
      linarith only [bH.2.2.2,bc,bs]
    have cap : B.loU+B.side≤(113/50)*B.c+3*B.s :=
      le_of_not_gt (fun upper => missingC ⟨by linarith only [cUlo],
        by linarith only [upper],by linarith only [cVlo],by linarith only [cVhi]⟩)
    have cLow : 50/63<B.c := by linarith only [lowerU,cap,side]
    have highSlope : B.s≤(4/5)*B.c := by
      apply le_of_not_gt
      intro failure
      have first := mul_pos (sub_pos.mpr failure)
        (show 0<B.s+(4/5)*B.c by linarith only [bs,bc])
      have second := mul_pos (sub_pos.mpr cLow)
        (show 0<B.c+50/63 by linarith only [bc])
      nlinarith only [first,second,B.unit_normal]
    exact C849ShallowAB.in_frame A' B ac aNonneg bc bs lowSlope highSlope
      (shape.trans same) side ((closed _ _).mpr aP) ((closed _ _).mpr aQ)
      ((inside _ _).mpr aT) (fun h => missingG ((inside _ _).mp h))
      (fun h => missingB ((inside _ _).mp h)) (fun h => missingR ((inside _ _).mp h))
      bT bH (fun x y h => apart x y ⟨(inside _ _).mp h.1,h.2⟩)
  · exact C849SteepAB.in_frame A' B ac aNonneg bc bs bsc (shape.trans same) side height upperV
      ((closed _ _).mpr aP) ((closed _ _).mpr aQ) ((inside _ _).mpr aT)
      (fun h => missingG ((inside _ _).mp h)) (fun h => missingB ((inside _ _).mp h))
      (fun h => missingR ((inside _ _).mp h)) bT bH
      (fun x y h => apart x y ⟨(inside _ _).mp h.1,h.2⟩)

private theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed _ p hf mask member P checked

private theorem aux_inside (p : NormalizedPacking) (mask index : Nat)
    (bound : index<20) (own : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr own

private theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun h => apart _ p hf m n hm hn different x y ⟨h,point⟩

/-- The entire incoming NE branch, in every orientation, forces the live
extra G7 endpoint of the actual merged top. It does not exclude that
remaining endpoint alternative or assert a whole original-case theorem. -/
theorem incoming_forces_top_seven (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (incoming : 5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024) :
    17∈auxiliaries p 34816 := by
  classical
  by_contra missing
  have points := compulsory p hf
  have aP : (owner p 1024).Inside 2 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 5 (by norm_num) incoming.1
  have aQ : (owner p 1024).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 16 (by norm_num) incoming.2
  have aT : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have aHigh := C975IncomingCut.incoming_high p hf incoming
  have bT : (owner p 34816).Inside (33/20) (47/20) := by
    have h := seed_point p hf 34816 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have bP : (owner p 34816).Inside (8/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p 34816 3 (by norm_num) (C975IncomingCut.top_left p hf)
  have bH : (owner p 34816).Inside 2 (1543/500) := by
    have h := seed_point p hf 34816 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have noC : ¬(owner p 34816).Inside (113/50) 3 := by
    intro h
    apply missing
    apply (auxiliary_exact p 34816 17 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using h
  have sw : (owner p 256).Inside (33/20) (33/20) := by
    have h := seed_point p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have se : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have rHigh : (owner p 16384).Inside 3 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 16384 19 (by norm_num) points.rightWall.2
  have lMarker : (owner p 4096).Inside (457/500) 2 := by
    have h := seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have lHigh : (owner p 4096).Inside 1 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 4096 11 (by norm_num) points.leftWall.2
  have lSeed : (owner p 2).Inside (19/25) (187/100) := by
    have h := seed_point p hf 2 (by decide +kernel) (19/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have eP : (owner p 192).Inside 1 (1543/500) := by
    have h := seed_point p hf 192 (by decide +kernel) (1,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have eQ : (owner p 192).Inside (457/500) 3 := by
    have h := seed_point p hf 192 (by decide +kernel) (457/500,3) (by decide +kernel)
    norm_num at h; exact h
  have eCorner : (owner p 192).Inside 1 3 := by
    have h := seed_point p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
    norm_num at h; exact h
  obtain ⟨B,bc,range,shape,inside,closed⟩ := ClosedFrames.canonical_frame (owner p 34816)
  have bSide : 1<B.side := by simpa only [shape] using side p 34816
  have bMarker := (inside _ _).mpr bT
  have bTop := (inside _ _).mpr bH
  have bPoint := (closed _ _).mpr (close bP)
  have bMissingC : ¬B.Inside (113/50) 3 := fun h => noC ((inside _ _).mp h)
  have ab : ∀ x y, ¬((owner p 1024).Inside x y ∧ B.Inside x y) :=
    fun x y h => apart _ p hf 1024 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x y ⟨h.1,(inside x y).mp h.2⟩
  by_cases sign : 0≤B.s
  · apply positive (owner p 1024) B bc sign (abs_le.mp range).2
      ((p.congruent _).trans ((shape.trans (p.congruent _)).symm)) bSide
      (close aP) (close aQ) aT aHigh
      (foreign p hf 1024 512 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ se)
      (foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ bT)
      (foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ rHigh)
      (close bMarker) bPoint bTop bMissingC
      (fun h => foreign p hf 34816 192 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ eCorner ((inside _ _).mp h)) ab
  · obtain ⟨L,lc,lRange,lShape,lInside,lClosed⟩ := ClosedFrames.canonical_frame (owner p 4096)
    apply C849Negative.impossible B L (owner p 192) bc (lt_of_not_ge sign).le
      (by linarith only [(abs_le.mp range).1]) lc lRange bSide
    · rw [shape]; change (p.square _).side≤1001/1000
      rw [p.congruent]; exact p.side_le
    · exact (shape.trans (p.congruent _)).trans ((lShape.trans (p.congruent _)).symm)
    · exact (p.congruent _).trans ((shape.trans (p.congruent _)).symm)
    · intro x y h
      exact box p 4096 x y ((lInside x y).mp h)
    · exact box p 192
    · exact bMarker
    · exact bPoint
    · exact bTop
    · exact fun h => ab _ _ ⟨aHigh,h⟩
    · exact bMissingC
    · exact (lClosed _ _).mpr (close lMarker)
    · exact (lClosed _ _).mpr (close lHigh)
    · exact fun h => foreign p hf 4096 2 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ lSeed ((lInside _ _).mp h)
    · exact fun h => foreign p hf 4096 256 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ sw ((lInside _ _).mp h)
    · exact eP
    · exact eQ
    · exact fun x y h => apart _ p hf 34816 4096 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) x y ⟨(inside x y).mp h.1,(lInside x y).mp h.2⟩
    · exact fun x y h => apart _ p hf 34816 192 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) x y ⟨(inside x y).mp h.1,h.2⟩

/-- The long mixed elbow cannot omit both incoming and top endpoints.
The actual right wall supplies both required foreign points; no long
wall bar or singleton lower-corner seed is attributed to this family. -/
theorem missing_ne_seven_forces_incoming (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noSeven : 17∉auxiliaries p 1024) :
    5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024 := by
  classical
  have points := compulsory p hf
  have elbow := points.northeast.2.resolve_right noSeven
  refine ⟨?_,elbow⟩
  by_contra missing
  have upper := points.northeast.1.resolve_left missing
  have a : (owner p 1024).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 16 (by norm_num) elbow
  have b : (owner p 1024).Inside (12/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 7 (by norm_num) upper
  have noF : ¬(owner p 1024).Inside 2 (113/50) := by
    intro h
    apply missing
    apply (auxiliary_exact p 1024 5 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using h
  have noG : ¬(owner p 1024).Inside (113/50) 3 := by
    intro h
    apply noSeven
    apply (auxiliary_exact p 1024 17 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using h
  have rF : (owner p 16384).Inside 3 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 16384 9 (by norm_num) points.rightWall.1
  have rG : (owner p 16384).Inside 3 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 16384 19 (by norm_num) points.rightWall.2
  let turn : Transform := ⟨true,true,false⟩
  apply C1092MixedSpan.impossible (turn.pull (owner p 1024))
    (by simpa only [pull_same_side] using side p 1024)
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]; exact a
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]; exact b
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]; exact noF
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]; exact noG
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
    exact foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ rF
  · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
    exact foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ rG

theorem top_seven_forces_incoming (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (seven : 17∈auxiliaries p 34816) :
    5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024 := by
  apply missing_ne_seven_forces_incoming p hf
  exact fun own => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 1024 34816
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) own seven

/-- A complete original-family dichotomy, retaining every extra allowed
label: either the NE owner is incoming and the merged owner takes G7,
or NE takes G7 while the merged owner has exactly G4 and omits F7. This
records the two unfinished endgames without asserting either impossible. -/
theorem dichotomy (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ((5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024) ∧ 17∈auxiliaries p 34816) ∨
      (17∈auxiliaries p 1024 ∧ natAuxOwners p 1 (ownerIndex p 34816)={4} ∧
        7∉auxiliaries p 34816) := by
  classical
  by_cases seven : 17∈auxiliaries p 1024
  · right
    have noTop : 17∉auxiliaries p 34816 := fun own =>
      Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 34816 1024
        (by decide +kernel) (by decide +kernel) (by decide +kernel)) own seven
    have topG : natAuxOwners p 1 (ownerIndex p 34816)={4} := by
      rcases C975IncomingCut.top_g_options p hf with single | double
      · exact single
      · exfalso
        apply noTop
        apply (auxiliary_exact p 34816 17 (by norm_num)).mp
        have h := (nat_aux_exact p 1 (ownerIndex p 34816) 7 (by decide +kernel)).mpr
          (show 7∈natAuxOwners p 1 (ownerIndex p 34816) by rw [double]; decide +kernel)
        simpa [auxKind,auxPoints,fPoints,gPoints,CommonCases.OriginalOwners.owner] using h
    refine ⟨seven,topG,?_⟩
    intro ownF
    exact noTop (incoming_forces_top_seven p hf (C975IncomingCut.top_seven_incoming p hf ownF))
  · have incoming := missing_ne_seven_forces_incoming p hf seven
    exact Or.inl ⟨incoming,incoming_forces_top_seven p hf incoming⟩

#print axioms incoming_forces_top_seven
#print axioms missing_ne_seven_forces_incoming
#print axioms dichotomy
end
end N12Compact.FiniteCases.C975IncomingPair
