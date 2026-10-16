import Compact.Cases.C868.UpperCenter
import Compact.Cases.C868.UpperNonnegative

/-! The full nonnegative merged-upper sector of the original C868 family.
The three scalar modes and both top-point faces are exhaustive.  This is
still a sector theorem: the strictly negative upper frame is retained. -/
namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem nonnegative_upper_frames_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A H : OpenSquare)
    (ac : 0<A.c) (aCanonical : |A.s|≤A.c) (hH : Normal H.c H.s)
    (sideA : A.side=(owner p 256).side) (sideH : H.side=(owner p 3072).side)
    (insideA : ∀ x y,A.Inside x y↔(owner p 256).Inside x y)
    (insideH : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) : False := by
  by_cases nonnegative : 0≤A.s
  · exact positive_frames_impossible p hf A H
      ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using aCanonical,A.unit_normal⟩
      hH sideA sideH insideA insideH
  have negative : A.s<0 := lt_of_not_ge nonnegative
  have hA : Normal A.c (-A.s) :=
    ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using aCanonical,
      by nlinarith only [A.unit_normal]⟩
  have bounds := normal_bounds hH
  have center := upper_nonnegative_center p hf H (by linarith only [bounds.1])
    hH.1 hH.2.1 sideH insideH
  have same : A.side=H.side := by
    rw [sideA,sideH,show (owner p 256).side=p.commonSide from p.congruent _,
      show (owner p 3072).side=p.commonSide from p.congruent _]
  have crosspoints := southwest_crosspoints p hf
  have actualApart (x y : ℝ) : ¬(A.Inside x y ∧ H.Inside x y) := fun own =>
    apart p hf 256 3072 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      x y ⟨(insideA _ _).mp own.1,(insideH _ _).mp own.2⟩
  apply UpperNonnegative.impossible A H
  refine {
    lowerNormal := hA
    upperNormal := hH
    side := ?_
    same := same
    marker := ?_
    nearBottom := ?_
    nearLeft := ?_
    left := (insideA _ _).mpr crosspoints.1
    below := (insideA _ _).mpr crosspoints.2
    northwest := ?_
    northeast := ?_
    center := center
    missingBottom := ?_
    missingLeft := ?_
    missingTopLeft := ?_
    missingTopRight := ?_
    apart := actualApart }
  · rw [sideA,show (owner p 256).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  · apply (insideA _ _).mpr
    simpa using seed_inside p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
  · apply (insideA _ _).mpr
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 0
  · apply (insideA _ _).mpr
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1
  · apply (insideH _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (33/20,47/20) (by decide +kernel)
  · apply (insideH _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (47/20,47/20) (by decide +kernel)
  · intro own
    exact apart p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(insideA _ _).mp own,by
        simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 3⟩
  · intro own
    exact apart p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(insideA _ _).mp own,by
        simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 4⟩
  · intro own
    exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(insideH _ _).mp own,by
        simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2⟩
  · intro own
    exact apart p hf 3072 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(insideH _ _).mp own,by
        simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 1⟩

/-- Every signed canonical frame of the actual merged square has strictly
negative sine.  Neither the negative sector nor the whole case is excluded
by this theorem. -/
theorem upper_negative_required (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (hc : 0<H.c) (canonical : |H.s|≤H.c)
    (side : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) : H.s<0 := by
  apply lt_of_not_ge
  intro sign
  obtain ⟨A,ac,aCanonical,sideA,insideA,_⟩ := ClosedFrames.canonical_frame (owner p 256)
  exact nonnegative_upper_frames_impossible p hf A H ac aCanonical
    ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,H.unit_normal⟩
    sideA side insideA inside

#print axioms nonnegative_upper_frames_impossible
#print axioms upper_negative_required
end N12Compact.C868
