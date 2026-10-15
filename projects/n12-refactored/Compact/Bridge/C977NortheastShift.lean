import Compact.Bridge.C977NortheastFarther
import Compact.Geometry.UpperRightNegativeCornerPositiveTop
import Completion.Cases.C977.SwapReduction

/-! All-angle original northeast-corner ending. Exact diagonal transport
first supplies the negative corner's vertical endpoint. The complete
corner/top separation then supplies the horizontal endpoint for every
sign, excluding either wall displacement separately. Source-only. -/
namespace N12Compact.C977NortheastShift

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

private def ownerSwap : Fin 12→Fin 12 := ![1,0,4,3,2,5,7,6,9,8,11,10]

private theorem transpose_owner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) : orderedOwner (transposePacking p) i=orderedOwner p (ownerSwap i) := by
  apply markerCode_injective (transposePacking p)
  rw [ordered_owner_code _ (transpose_family p hf) i,transpose_code p hf,
    ordered_owner_code p hf (ownerSwap i)]
  fin_cases i <;> decide

private noncomputable def swapFrame (A : OpenSquare) : OpenSquare where
  c := A.c
  s := -A.s
  loU := A.loV
  loV := A.loU
  side := A.side
  unit_normal := by nlinarith only [A.unit_normal]
  side_pos := A.side_pos

private theorem inside_swapFrame (A : OpenSquare) (x y : ℝ) :
    (swapFrame A).Inside x y↔A.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

/-- A negative canonical northeast corner reaches vertically outward.
The proof uses the actual right wall as the top neighbor after the
diagonal transport of the complete packing. -/
theorem frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (en : Normal (q 3).c (-(q 3).s)) (rn : |(q 10).s|≤(q 10).c) :
    (q 3).Inside 3 (7/2) := by
  have eShape : (swapFrame (q 3)).side=
      ((transposePacking p).square (orderedOwner (transposePacking p) 3)).side := by
    rw [transpose_owner p hf,transpose_square]
    exact shape 3
  have tShape : (swapFrame (q 10)).side=
      ((transposePacking p).square (orderedOwner (transposePacking p) 11)).side := by
    rw [transpose_owner p hf,transpose_square]
    exact shape 10
  have eEquivalent : ∀ x y, (swapFrame (q 3)).Inside x y↔
      ((transposePacking p).square (orderedOwner (transposePacking p) 3)).Inside x y := by
    intro x y
    rw [transpose_owner p hf,transpose_inside]
    exact (inside_swapFrame _ x y).trans (equivalent 3 y x)
  have tEquivalent : ∀ x y, (swapFrame (q 10)).Inside x y↔
      ((transposePacking p).square (orderedOwner (transposePacking p) 11)).Inside x y := by
    intro x y
    rw [transpose_owner p hf,transpose_inside]
    exact (inside_swapFrame _ x y).trans (equivalent 10 y x)
  have topCanonical : |(swapFrame (q 10)).s|≤(swapFrame (q 10)).c := by
    simpa only [swapFrame,abs_neg] using rn
  have point := C977NortheastFarther.frame_point (transposePacking p)
    (transpose_family p hf) (swapFrame (q 3)) (swapFrame (q 10)) en topCanonical
    eShape tShape eEquivalent tEquivalent
  exact (inside_swapFrame (q 3) (7/2) 3).mp point

/-- A positive top wall forces the horizontal farther point for either
canonical sign of the actual corner. In the negative corner sign its
vertical farther point is supplied by the full original right neighbor. -/
theorem positive_top_frame_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (rc : |(q 10).s|≤(q 10).c)
    (tn : Normal (q 11).c (q 11).s) : (q 3).Inside (7/2) 3 := by
  by_cases sign : 0≤(q 3).s
  · have en : Normal (q 3).c (q 3).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using ec,(q 3).unit_normal⟩
    exact C977NortheastFarther.frame_point p hf (q 3) (q 11) en
      (by simpa only [abs_of_nonneg tn.1] using tn.2.1)
      (shape 3) (shape 11) (equivalent 3) (equivalent 11)
  · have negative : (q 3).s≤0 := (lt_of_not_ge sign).le
    have en : Normal (q 3).c (-(q 3).s) :=
      ⟨neg_nonneg.mpr negative,by simpa only [abs_of_nonpos negative] using ec,
        by nlinarith only [(q 3).unit_normal]⟩
    have vertical := frame_point p hf q shape equivalent en rc
    exact C977NortheastFarther.negative_frame_point p hf (q 3) (q 11) en tn
      (shape 3) (shape 11) (equivalent 3) (equivalent 11) vertical

/-- Both positive wall signs exclude the right displacement regardless
of the paired corner orientation. The remaining opposite wall-sign cell
is not discarded by this conclusion. -/
theorem positive_top_right_shift_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c)
    (rn : Normal (q 10).c (q 10).s) (tn : Normal (q 11).c (q 11).s)
    (shift : 3*(q 10).c+2*(q 10).s≤(q 10).loU) : False := by
  have farther := positive_top_frame_point p hf q shape equivalent ec
    (by simpa only [abs_of_nonneg rn.1] using rn.2.1) tn
  exact C977NortheastFarther.right_shift_of_farther p hf q shape equivalent rn shift farther

/-- The actual diagonal endpoint supplies the last premise of the
negative-corner/positive-top argument; no farther point is assumed. -/
theorem negative_positive_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (en : Normal (q 3).c (-(q 3).s)) (rn : |(q 10).s|≤(q 10).c)
    (tn : Normal (q 11).c (q 11).s) : (q 3).Inside (7/2) 3 := by
  exact C977NortheastFarther.negative_frame_point p hf (q 3) (q 11) en tn
    (shape 3) (shape 11) (equivalent 3) (equivalent 11)
    (frame_point p hf q shape equivalent en rn)

/-- Every canonical orientation of the actual northeast pair reaches
the same farther point. The sign split is exhaustive and has no angle grid. -/
theorem all_frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (rc : |(q 10).s|≤(q 10).c)
    (tc : |(q 11).s|≤(q 11).c) : (q 3).Inside (7/2) 3 := by
  by_cases positive : 0≤(q 3).s
  · have en : Normal (q 3).c (q 3).s :=
      ⟨positive,by simpa only [abs_of_nonneg positive] using ec,(q 3).unit_normal⟩
    exact C977NortheastFarther.frame_point p hf (q 3) (q 11) en tc
      (shape 3) (shape 11) (equivalent 3) (equivalent 11)
  · have negative : (q 3).s≤0 := (lt_of_not_ge positive).le
    have en : Normal (q 3).c (-(q 3).s) :=
      ⟨neg_nonneg.mpr negative,by simpa only [abs_of_nonpos negative] using ec,
        by nlinarith only [(q 3).unit_normal]⟩
    have vertical := frame_point p hf q shape equivalent en rc
    by_cases top : 0≤(q 11).s
    · have tn : Normal (q 11).c (q 11).s :=
        ⟨top,by simpa only [abs_of_nonneg top] using tc,(q 11).unit_normal⟩
      exact C977NortheastFarther.negative_frame_point p hf (q 3) (q 11) en tn
        (shape 3) (shape 11) (equivalent 3) (equivalent 11) vertical
    · have tn : Normal (q 11).c (-(q 11).s) :=
        ⟨by linarith only [top],by simpa only [abs_of_neg (lt_of_not_ge top)] using tc,
          by nlinarith only [(q 11).unit_normal]⟩
      exact C977NortheastFarther.negative_pair_frame_point p hf (q 3) (q 11) en tn
        (shape 3) (shape 11) (equivalent 3) (equivalent 11) vertical

/-- One genuine right-wall displacement is already impossible. No
condition on the other wall's sign or displacement remains. -/
theorem right_shift_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (tc : |(q 11).s|≤(q 11).c)
    (rn : Normal (q 10).c (q 10).s)
    (shift : 3*(q 10).c+2*(q 10).s≤(q 10).loU) : False := by
  have rc : |(q 10).s|≤(q 10).c := by
    simpa only [abs_of_nonneg rn.1] using rn.2.1
  exact C977NortheastFarther.right_shift_of_farther p hf q shape equivalent rn shift
    (all_frame_point p hf q shape equivalent ec rc tc)

/-- Diagonal transport excludes the top-wall displacement for every
corner sign as well. The entire original packing is transported. -/
theorem all_top_shift_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (rc : |(q 10).s|≤(q 10).c)
    (tn : Normal (q 11).c (-(q 11).s))
    (shift : 3*(q 11).c-2*(q 11).s≤(q 11).loV) : False := by
  let Q : Fin 12→OpenSquare := fun i => swapFrame (q (ownerSwap i))
  have qShape (i : Fin 12) : (Q i).side=
      ((transposePacking p).square (orderedOwner (transposePacking p) i)).side := by
    rw [transpose_owner p hf,transpose_square]
    change (q (ownerSwap i)).side=(p.square (orderedOwner p (ownerSwap i))).side
    exact shape (ownerSwap i)
  have qEquivalent (i : Fin 12) (x y : ℝ) : (Q i).Inside x y↔
      ((transposePacking p).square (orderedOwner (transposePacking p) i)).Inside x y := by
    rw [transpose_owner p hf,transpose_inside]
    exact (inside_swapFrame _ x y).trans (equivalent (ownerSwap i) y x)
  have qE : |(Q 3).s|≤(Q 3).c := by
    change |-(q 3).s|≤(q 3).c
    simpa only [abs_neg] using ec
  have qT : |(Q 11).s|≤(Q 11).c := by
    change |-(q 10).s|≤(q 10).c
    simpa only [abs_neg] using rc
  have qR : Normal (Q 10).c (Q 10).s := tn
  have qShift : 3*(Q 10).c+2*(Q 10).s≤(Q 10).loU := by
    change 3*(q 11).c+2*(-(q 11).s)≤(q 11).loV
    linarith only [shift]
  exact right_shift_excludes (transposePacking p) (transpose_family p hf)
    Q qShape qEquivalent qE qT qR qShift

/-- Only the negative-corner/negative-top sign cell can survive a
positive right-wall displacement. The conclusion keeps the full packing. -/
theorem right_shift_negative_signs (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (tc : |(q 11).s|≤(q 11).c)
    (rn : Normal (q 10).c (q 10).s)
    (shift : 3*(q 10).c+2*(q 10).s≤(q 10).loU) :
    (q 3).s<0 ∧ (q 11).s<0 := by
  have eNegative : (q 3).s<0 := by
    apply lt_of_not_ge
    intro positive
    have en : Normal (q 3).c (q 3).s :=
      ⟨positive,by simpa only [abs_of_nonneg positive] using ec,(q 3).unit_normal⟩
    exact C977NortheastFarther.right_shift_excludes p hf q shape equivalent en tc rn shift
  refine ⟨eNegative,?_⟩
  apply lt_of_not_ge
  intro positive
  have en : Normal (q 3).c (-(q 3).s) :=
    ⟨by linarith only [eNegative],by simpa only [abs_of_neg eNegative] using ec,
      by nlinarith only [(q 3).unit_normal]⟩
  have tn : Normal (q 11).c (q 11).s :=
    ⟨positive,by simpa only [abs_of_nonneg positive] using tc,(q 11).unit_normal⟩
  have rc : |(q 10).s|≤(q 10).c := by
    simpa only [abs_of_nonneg rn.1] using rn.2.1
  exact C977NortheastFarther.right_shift_of_farther p hf q shape equivalent rn shift
    (negative_positive_point p hf q shape equivalent en rc tn)

/-- The entire original packing, including its top/right owner exchange,
is transported. The top escape cannot occur with a negative corner. -/
theorem top_shift_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (en : Normal (q 3).c (-(q 3).s)) (rn : |(q 10).s|≤(q 10).c)
    (tn : Normal (q 11).c (-(q 11).s))
    (shift : 3*(q 11).c-2*(q 11).s≤(q 11).loV) : False := by
  let Q : Fin 12→OpenSquare := fun i => swapFrame (q (ownerSwap i))
  have qShape (i : Fin 12) : (Q i).side=
      ((transposePacking p).square (orderedOwner (transposePacking p) i)).side := by
    rw [transpose_owner p hf,transpose_square]
    change (q (ownerSwap i)).side=(p.square (orderedOwner p (ownerSwap i))).side
    exact shape (ownerSwap i)
  have qEquivalent (i : Fin 12) (x y : ℝ) : (Q i).Inside x y↔
      ((transposePacking p).square (orderedOwner (transposePacking p) i)).Inside x y := by
    rw [transpose_owner p hf,transpose_inside]
    exact (inside_swapFrame _ x y).trans (equivalent (ownerSwap i) y x)
  have qE : Normal (Q 3).c (Q 3).s := en
  have qT : |(Q 11).s|≤(Q 11).c := by
    change |-(q 10).s|≤(q 10).c
    simpa only [abs_neg] using rn
  have qR : Normal (Q 10).c (Q 10).s := tn
  have qShift : 3*(Q 10).c+2*(Q 10).s≤(Q 10).loU := by
    change 3*(q 11).c+2*(-(q 11).s)≤(q 11).loV
    linarith only [shift]
  exact C977NortheastFarther.right_shift_excludes (transposePacking p)
    (transpose_family p hf) Q qShape qEquivalent qE qT qR qShift

/-- Simultaneous inward wall displacements are impossible for every
canonical corner sign. An either-wall disjunction remains a separate
global coupling obligation. -/
theorem simultaneous_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (ec : |(q 3).s|≤(q 3).c) (rc : |(q 10).s|≤(q 10).c)
    (tc : |(q 11).s|≤(q 11).c)
    (right : 0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU)
    (top : (q 11).s≤0 ∧ 3*(q 11).c-2*(q 11).s≤(q 11).loV) : False := by
  by_cases sign : 0≤(q 3).s
  · have en : Normal (q 3).c (q 3).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using ec,(q 3).unit_normal⟩
    have rn : Normal (q 10).c (q 10).s :=
      ⟨right.1,by simpa only [abs_of_nonneg right.1] using rc,(q 10).unit_normal⟩
    exact C977NortheastFarther.right_shift_excludes p hf q shape equivalent en tc rn right.2
  · have negative : (q 3).s≤0 := (lt_of_not_ge sign).le
    have en : Normal (q 3).c (-(q 3).s) :=
      ⟨neg_nonneg.mpr negative,by simpa only [abs_of_nonpos negative] using ec,
        by nlinarith only [(q 3).unit_normal]⟩
    have tn : Normal (q 11).c (-(q 11).s) :=
      ⟨neg_nonneg.mpr top.1,by simpa only [abs_of_nonpos top.1] using tc,
        by nlinarith only [(q 11).unit_normal]⟩
    exact top_shift_excludes p hf q shape equivalent en rc tn top.2

#print axioms frame_point
#print axioms all_frame_point
#print axioms right_shift_excludes
#print axioms all_top_shift_excludes
#print axioms positive_top_frame_point
#print axioms positive_top_right_shift_excludes
#print axioms top_shift_excludes
#print axioms simultaneous_excludes
end N12Compact.C977NortheastShift
