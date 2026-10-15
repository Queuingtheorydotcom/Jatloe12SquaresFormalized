import Compact.Bridge.C696PositiveBottomWest
import Compact.Bridge.C696NextBottomWall
import S12.FamilyTransport

/-! Center-first normalization of the full original C696 packing.
Mutual disjointness chooses a central square missing (2,2); a physical
half-turn puts it southwest and a physical diagonal reflection makes its
canonical frame nonnegative. The completed corner/sign implications then
leave one actual residual configuration. No historical corner-root module
or saved pose state is used. Source only, uncompiled. -/
namespace N12Compact.C696CentralNormalForm

open S12 S12Pilot S12Completion.C696 SideSignPacking C977CornerCubic
set_option Elab.async false

def symmetry : Fin 2 → Transform := ![⟨false,true,true⟩,⟨true,false,false⟩]
def permutation : Fin 2 → Fin 12 → Fin 12 := ![
  ![3,4,5,0,1,2,7,6,10,11,8,9],
  ![1,0,5,4,3,2,6,7,9,8,11,10]]

private theorem symmetry_mem : ∀ k, symmetry k∈allTransforms := by decide
private theorem family_symmetry : ∀ k, family.image (symmetry k).maskAction=family := by decide
private theorem mask_symmetry : ∀ k i,
    (symmetry k).maskAction (ownerMasks i)=ownerMasks (permutation k i) := by decide
private theorem masks_candidate : ∀ m∈family, m∈candidateMasks := by decide

theorem pulled_family (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (k : Fin 2) : codedMarkerFamily ((symmetry k).pullPacking p)=family := by
  have subset : family⊆codedMarkerFamily ((symmetry k).pullPacking p) := by
    intro m hm
    have member : (symmetry k).maskAction m∈codedMarkerFamily p := by
      rw [hf,←family_symmetry k]
      exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
    obtain ⟨i,_,code⟩ := Finset.mem_image.mp member
    have markers : ExactMarkers (p.square i) (maskSupport ((symmetry k).maskAction m)) := by
      rw [←code]
      exact coded_exact p i
    have transformed := exact_markers_pull (symmetry k) (symmetry_mem k)
      (p.square i) m (masks_candidate m hm) markers
    have supports : maskSupport (markerCode ((symmetry k).pullPacking p) i)=maskSupport m := by
      apply Finset.ext
      intro j
      exact (coded_exact ((symmetry k).pullPacking p) i j).symm.trans (transformed j)
    have same := candidate_support_injective _ _
      (markerCode_spec ((symmetry k).pullPacking p) i).1 (masks_candidate m hm) supports
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,same⟩
  apply (Finset.eq_of_subset_of_card_le subset ?_).symm
  rw [codedMarkerFamily_card]
  decide

theorem pulled_owner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (k : Fin 2) (i : Fin 12) :
    ownerIndex ((symmetry k).pullPacking p) (ownerMasks i)=
      ownerIndex p (ownerMasks (permutation k i)) := by
  let j := ownerIndex p (ownerMasks (permutation k i))
  have code : markerCode p j=ownerMasks (permutation k i) :=
    ownerIndex_spec p _ (by rw [hf]; exact ownerMasks_mem _)
  have markers : ExactMarkers (p.square j)
      (maskSupport ((symmetry k).maskAction (ownerMasks i))) := by
    simpa only [mask_symmetry,code] using coded_exact p j
  have transformed := exact_markers_pull (symmetry k) (symmetry_mem k)
    (p.square j) (ownerMasks i) (masks_candidate _ (ownerMasks_mem i)) markers
  have supports : maskSupport (markerCode ((symmetry k).pullPacking p) j)=
      maskSupport (ownerMasks i) := by
    apply Finset.ext
    intro m
    exact (coded_exact ((symmetry k).pullPacking p) j m).symm.trans (transformed m)
  have newCode := candidate_support_injective _ _
    (markerCode_spec ((symmetry k).pullPacking p) j).1
    (masks_candidate _ (ownerMasks_mem i)) supports
  apply markerCode_injective ((symmetry k).pullPacking p)
  exact (ownerIndex_spec ((symmetry k).pullPacking p) (ownerMasks i)
    (by rw [pulled_family p hf k]; exact ownerMasks_mem i)).trans newCode.symm

theorem pulled_inside (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (k : Fin 2) (i : Fin 12) (x y : ℝ) :
    (owners ((symmetry k).pullPacking p) i).Inside x y ↔
      (owners p (permutation k i)).Inside ((symmetry k).apply x y).1
        ((symmetry k).apply x y).2 := by
  simp only [owners,pulled_owner p hf k i]
  change ((symmetry k).pull (p.square _)).Inside x y ↔ _
  exact inside_pull _ _ x y

theorem pulled_side (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (k : Fin 2) (i : Fin 12) :
    (owners ((symmetry k).pullPacking p) i).side=(owners p (permutation k i)).side := by
  simp only [owners,pulled_owner p hf k i]
  change ((symmetry k).pull (p.square _)).side=(p.square _).side
  exact pull_same_side _ _

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have hi := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  exact different (AuxiliaryNecessity.ownerMasks_injective
    (hi.symm.trans ((congrArg (markerCode p) equal).trans hj)))

/-- The missing central point is selected from actual mutual disjointness,
not assumed for one fixed original central owner. -/
theorem missing_center_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∃ q : NormalizedPacking, codedMarkerFamily q=family ∧ ¬(owners q 6).Inside 2 2 := by
  classical
  by_cases missing : ¬(owners p 6).Inside 2 2
  · exact ⟨p,hf,missing⟩
  · have own : (owners p 6).Inside 2 2 := not_not.mp missing
    refine ⟨(symmetry 0).pullPacking p,pulled_family p hf 0,?_⟩
    intro h
    have other := (pulled_inside p hf 0 6 2 2).mp h
    norm_num [symmetry,permutation,Transform.apply] at other
    exact apart p hf 6 7 (by decide) 2 2 ⟨own,other⟩

private noncomputable def swapped (A : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (turnFrame (pullSwap A)))

private theorem swapped_inside (A : OpenSquare) (x y : ℝ) :
    (swapped A).Inside x y↔A.Inside y x := by
  simp only [swapped,turnFrame_inside,inside_pullSwap]

private theorem nonnegative_central_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 2 2) :
    ∃ q : NormalizedPacking, codedMarkerFamily q=family ∧
      ∃ A : OpenSquare, Normal A.c A.s ∧ A.side=(owners q 6).side ∧
        (∀ x y, A.Inside x y↔(owners q 6).Inside x y) ∧ ¬(owners q 6).Inside 2 2 := by
  obtain ⟨A,_,canonical,shape,equivalent,_⟩ := ClosedFrames.canonical_frame (owners p 6)
  by_cases nonnegative : 0≤A.s
  · exact ⟨p,hf,A,⟨nonnegative,(le_abs_self A.s).trans canonical,A.unit_normal⟩,
      shape,equivalent,missing⟩
  · have negative : A.s<0 := lt_of_not_ge nonnegative
    let q := (symmetry 1).pullPacking p
    have normal : Normal (swapped A).c (swapped A).s := by
      have h : Normal A.c (-A.s) := ⟨by linarith only [negative],
        by simpa only [abs_of_neg negative] using canonical,
        by nlinarith only [A.unit_normal]⟩
      simpa only [swapped,turnFrame,pullSwap,neg_neg] using h
    have same : (owners q 6).side=(owners p 6).side := by
      simpa [q,permutation] using pulled_side p hf 1 6
    have inside : ∀ x y, (swapped A).Inside x y↔(owners q 6).Inside x y := by
      intro x y
      have original : (owners q 6).Inside x y↔(owners p 6).Inside y x := by
        simpa [q,symmetry,permutation,Transform.apply] using pulled_inside p hf 1 6 x y
      exact (swapped_inside A x y).trans ((equivalent y x).trans original.symm)
    have shape' : (swapped A).side=(owners q 6).side := by
      change A.side=(owners q 6).side
      exact shape.trans same.symm
    have missing' : ¬(owners q 6).Inside 2 2 := by
      intro h
      have original := (pulled_inside p hf 1 6 2 2).mp h
      norm_num [symmetry,permutation,Transform.apply] at original
      exact missing original
    exact ⟨q,pulled_family p hf 1,swapped A,normal,shape',inside,missing'⟩

/-- One original-packing residual; A and O are descriptions of the actual
southwest central and bottom owners, not independent local squares. -/
structure Data (p : NormalizedPacking) (A O : OpenSquare) : Prop where
  centralNormal : Normal A.c A.s
  centralPositive : 0<A.s
  centralSide : A.side=(owners p 6).side
  centralInside : ∀ x y, A.Inside x y↔(owners p 6).Inside x y
  bottomCosine : 0<O.c
  bottomNegative : O.s<0
  bottomSteep : 1/5< -O.s
  bottomCanonical : |O.s|≤O.c
  bottomSide : O.side=(owners p 0).side
  bottomInside : ∀ x y, O.Inside x y↔(owners p 0).Inside x y
  missingCenter : ¬(owners p 6).Inside 2 2
  centralWest : (owners p 6).Inside 1 2
  leftCorner : (owners p 1).Inside 1 1
  missingCorner : ¬(owners p 0).Inside 1 1

theorem cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∃ q : NormalizedPacking, codedMarkerFamily q=family ∧
      ∃ A O : OpenSquare, Data q A O := by
  obtain ⟨q,hq,missing⟩ := missing_center_cover p hf
  obtain ⟨r,hr,A,an,aSide,aInside,missingCenter⟩ := nonnegative_central_cover q hq missing
  have leftCorner := C696CornerReach.left_corner r hr A an aSide aInside missingCenter
  have missingCorner : ¬(owners r 0).Inside 1 1 := fun h =>
    apart r hr 0 1 (by decide) 1 1 ⟨h,leftCorner⟩
  have positive : 0<A.s := by
    by_contra no
    have zero : A.s=0 := by linarith only [an.1,no]
    have negativeNormal : Normal A.c (-A.s) := by simpa only [zero,neg_zero] using an
    have center := C696NegativeCentral.center_of_negative_frame r hr missingCorner A (-A.s)
      (by ring) negativeNormal aSide aInside
    exact missingCenter center
  obtain ⟨O,oc,canonical,oSide,oInside,_⟩ := ClosedFrames.canonical_frame (owners r 0)
  have negative := C696PositiveBottomWest.canonical_sine_negative r hr O canonical
    oSide oInside missingCorner missingCenter
  have centralWest : (owners r 6).Inside 1 2 := by
    by_contra missingWest
    exact C696NextBottomWall.missing_west r hr missingCorner missingCenter missingWest
  have on : Normal O.c (-O.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,
    by nlinarith only [O.unit_normal]⟩
  have bottomSteep : 1/5< -O.s := by
    apply lt_of_not_ge
    intro small
    exact C696NextBottomWall.excludes_of_small_bottom r hr O (-O.s)
      (by ring) on small oSide oInside missingCorner
  exact ⟨r,hr,A,O,{
    centralNormal := an, centralPositive := positive,
    centralSide := aSide, centralInside := aInside,
    bottomCosine := oc, bottomNegative := negative, bottomSteep := bottomSteep,
    bottomCanonical := canonical,
    bottomSide := oSide, bottomInside := oInside,
    missingCenter := missingCenter, centralWest := centralWest,
    leftCorner := leftCorner, missingCorner := missingCorner }⟩

/-- The unchanged original case contract now needs one continuous
configuration, rather than the historical two missing-corner roots. -/
theorem excludes_of_normal_form
    (exclude : ∀ p : NormalizedPacking, codedMarkerFamily p=family →
      ∀ A O : OpenSquare, Data p A O → False) : ExcludesCase 696 := by
  intro row member ident p familyEq
  obtain ⟨q,hq,A,O,data⟩ := cover p (familyEq.trans (row_family row member ident))
  exact exclude q hq A O data

#print axioms cover
#print axioms excludes_of_normal_form
end N12Compact.C696CentralNormalForm
