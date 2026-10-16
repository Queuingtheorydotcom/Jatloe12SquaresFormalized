import Compact.Completion.FiniteCases.C580581UpperChain
import Compact.Completion.OtherCases.InwardSign
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.RightTripleData

/-! Both original C580/C581 families enter the same physical three-square
problem as C983. Every frame represents its actual original owner, and all
three pairwise disjointness statements are retained. This file supplies an
entrance only; it does not assume or assert the three-square contradiction. -/
namespace N12Compact.FiniteCases.C580581TripleEntrance
open S12 S12Pilot C580581Entrance C580581Points
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
noncomputable section
set_option Elab.async false

private theorem seed_point (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (mask : Nat) (member : mask∈family v)
    (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport mask)) :
    (owner p mask).Inside P.1 P.2 := seed _ p hf mask member P checked

private theorem foreign (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (m n : Nat)
    (hm : m∈family v) (hn : n∈family v) (different : m≠n)
    (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun h => apart _ p hf m n hm hn different x y ⟨h,own⟩

private theorem bottom_bar (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (x : ℝ)
    (low : 113/50≤x) (high : x≤14/5) :
    (owner p (bottomMask v)).Inside x 1 := by
  have near : (owner p (bottomMask v)).Inside (113/50) 1 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 4
  exact horizontal_segment _ _ _ _ _ near (C580581PilotInputs.bottom_far v p hf)
    (by norm_num) low high

private theorem right_bar (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (y : ℝ)
    (low : 2≤y) (high : y≤14/5) :
    (owner p 16384).Inside 3 y :=
  vertical_segment _ _ _ _ _ (C580581UpperChain.right_origin v p hf)
    (C580581PilotInputs.right_far v p hf) (by norm_num) low high

theorem southeast_negative_frame (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    ∃ E : OpenSquare,0<E.c ∧ E.s<0 ∧ -E.s≤E.c ∧ E.side=(owner p 512).side ∧
      (∀ x y,E.Inside x y ↔ (owner p 512).Inside (x+2) (y+2)) := by
  obtain ⟨E,cp,range,shape,physical,_⟩ := ClosedFrames.canonical_frame ((owner p 512).translated 2 2)
  have same : ∀ x y,E.Inside x y ↔ (owner p 512).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff,add_comm] using physical x y
  have size : 1<E.side := by simpa only [shape,OpenSquare.translated] using side p 512
  have equal : ((owner p 2304).translated 2 2).side=E.side := by
    rw [shape]
    exact (p.congruent _).trans (p.congruent _).symm
  have west : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have marker : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point v p hf 512 (by fin_cases v <;> decide +kernel)
      (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have inner : (owner p 512).Inside 2 (87/50) := by
    obtain ⟨_,_,_,_,_,south,_,_,_⟩ := compulsory v p hf
    have h := (auxiliary_exact p 512 4 (by norm_num)).mpr south
    simpa [auxPoints,fPoints,gPoints] using h
  have elbow : (owner p 512).Inside (113/50) 2 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 6
  have singleton : (owner p 8).Inside 3 (87/50) := by
    have h := seed_point v p hf 8 (by fin_cases v <;> decide +kernel)
      (3,87/50) (by decide +kernel)
    norm_num at h; exact h
  have negative : E.s<0 := by
    apply lt_of_not_ge
    intro sign
    apply InwardSign.positive_impossible ((owner p 2304).translated 2 2) E size equal
      cp sign (by simpa only [abs_of_nonneg sign] using range)
    · norm_num [inside_translated_iff]; exact west
    · norm_num [inside_translated_iff]; exact C580581CentralEntrance.merged_center v p hf
    · norm_num [inside_translated_iff]; exact C580581CentralEntrance.merged_inward v p hf
    · apply (same _ _).mpr; norm_num; exact marker
    · apply (same _ _).mpr; norm_num; exact inner
    · apply (same _ _).mpr; norm_num; exact elbow
    · intro own
      have original := (same _ _).mp own
      norm_num at original
      exact foreign v p hf 512 8 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ singleton original
    · intro x lo hi own
      have original := (same _ _).mp own
      norm_num at original
      exact foreign v p hf 512 (bottomMask v) (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel) _ _
        (bottom_bar v p hf (x+2) (by linarith only [lo]) (by linarith only [hi])) original
    · intro x y own
      exact apart _ p hf 2304 512 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) (x+2) (y+2)
        ⟨by simpa only [add_comm] using (inside_translated_iff (owner p 2304) 2 2 x y).mp own.1,(same _ _).mp own.2⟩
  exact ⟨E,cp,negative,by simpa only [abs_of_neg negative] using range,shape,same⟩

theorem northeast_profile (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    ∃ N : OpenSquare,N.side=(owner p 1024).side ∧
      (∀ x y,N.Inside x y ↔ (owner p 1024).Inside (x+2) (y+2)) ∧
      TopOnlyQuadrantProfile.Data N ∧ N.Inside (21/40) (1/8) ∧
      N.Inside (1/2) 1 ∧ N.Inside 0 (31/50) := by
  have marker : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point v p hf 1024 (by fin_cases v <;> decide +kernel)
      (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have top := C580581CentralEntrance.northeast_top v p hf
  have corner : (owner p 48).Inside 3 3 := by
    have h := seed_point v p hf 48 (by fin_cases v <;> decide +kernel)
      (3,3) (by decide +kernel)
    norm_num at h; exact h
  have missingL : ¬(owner p 1024).Inside 2 (113/50) :=
    foreign v p hf 1024 2304 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (C580581CentralEntrance.merged_inward v p hf)
  have missingP : ¬(owner p 1024).Inside 2 3 :=
    foreign v p hf 1024 32768 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (C580581UpperChain.top_origin v p hf)
  have missingC : ¬(owner p 1024).Inside 3 3 :=
    foreign v p hf 1024 48 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ corner
  have avoid (y : ℝ) (lo : 113/50≤y) (hi : y≤64/25) :
      ¬(owner p 1024).Inside 3 y :=
    foreign v p hf 1024 16384 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (right_bar v p hf y (by linarith only [lo]) (by linarith only [hi]))
  have sharp := UpperBarPoint.point_original (owner p 1024) (side p 1024)
    marker top.1 missingL missingP missingC avoid
  have left := TopOnlyLeftPoint.point_original (owner p 1024) (side p 1024)
    marker top.2 sharp missingL missingP missingC avoid
  obtain ⟨N,shape,physical,profile⟩ := TopOnlyQuadrantProfile.frame
    ((owner p 1024).translated 2 2) (side p 1024)
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact top.2)
    (by norm_num [inside_translated_iff]; exact sharp)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingC)
    (by
      intro y lo hi own
      have original : (owner p 1024).Inside 3 (y+2) := by
        convert (inside_translated_iff (owner p 1024) 2 2 1 y).mp own using 1 <;> ring
      exact avoid (y+2) (by linarith only [lo]) (by linarith only [hi]) original)
  have same : ∀ x y,N.Inside x y ↔ (owner p 1024).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff,add_comm 2 x,add_comm 2 y] using physical x y
  refine ⟨N,shape,same,profile,?_,?_,?_⟩
  · apply (same _ _).mpr; norm_num; exact sharp
  · apply (same _ _).mpr; norm_num; exact C580581UpperChain.northeast_extension v p hf
  · apply (same _ _).mpr; norm_num; exact left

theorem entrance (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    ∃ E N R : OpenSquare,RightTripleData.Input E N R ∧
      (∀ x y,¬(E.Inside x y ∧ N.Inside x y)) ∧
      (∀ x y,E.Inside x y ↔ (owner p 512).Inside (x+2) (y+2)) ∧
      (∀ x y,N.Inside x y ↔ (owner p 1024).Inside (x+2) (y+2)) ∧
      (∀ x y,R.Inside x y ↔ (owner p 16384).Inside (x+2) (y+2)) := by
  obtain ⟨E,cp,sn,order,eShape,ePhysical⟩ := southeast_negative_frame v p hf
  obtain ⟨N,nShape,nPhysical,nProfile,nSharp,nTop,nLeft⟩ := northeast_profile v p hf
  have rOrigin : ((owner p 16384).translated 2 2).Inside 1 0 := by
    norm_num [inside_translated_iff]; exact C580581UpperChain.right_origin v p hf
  have rUpper : ((owner p 16384).translated 2 2).Inside 1 (14/25) := by
    norm_num [inside_translated_iff]
    exact right_bar v p hf (64/25) (by norm_num) (by norm_num)
  have rWall : ∀ x y,((owner p 16384).translated 2 2).Inside x y → x≤2 := by
    intro x y own
    have original := (inside_translated_iff _ _ _ _ _).mp own
    have bound := (box p 16384 (2+x) (2+y) original).2.1
    linarith only [bound]
  obtain ⟨R,rShape,rSame,rProfile⟩ := RightTripleData.right_frame
    ((owner p 16384).translated 2 2) rOrigin rUpper rWall
  have rPhysical : ∀ x y,R.Inside x y ↔ (owner p 16384).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff,add_comm] using rSame x y
  have size : 1<E.side := by simpa only [eShape] using side p 512
  have marker : E.Inside (7/20) (-7/20) := by
    apply (ePhysical _ _).mpr
    norm_num
    have h := seed_point v p hf 512 (by fin_cases v <;> decide +kernel)
      (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have elbow : E.Inside (13/50) 0 := by
    apply (ePhysical _ _).mpr
    norm_num
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 6
  have apartEN : ∀ x y,¬(E.Inside x y ∧ N.Inside x y) := by
    intro x y own
    exact apart _ p hf 512 1024 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) (x+2) (y+2)
      ⟨(ePhysical _ _).mp own.1,(nPhysical _ _).mp own.2⟩
  have apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y) := by
    intro x y own
    exact apart _ p hf 512 16384 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) (x+2) (y+2)
      ⟨(ePhysical _ _).mp own.1,(rPhysical _ _).mp own.2⟩
  have apartNR : ∀ x y,¬(N.Inside x y ∧ R.Inside x y) := by
    intro x y own
    exact apart _ p hf 1024 16384 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) (x+2) (y+2)
      ⟨(nPhysical _ _).mp own.1,(rPhysical _ _).mp own.2⟩
  have eProfile := NegativeTripleFaces.faces E (-E.s) (by ring) size cp
    (by linarith only [sn]) order marker elbow
    (by
      intro own
      have original := (ePhysical _ _).mp own
      norm_num at original
      exact C580581PilotInputs.southeast_missing_center v p hf original)
    (by
      intro own
      have original := (ePhysical _ _).mp own
      norm_num at original
      exact foreign v p hf 512 16384 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
        (C580581UpperChain.right_origin v p hf) original)
    (fun own => apartEN _ _ ⟨own,nSharp⟩)
    (by
      intro x lo hi own
      have original := (ePhysical _ _).mp own
      norm_num at original
      exact foreign v p hf 512 (bottomMask v) (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel) _ _
        (bottom_bar v p hf (x+2) (by linarith only [lo]) (by linarith only [hi])) original)
  have sameEN : E.side=N.side := by
    rw [eShape,nShape]
    exact (p.congruent _).trans (p.congruent _).symm
  have sameER : E.side=R.side := by
    rw [eShape,rShape]
    exact (p.congruent _).trans (p.congruent _).symm
  exact ⟨E,N,R,⟨sameEN,sameER,eProfile,nProfile,rProfile,marker,elbow,nSharp,nTop,nLeft,
    apartER,apartNR⟩,apartEN,ePhysical,nPhysical,rPhysical⟩

#print axioms southeast_negative_frame
#print axioms northeast_profile
#print axioms entrance
end
end N12Compact.FiniteCases.C580581TripleEntrance
