import Compact.Completion.FiniteCases.C975SelectionForward
import Compact.Geometry.C849Negative

/-! The genuine merged-top origin in C975. Both top markers belong
to the one actual owner34816. A negative frame omitting the origin also
omits (2,2.5), which supplies the existing full C849 negative obstruction
using the actual left4096, singleton2 and corner192. No northeast
incoming pair or foreign owner for (2,2.5) is assumed. Source only. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem closed {Q : OpenSquare} {x y : ℝ} (own : Q.Inside x y) :
    FourSquareAnchors.ClosedInside Q x y := ⟨own.1.le,own.2.1.le,own.2.2.1.le,own.2.2.2.le⟩

/-- The origin and the lower point share the same potential upper-u
exit. All other origin bands are strict from the two genuine markers. -/
theorem negative_origin_exit (T : OpenSquare) (cp : 0<T.c) (sn : T.s≤0)
    (northwest : T.Inside (33/20) (47/20)) (top : T.Inside 2 (1543/500))
    (missing : ¬T.Inside 2 3) : ¬T.Inside 2 (5/2) := by
  have cap : T.loU+T.side≤2*T.c+3*T.s := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,by nlinarith only [high],?_,?_⟩ <;>
      linarith only [top.1,top.2.2.2,northwest.2.2.1,cp,sn]
  intro own
  linarith only [cap,own.2.1,sn]

/-- The actual C849 negative obstruction forces the lower point in
every nonpositive canonical frame of this same merged34816. The omitted
lower point is only a temporary supposition; no foreign owner is assumed. -/
theorem negative_top_lower (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (T : OpenSquare) (tp : 0<T.c) (sn : T.s≤0) (order : -T.s≤T.c)
    (tshape : T.side=(owner p 34816).side)
    (tinside : ∀ x y,T.Inside x y↔(owner p 34816).Inside x y) :
    T.Inside 2 (5/2) := by
  by_contra missingA
  have h := fixed p hf
  have points := compulsory p hf
  have topF : (owner p 34816).Inside (8/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_point p 34816 3 (by norm_num) (C975IncomingCut.top_left p hf)
  have leftMarker : (owner p 4096).Inside (457/500) 2 := by
    convert seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
      using 1 <;> norm_num
  have leftHigh : (owner p 4096).Inside 1 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 4096 11 (by norm_num) points.leftWall.2
  have singletonSeed : (owner p 2).Inside (19/25) (187/100) := by
    convert seed_point p hf 2 (by decide +kernel) (19/25,187/100) (by decide +kernel)
      using 1 <;> norm_num
  have cornerP : (owner p 192).Inside 1 (1543/500) := by
    convert seed_point p hf 192 (by decide +kernel) (1,1543/500) (by decide +kernel)
      using 1 <;> norm_num
  have cornerQ : (owner p 192).Inside (457/500) 3 := by
    convert seed_point p hf 192 (by decide +kernel) (457/500,3) (by decide +kernel)
      using 1 <;> norm_num
  have M := (tinside _ _).mpr h.northwestMarker
  have H := (tinside _ _).mpr h.topMarker
  obtain ⟨L,lp,lcanonical,lshape,linside,lclosed⟩ := ClosedFrames.canonical_frame (owner p 4096)
  apply C849Negative.impossible T L (owner p 192) tp sn order lp lcanonical
    (by simpa only [tshape] using side p 34816)
  · rw [tshape]
    change (p.square _).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  · exact (tshape.trans (p.congruent _)).trans ((lshape.trans (p.congruent _)).symm)
  · exact (p.congruent _).trans ((tshape.trans (p.congruent _)).symm)
  · exact fun x y own => box p 4096 x y ((linside x y).mp own)
  · exact box p 192
  · exact M
  · exact closed ((tinside _ _).mpr topF)
  · exact H
  · exact missingA
  · exact fun own => foreign p hf 34816 1024 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (northeast_selection p hf).1 ((tinside _ _).mp own)
  · exact (lclosed _ _).mpr (closed leftMarker)
  · exact (lclosed _ _).mpr (closed leftHigh)
  · exact fun own => foreign p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ singletonSeed ((linside _ _).mp own)
  · exact fun own => foreign p hf 4096 256 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.southwestMarker ((linside _ _).mp own)
  · exact cornerP
  · exact cornerQ
  · exact fun x y both => apart _ p hf 34816 4096 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x y ⟨(tinside x y).mp both.1,(linside x y).mp both.2⟩
  · exact fun x y both => apart _ p hf 34816 192 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x y ⟨(tinside x y).mp both.1,both.2⟩

/-- Every canonical sign of the actual merged top owns (2,3). The
negative contradiction retains the complete actual left and corner
squares, their real walls, and the strict singleton2 foreign seed. -/
theorem top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 34816).Inside 2 3 := by
  have h := fixed p hf
  obtain ⟨T,tp,tcanonical,tshape,tinside,_⟩ := ClosedFrames.canonical_frame (owner p 34816)
  have M := (tinside _ _).mpr h.northwestMarker
  have H := (tinside _ _).mpr h.topMarker
  by_cases sign : 0≤T.s
  · apply (tinside _ _).mp
    have order : T.s≤T.c := (abs_le.mp tcanonical).2
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,M.2.2.1,H.2.1,H.2.2.2,tp,sign,order]
  · apply Classical.byContradiction
    intro absent
    have sn : T.s≤0 := (lt_of_not_ge sign).le
    have missing : ¬T.Inside 2 3 := fun own => absent ((tinside _ _).mp own)
    apply negative_origin_exit T tp sn M H missing
    exact negative_top_lower p hf T tp sn (by linarith only [(abs_le.mp tcanonical).1])
      tshape tinside

#print axioms negative_origin_exit
#print axioms negative_top_lower
#print axioms top_origin
end
end N12Compact.FiniteCases.C975Selection
