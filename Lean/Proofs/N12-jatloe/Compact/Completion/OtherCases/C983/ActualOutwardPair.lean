import Compact.Completion.OtherCases.C983.ActualOutwardFrame
import Compact.Completion.OtherCases.OutwardPair

/-! The full actual C983 coupled-pair application. Its angle, support
faces and sharp point come from one physical southeast frame; northeast
inward/top anchors and each foreign source are explicit arguments. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem southeast_outward_pair_exclusion (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 5) (g8 : 18∈actual p 5) (noG6 : 16∉actual p 5)
    (nF5 : 5∈actual p 6) (nG7 : 17∈actual p 6)
    (topOrigin : (owners p 11).Inside 2 3) : False := by
  obtain ⟨r,cp,sn,order,shape,same,faces⟩ := southeast_outward_frame p hf f8 g8 noG6
  let A := (pullY r).translated 2 2
  let N := (owners p 6).translated 2 2
  have aInside (x y : ℝ) : A.Inside x y ↔ (owners p 5).Inside (x+2) (y+2) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY,same,inside_pullY]
    rw [show 4-(4-(2+y))=y+2 by ring,add_comm 2 x]
  have nInside (x y : ℝ) : N.Inside x y ↔ (owners p 6).Inside (x+2) (y+2) := by
    simpa only [add_comm] using inside_translated_iff (owners p 6) 2 2 x y
  have sideR : 1<r.side := by rw [shape]; exact owners_side p 5
  have actualSame : A.side=N.side := shape.trans (owners_same_side p 5 6)
  have upperU : A.loU+A.side≤A.c+r.s := by
    have h := faces.upperU
    dsimp only [A,pullY,OpenSquare.translated] at h ⊢
    linarith only [h]
  have lowerV : -A.c+(4/5)*r.s≤A.loV := by
    have h := faces.upperV
    dsimp only [A,pullY,OpenSquare.translated] at h ⊢
    linarith only [h]
  have halfHigh : half A.c r.s<143/500 :=
    SharpPointScalars.half_upper r.c r.s (143/500) cp faces.sinePositive r.unit_normal
      faces.upperSpan
  have lowerHalf := SharpPointScalars.half_lower r.c r.s (37/50)
    cp sn order r.unit_normal faces.lowerSpan
  have halfLow : 13/87<half A.c r.s := by
    change 13/87<half r.c r.s
    linarith only [lowerHalf]
  have eMarker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have southMarker : A.Inside (7/20) (-7/20) := by
    apply (aInside _ _).mpr
    norm_num only
    exact eMarker
  have southY : A.Inside (21/40) (1/8) := by
    apply (aInside _ _).mpr
    norm_num only
    exact southeast_outward_point p hf f8 g8 noG6
  have nMarker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have northF : (owners p 6).Inside 2 (113/50) := by
    have h := auxiliary_inside p 6 5 (by decide +kernel) nF5
    simpa [auxPoints,fPoints,gPoints] using h
  have northG : (owners p 6).Inside (113/50) 3 := by
    have h := auxiliary_inside p 6 17 (by decide +kernel) nG7
    simpa [auxPoints,fPoints,gPoints] using h
  have northwest : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  have noL : ¬(owners p 6).Inside (33/20) (47/20) :=
    fun h => owners_apart p hf 6 7 (by decide +kernel) _ _ ⟨h,northwest⟩
  have noP0 : ¬(owners p 6).Inside 2 3 :=
    fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,topOrigin⟩
  have noP1 : ¬(owners p 6).Inside 3 3 :=
    fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩
  exact OutwardPair.impossible A N r.s sideR actualSame rfl cp sn order
    halfLow halfHigh upperU lowerV southMarker southY
    (by apply (nInside _ _).mpr; norm_num only; exact nMarker)
    (by apply (nInside _ _).mpr; norm_num only; exact northF)
    (by apply (nInside _ _).mpr; norm_num only; exact northG)
    (by
      intro h
      have point := (nInside _ _).mp h
      norm_num only at point
      exact noL point)
    (by
      intro h
      have point := (nInside _ _).mp h
      norm_num only at point
      exact noP0 point)
    (by
      intro h
      have point := (nInside _ _).mp h
      norm_num only at point
      exact noP1 point)
    (by
      intro x y h
      exact owners_apart p hf 5 6 (by decide +kernel) (x+2) (y+2)
        ⟨(aInside x y).mp h.1,(nInside x y).mp h.2⟩)


end
#print axioms southeast_outward_pair_exclusion
end N12Compact.Completion.OtherCases.C983

