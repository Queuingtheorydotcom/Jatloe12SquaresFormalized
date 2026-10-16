import Compact.Completion.OtherCases.C1089.LastSectorSupportJoin
import Compact.Completion.OtherCases.OutwardBarFrame
import Compact.Completion.OtherCases.OutwardPair
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Main

/-! C1089-LAST-SECTOR-ENDING.md section 2, with its actual foreign owners.
The southwest extra point is derived from the two alternatives for the
northwest F5. Its canonical frame, half-angle and support faces are all
obtained from the original strict points and the one actual singleton bar.
No exact auxiliary label is needed by this continuous implication.
This source has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorExtra
open S12 S12Pilot
open C1092WallProfileScalars
set_option Elab.async false

/-- The chapter's actual point table before the southwest extra is forced.
Every segment below is formed inside its one named original owner. -/
structure Input (q : Fin 12 → OpenSquare) : Prop
    extends LastSectorSupportJoin.BaseData q where
  sameSouthwestNorthwest : (q 4).side=(q 7).side
  southwestF0 : (q 4).Inside 1 (87/50)
  southwestG0 : (q 4).Inside 1 (8/5)
  singletonCorner : (q 0).Inside 1 1
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  absentMarker : ∀ i, ¬(q i).Inside (457/500) 1
  leftMarker : (q 8).Inside (457/500) 2
  leftNear : (q 8).Inside 1 (113/50)
  leftFar : (q 8).Inside 1 (64/25)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF3 : (q 7).Inside (8/5) 3
  northwestG4 : (q 7).Inside (87/50) 3
  northwestCorner : (q 3).Inside 1 3

/-- The genuine singleton bar gives A's crosspoint and excludes Q8's
optional G3, without assigning the absent marker to the singleton. -/
theorem southwest_crosspoint_and_left_omission (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside (3/2) 2 ∧ ¬(q 8).Inside (87/50) 2 :=
  OrdinaryBarCrosspoint.southwest_point_and_left_omission (q 4) (q 0) (q 8)
    (h.side 4) h.southwestMarker h.southwestF0 h.southwestG0
    h.singletonNear h.singletonFar h.leftMarker (h.absentMarker 4)
    (h.apart 4 0 (by decide)) (h.apart 4 8 (by decide))

/-- The one original southwest square must strictly own G3. Both F5
alternatives of the original northwest square are excluded geometrically. -/
theorem southwest_extra (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside (87/50) 2 := by
  by_contra missing
  let rotated := pullY (pullX (q 4))
  have rotatedChart (x y : ℝ) :
      rotated.Inside x y ↔ (q 4).Inside (4-x) (4-y) := by
    dsimp only [rotated]
    rw [inside_pullY,inside_pullX]
  have singletonBar (x : ℝ) (low : 28/25≤x) (high : x≤87/50) :
      (q 0).Inside x 1 := by
    have bar := WallProfile.vertical_owned (pullSwap (q 0)) 1 (28/25) (87/50)
      (by norm_num)
      (by norm_num [inside_pullSwap]; exact h.singletonNear)
      (by norm_num [inside_pullSwap]; exact h.singletonFar)
    exact (inside_pullSwap _ _ _).mp (bar x low high)
  have rotMarker : rotated.Inside (47/20) (47/20) := by
    apply (rotatedChart _ _).mpr
    convert h.southwestMarker using 1 <;> norm_num
  have rotOutward : rotated.Inside 3 (113/50) := by
    apply (rotatedChart _ _).mpr
    convert h.southwestF0 using 1 <;> norm_num
  have rotUpper : rotated.Inside 3 (12/5) := by
    apply (rotatedChart _ _).mpr
    convert h.southwestG0 using 1 <;> norm_num
  have rotMissingG : ¬rotated.Inside (113/50) 2 := by
    intro own
    apply missing
    have actual := (rotatedChart _ _).mp own
    convert actual using 1 <;> norm_num
  have rotMissingR : ¬rotated.Inside (1543/500) 2 := by
    intro own
    have actual := (rotatedChart _ _).mp own
    norm_num at actual
    exact h.apart 4 8 (by decide) _ _ ⟨actual,h.leftMarker⟩
  have rotMissingP : ¬rotated.Inside 3 3 := by
    intro own
    have actual := (rotatedChart _ _).mp own
    norm_num at actual
    exact h.apart 4 0 (by decide) _ _ ⟨actual,h.singletonCorner⟩
  have rotMissingH : ¬rotated.Inside (1543/500) 3 := by
    intro own
    have actual := (rotatedChart _ _).mp own
    norm_num at actual
    exact h.absentMarker 4 actual
  have rotAvoid (x : ℝ) (low : 113/50≤x) (high : x≤14/5) :
      ¬rotated.Inside x 3 := by
    intro own
    have actual := (rotatedChart _ _).mp own
    norm_num only at actual
    exact h.apart 4 0 (by decide) _ _
      ⟨actual,singletonBar (4-x) (by linarith only [high]) (by linarith only [low])⟩
  obtain ⟨r,cp,sn,order,shape,same,faces⟩ := OutwardBarFrame.frame_original
    rotated (h.side 4) rotMarker rotOutward rotUpper
    rotMissingG rotMissingR rotMissingP rotMissingH rotAvoid
  have sideR : 1<r.side := by
    rw [shape]
    exact h.side 4
  have rMarker := (same _ _).mpr rotMarker
  have rOutward := (same _ _).mpr rotOutward
  have rSharp := OutwardBarPoint.positive_point_original r sideR cp sn order
    rMarker rOutward
    (fun own => rotMissingG ((same _ _).mp own))
    (fun own => rotMissingR ((same _ _).mp own))
    (fun own => rotMissingP ((same _ _).mp own))
    (fun own => rotMissingH ((same _ _).mp own))
    (fun x low high own => rotAvoid x low high ((same _ _).mp own))
  let A := (pullY r).translated 2 2
  let N := (pullX (q 7)).translated 2 2
  have rChart (x y : ℝ) : r.Inside x y ↔ (q 4).Inside (4-x) (4-y) :=
    (same x y).trans (rotatedChart x y)
  have aChart (x y : ℝ) : A.Inside x y ↔ (q 4).Inside (2-x) (2+y) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY,rChart,
      show (4:ℝ)-(2+x)=2-x by ring,
      show (4:ℝ)-(4-(2+y))=2+y by ring]
  have nChart (x y : ℝ) : N.Inside x y ↔ (q 7).Inside (2-x) (2+y) := by
    dsimp only [N]
    rw [inside_translated_iff,inside_pullX,
      show (4:ℝ)-(2+x)=2-x by ring]
  have aMarker : A.Inside (7/20) (-7/20) := by
    apply (aChart _ _).mpr
    convert h.southwestMarker using 1 <;> norm_num
  have aSharp : A.Inside (21/40) (1/8) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY]
    convert rSharp using 1 <;> norm_num
  have aUpperU : A.loU+A.side≤A.c+r.s := by
    have bound := faces.upperU
    dsimp only [A,pullY,OpenSquare.translated] at bound ⊢
    linarith only [bound]
  have aLowerV : -A.c+(4/5)*r.s≤A.loV := by
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
  have nMarker : N.Inside (7/20) (7/20) := by
    apply (nChart _ _).mpr
    convert h.northwestMarker using 1 <;> norm_num
  have nAnchor : N.Inside (2/5) 1 := by
    apply (nChart _ _).mpr
    convert h.northwestF3 using 1 <;> norm_num
  have nG : N.Inside (13/50) 1 := by
    apply (nChart _ _).mpr
    convert h.northwestG4 using 1 <;> norm_num
  have nMissingL : ¬N.Inside (-7/20) (7/20) := by
    intro own
    have actual := (nChart _ _).mp own
    norm_num at actual
    exact h.apart 7 6 (by decide) _ _ ⟨actual,h.northeastMarker⟩
  have nMissingP0 : ¬N.Inside 0 1 := by
    intro own
    have actual := (nChart _ _).mp own
    norm_num at actual
    exact h.apart 7 11 (by decide) _ _ ⟨actual,h.topOrigin⟩
  have nMissingP1 : ¬N.Inside 1 1 := by
    intro own
    have actual := (nChart _ _).mp own
    norm_num at actual
    exact h.apart 7 3 (by decide) _ _ ⟨actual,h.northwestCorner⟩
  have actualApart : ∀ x y, ¬(A.Inside x y ∧ N.Inside x y) := by
    intro x y own
    exact h.apart 4 7 (by decide) _ _
      ⟨(aChart x y).mp own.1,(nChart x y).mp own.2⟩
  by_cases northF5 : (q 7).Inside 2 (113/50)
  · have nF : N.Inside 0 (13/50) := by
      apply (nChart _ _).mpr
      convert northF5 using 1 <;> norm_num
    have sameSide : A.side=N.side := shape.trans h.sameSouthwestNorthwest
    exact OutwardPair.impossible A N r.s sideR sameSide rfl cp sn order
      halfLow halfHigh aUpperU aLowerV aMarker aSharp nMarker nF nG
      nMissingL nMissingP0 nMissingP1 actualApart
  · have nMissingF : ¬N.Inside 0 (13/50) := by
      intro own
      apply northF5
      have actual := (nChart _ _).mp own
      convert actual using 1 <;> norm_num
    have leftBar := WallProfile.vertical_owned (q 8) 1 (113/50) (64/25)
      (by norm_num) h.leftNear h.leftFar
    have nAvoid (y : ℝ) (low : 13/50≤y) (high : y≤14/25) :
        ¬N.Inside 1 y := by
      intro own
      have actual := (nChart _ _).mp own
      norm_num only at actual
      exact h.apart 7 8 (by decide) _ _
        ⟨actual,leftBar (2+y) (by linarith only [low]) (by linarith only [high])⟩
    have nSharp := UpperBarPoint.point N (h.side 7) nMarker nAnchor
      nMissingF nMissingP0 nMissingP1 nAvoid
    exact actualApart _ _ ⟨aSharp,nSharp⟩

/-- Sections 2--5 of the final-sector chapter, using the new eight-point
terminal. The southwest extra is proved here, rather than passed in. -/
theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False := by
  apply LastSectorSupportJoin.impossible q
  exact { toBaseData := h.toBaseData, southwestExtra := southwest_extra q h }

#print axioms southwest_extra
#print axioms southwest_crosspoint_and_left_omission
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastSectorExtra
