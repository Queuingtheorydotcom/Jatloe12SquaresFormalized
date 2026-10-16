import Compact.Completion.OtherCases.C976MergedLeft.ActualOwners
import Compact.Completion.OtherCases.C976NegativeTop.Main

/-! The complete continuous C976 ending on its literal actual-owner
point table. The northwest central marker stays in merged owner Q8.
Both northeast alternatives and every top angle are retained. Source
only: the separate family entrance must still produce this Data. -/
namespace N12Compact.Completion.OtherCases.C976
open S12 S12Pilot
set_option Elab.async false

abbrev Data := C976MergedLeft.ActualOwners.Data

theorem negative_alternative (q : Fin 12 → OpenSquare) (h : Data q)
    (N : OpenSquare) (inside : ∀ x y,N.Inside x y↔(q 7).Inside (2+x) (3+y)) :
    C976NegativeTop.Alternative N := by
  by_cases mixed : (q 7).Inside 2 (113/50)
  · right
    refine ⟨(inside _ _).mpr (by convert mixed using 1 <;> norm_num),?_⟩
    intro x low high own
    let t := (25/6)*(x-13/50)
    have tn : 0≤t := by dsimp only [t]; linarith only [low]
    have tu : t≤1 := by dsimp only [t]; linarith only [high]
    have foreign : (q 6).Inside (2+x) 2 := by
      convert inside_segment (q 6) (113/50) 2 (5/2) 2 t
        h.southeastG6 h.southeastEast tn tu using 1 <;> dsimp only [t] <;> ring
    apply h.apart 7 6 (by decide) _ _ ⟨?_,foreign⟩
    convert (inside _ _).mp own using 1; norm_num
  · left
    have inward := C976MergedLeft.ActualOwners.northeast_inward q h mixed
    refine ⟨(inside _ _).mpr (by convert inward using 1 <;> norm_num),?_⟩
    intro own
    apply mixed
    convert (inside _ _).mp own using 1 <;> norm_num

/-- Reindexing Q11's faces preserves the actual merged Q8 comparison.
This is the existing left/top theorem applied to that same physical top
square; no ordinary northwest owner is substituted for Q8. -/
theorem steep_negative_top (q : Fin 12 → OpenSquare) (h : Data q)
    (W : OpenSquare) (shape : W.side=(q 11).side)
    (inside : ∀ x y,W.Inside x y↔(q 11).Inside x y)
    (cp : 0<W.c) (sn : W.s≤0) : (2/3)*W.c< -W.s := by
  have reach := C976LeftTop.ActualOwners.top_reach q h.toData
  have origin := C976LeftTop.ActualOwners.top_origin q h.toData
  let top : C976LeftTop.TopInput (W.translated 1 2) := {
    anchor := by
      norm_num only [inside_translated_iff]
      exact (inside _ _).mpr reach
    origin := by
      norm_num only [inside_translated_iff]
      exact (inside _ _).mpr origin
    marker := by
      norm_num only [inside_translated_iff]
      exact (inside _ _).mpr h.topMarker
    missing := by
      norm_num only [inside_translated_iff]
      exact fun own => h.apart 11 7 (by decide) _ _ ⟨(inside _ _).mp own,h.northeastG7⟩
    wall := by
      intro x y own
      have actual := (inside _ _).mp ((inside_translated_iff _ _ _ _ _).mp own)
      have bound := (h.box 11 (1+x) (2+y) actual).2.2.2
      linarith only [bound]
  }
  exact C976LeftTop.UpperPoints.steep_negative ((q 8).translated 1 2) (W.translated 1 2)
    (C976LeftTop.ActualOwners.left_input q h.toData) top cp sn
    (by simpa only [OpenSquare.translated,shape] using h.same 8 11)
    (fun x y pair => h.apart 8 11 (by decide) (1+x) (2+y)
      ⟨(inside_translated_iff _ _ _ _ _).mp pair.1,
        (inside _ _).mp ((inside_translated_iff _ _ _ _ _).mp pair.2)⟩)

theorem negative_northeast_impossible (q : Fin 12 → OpenSquare) (h : Data q)
    (R : OpenSquare) (shapeR : R.side=(q 7).side)
    (insideR : ∀ x y,R.Inside x y↔(q 7).Inside x y)
    (cp : 0<R.c) (sn : R.s<0) (order : -R.s≤R.c) : False := by
  let N := R.translated 2 3
  have nInside (x y : ℝ) : N.Inside x y↔(q 7).Inside (2+x) (3+y) :=
    (inside_translated_iff R 2 3 x y).trans (insideR (2+x) (3+y))
  have nSide : 1<N.side := by simpa only [N,OpenSquare.translated,shapeR] using h.side 7
  have marker : N.Inside (7/20) (-13/20) :=
    (nInside _ _).mpr (by convert h.northeastMarker using 1 <;> norm_num)
  have elbow : N.Inside (13/50) 0 :=
    (nInside _ _).mpr (by convert h.northeastG7 using 1 <;> norm_num)
  have right : ¬N.Inside 1 (-11/25) := by
    intro own
    apply h.apart 7 10 (by decide) _ _ ⟨?_,C976MergedLeft.ActualOwners.right_high q h⟩
    convert (nInside _ _).mp own using 1 <;> norm_num
  have alternative := negative_alternative q h N nInside
  obtain ⟨W,wp,canonical,shapeW,insideW,_⟩ := ClosedFrames.canonical_frame (q 11)
  let T := W.translated 2 3
  have tInside (x y : ℝ) : T.Inside x y↔(q 11).Inside (2+x) (3+y) :=
    (inside_translated_iff W 2 3 x y).trans (insideW (2+x) (3+y))
  have same : N.side=T.side := by
    change R.side=W.side
    rw [shapeR,shapeW]
    exact h.same 7 11
  have origin : T.Inside 0 0 := (tInside _ _).mpr (by
    convert C976LeftTop.ActualOwners.top_origin q h.toData using 1 <;> norm_num)
  have left : ¬T.Inside (-18/25) 0 := by
    intro own
    apply h.apart 11 8 (by decide) _ _
      ⟨?_,(C976LeftTop.ActualOwners.left_points q h.toData).2.2⟩
    convert (tInside _ _).mp own using 1 <;> norm_num
  have wall : ∀ x y,T.Inside x y → y≤1 := by
    intro x y own
    have bound := (h.box 11 (2+x) (3+y) ((tInside _ _).mp own)).2.2.2
    linarith only [bound]
  have apart : ∀ x y,¬(N.Inside x y ∧ T.Inside x y) := fun x y pair =>
    h.apart 7 11 (by decide) (2+x) (3+y) ⟨(nInside _ _).mp pair.1,(tInside _ _).mp pair.2⟩
  by_cases sign : 0≤W.s
  · have ordered : W.s≤W.c := by simpa only [abs_of_nonneg sign] using canonical
    have result := C976NegativeTop.angle N T (-R.s)
      (by dsimp only [N,OpenSquare.translated]; ring) nSide same cp
      (by linarith only [sn]) order wp.le sign marker elbow right alternative
      origin left (C981CompletionCornerAdvance.upper_wall T wall) apart
    change 0<W.s ∧ W.c<(2/3)*W.s at result
    linarith only [result.1,result.2,ordered]
  · have turnedWall : ∀ x y,(turnFrame T).Inside x y → y≤1 :=
      fun x y own => wall x y ((turnFrame_inside T x y).mp own)
    have result := C976NegativeTop.angle N (turnFrame T) (-R.s)
      (by dsimp only [N,OpenSquare.translated]; ring) nSide
      (by simpa only [turnFrame_side] using same) cp (by linarith only [sn]) order
      (by dsimp only [turnFrame,T,OpenSquare.translated]; linarith only [sign])
      wp.le marker elbow right alternative ((turnFrame_inside T _ _).mpr origin)
      (fun own => left ((turnFrame_inside T _ _).mp own))
      (C981CompletionCornerAdvance.upper_wall (turnFrame T) turnedWall)
      (fun x y pair => apart x y ⟨pair.1,(turnFrame_inside T x y).mp pair.2⟩)
    change 0<W.c ∧ -W.s<(2/3)*W.c at result
    have contrary := steep_negative_top q h W shapeW insideW wp (le_of_not_ge sign)
    linarith only [contrary,result.2]

theorem impossible (q : Fin 12 → OpenSquare) (h : Data q) : False := by
  obtain ⟨N,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame (q 7)
  by_cases sign : 0≤N.s
  · exact C976MergedLeft.ActualOwners.nonnegative_impossible q h N shape inside cp sign
      (by simpa only [abs_of_nonneg sign] using canonical)
  · exact negative_northeast_impossible q h N shape inside cp (lt_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)

#print axioms negative_northeast_impossible
#print axioms impossible
end N12Compact.Completion.OtherCases.C976
