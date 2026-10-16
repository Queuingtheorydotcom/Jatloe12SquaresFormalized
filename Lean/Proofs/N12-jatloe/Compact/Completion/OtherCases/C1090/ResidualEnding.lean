import Compact.Completion.OtherCases.C1090.ResidualOwners
import Compact.Completion.OtherCases.C976MergedLeft.TopTransfers
import Compact.Completion.OtherCases.C976NegativeTop.Main

/-! C1089-REVERSE-CYCLIC-ENDING sections 7--8, with its literal residual
owner table. This is also the continuous ending required by the supplied
C1090 summary. The missing RESIDUAL-ENDING attachment is not used as a
proof. Both NE alternatives, all square-angle signs, and weak wall/separator
contacts are retained. The raw Input still requires a finite entrance;
this theorem is not ExcludesCase1090 or ExcludesCase1089. Uncompiled source. -/
namespace N12Compact.Completion.OtherCases.C1090.Residual
open S12 S12Pilot
set_option Elab.async false

theorem nonnegative_northeast_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (N : OpenSquare) (shape : N.side=(q 6).side)
    (inside : ∀ x y,N.Inside x y↔(q 6).Inside x y)
    (cp : 0<N.c) (sn : 0≤N.s) (order : N.s≤N.c) : False := by
  have nSide : 1<N.side := by simpa only [shape] using h.side 6
  have wall : ∀ x y,(q 11).Inside x y → y≤4 := fun x y own =>
    (h.box 11 x y own).2.2.2
  have apart : ∀ x y,¬(N.Inside x y ∧ (q 11).Inside x y) := fun x y pair =>
    h.apart 6 11 (by decide) x y ⟨(inside x y).mp pair.1,pair.2⟩
  have origin := top_origin q h
  have foreign := (northwest_upper_points q h).2
  by_cases mixed : (q 6).Inside 2 (113/50)
  · have advance := C976MergedLeft.mixed_top_advance N (q 11) nSide (h.side 11)
      cp sn order ((inside _ _).mpr h.northeastG7) ((inside _ _).mpr mixed)
      (fun own => h.apart 6 5 (by decide) _ _ ⟨(inside _ _).mp own,h.southeastG6⟩)
      h.topMarker h.topF3 wall apart
    have own : (q 11).Inside (7/5) 3 := by
      convert inside_segment (q 11) (127/100) 3 2 3 (13/73)
        advance origin (by norm_num) (by norm_num) using 1 <;> norm_num
    exact h.apart 7 11 (by decide) _ _ ⟨foreign,own⟩
  · have advance := C976MergedLeft.top_only_advance N (q 11) nSide (h.side 11)
      cp sn order ((inside _ _).mpr h.northeastMarker) ((inside _ _).mpr h.northeastG7)
      ((inside _ _).mpr (northeast_outer_sharp q h mixed))
      (fun own => mixed ((inside _ _).mp own))
      (fun own => h.apart 6 2 (by decide) _ _ ⟨(inside _ _).mp own,h.northeastCorner⟩)
      (fun y low high own => h.apart 6 10 (by decide) _ _
        ⟨(inside _ _).mp own,right_bar q h y low high⟩)
      origin wall apart
    have own : (q 11).Inside (7/5) 3 := by
      convert inside_segment (q 11) (6/5) 3 2 3 (1/4)
        advance origin (by norm_num) (by norm_num) using 1 <;> norm_num
    exact h.apart 7 11 (by decide) _ _ ⟨foreign,own⟩

/-- The top-only point follows from the completed upper-square theorems.
In the mixed alternative the full excluded segment is in actual Q5. -/
theorem negative_alternative (q : Fin 12 → OpenSquare) (h : Input q)
    (N : OpenSquare) (inside : ∀ x y,N.Inside x y↔(q 6).Inside (2+x) (3+y)) :
    C976NegativeTop.Alternative N := by
  by_cases mixed : (q 6).Inside 2 (113/50)
  · right
    refine ⟨(inside _ _).mpr (by convert mixed using 1 <;> norm_num),?_⟩
    intro x low high own
    let t := (25/6)*(x-13/50)
    have tn : 0≤t := by dsimp only [t]; linarith only [low]
    have tu : t≤1 := by dsimp only [t]; linarith only [high]
    have foreign : (q 5).Inside (2+x) 2 := by
      convert inside_segment (q 5) (113/50) 2 (5/2) 2 t
        h.southeastG6 (southeast_east q h) tn tu using 1 <;> dsimp only [t] <;> ring
    apply h.apart 6 5 (by decide) _ _ ⟨?_,foreign⟩
    convert (inside _ _).mp own using 1 <;> norm_num
  · left
    have inward := TopOnlyLeftPoint.point_original (q 6) (h.side 6)
      h.northeastMarker h.northeastG7 (northeast_outer_sharp q h mixed) mixed
      (fun own => h.apart 6 11 (by decide) _ _ ⟨own,top_origin q h⟩)
      (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
      (fun y low high own => h.apart 6 10 (by decide) _ _ ⟨own,right_bar q h y low high⟩)
    refine ⟨(inside _ _).mpr (by convert inward using 1 <;> norm_num),?_⟩
    intro own
    apply mixed
    convert (inside _ _).mp own using 1 <;> norm_num

/-- OrdinaryLeftTop Theorem 2 concerns actual Q7 and Q11. Neither the
merged Q8 nor a fictitious northwest-marker owner enters this support join. -/
theorem shallow_top_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (W : OpenSquare) (shape : W.side=(q 11).side)
    (inside : ∀ x y,W.Inside x y↔(q 11).Inside x y)
    (cp : 0<W.c) (sn : W.s≤0) (slope : -W.s≤(2/3)*W.c) : False :=
  OrdinaryLeftTop.ShallowTop.impossible_from_ordinary_input
    ((q 7).translated 1 2) (W.translated 1 2)
    (ordinary_input q h) (top_input q h W inside) cp sn slope
    (by simpa only [OpenSquare.translated,shape] using h.same 7 11)
    (fun x y pair => h.apart 7 11 (by decide) (1+x) (2+y)
      ⟨(inside_translated_iff _ _ _ _ _).mp pair.1,
        (inside _ _).mp ((inside_translated_iff _ _ _ _ _).mp pair.2)⟩)

theorem negative_northeast_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (R : OpenSquare) (shapeR : R.side=(q 6).side)
    (insideR : ∀ x y,R.Inside x y↔(q 6).Inside x y)
    (cp : 0<R.c) (sn : R.s<0) (order : -R.s≤R.c) : False := by
  let N := R.translated 2 3
  have nInside (x y : ℝ) : N.Inside x y↔(q 6).Inside (2+x) (3+y) :=
    (inside_translated_iff R 2 3 x y).trans (insideR (2+x) (3+y))
  have nSide : 1<N.side := by simpa only [N,OpenSquare.translated,shapeR] using h.side 6
  have marker : N.Inside (7/20) (-13/20) :=
    (nInside _ _).mpr (by convert h.northeastMarker using 1 <;> norm_num)
  have elbow : N.Inside (13/50) 0 :=
    (nInside _ _).mpr (by convert h.northeastG7 using 1 <;> norm_num)
  have right : ¬N.Inside 1 (-11/25) := by
    intro own
    apply h.apart 6 10 (by decide) _ _ ⟨?_,h.rightAdvance⟩
    convert (nInside _ _).mp own using 1 <;> norm_num
  have alternative := negative_alternative q h N nInside
  obtain ⟨W,wp,canonical,shapeW,insideW,_⟩ := ClosedFrames.canonical_frame (q 11)
  let T := W.translated 2 3
  have tInside (x y : ℝ) : T.Inside x y↔(q 11).Inside (2+x) (3+y) :=
    (inside_translated_iff W 2 3 x y).trans (insideW (2+x) (3+y))
  have same : N.side=T.side := by
    change R.side=W.side
    rw [shapeR,shapeW]
    exact h.same 6 11
  have origin : T.Inside 0 0 := (tInside _ _).mpr (by
    convert top_origin q h using 1 <;> norm_num)
  have left : ¬T.Inside (-18/25) 0 := by
    intro own
    apply h.apart 11 7 (by decide) _ _ ⟨?_,(northwest_upper_points q h).1⟩
    convert (tInside _ _).mp own using 1 <;> norm_num
  have wall : ∀ x y,T.Inside x y → y≤1 := by
    intro x y own
    have bound := (h.box 11 (2+x) (3+y) ((tInside _ _).mp own)).2.2.2
    linarith only [bound]
  have apart : ∀ x y,¬(N.Inside x y ∧ T.Inside x y) := fun x y pair =>
    h.apart 6 11 (by decide) (2+x) (3+y) ⟨(nInside _ _).mp pair.1,(tInside _ _).mp pair.2⟩
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
    exact shallow_top_impossible q h W shapeW insideW wp
      (le_of_not_ge sign) result.2.le

/-- The full continuous residual ending, starting from the stated strict
point table and genuine walls. The finite reductions producing this Input
are deliberately separate and are not claimed by this declaration. -/
theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False := by
  obtain ⟨N,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame (q 6)
  by_cases sign : 0≤N.s
  · exact nonnegative_northeast_impossible q h N shape inside cp sign
      (by simpa only [abs_of_nonneg sign] using canonical)
  · exact negative_northeast_impossible q h N shape inside cp (lt_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)

#print axioms impossible
end N12Compact.Completion.OtherCases.C1090.Residual
