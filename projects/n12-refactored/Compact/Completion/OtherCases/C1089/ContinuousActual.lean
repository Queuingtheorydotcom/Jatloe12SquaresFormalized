import Compact.Completion.OtherCases.C1089.ContinuousCenter

/-! The two actual-owner applications in C1089-CONTINUOUS-REDUCTION
section 5. Each compulsory auxiliary is still an explicit input from the
original point-covering entrance; these adapters do not assert that
finite entrance has already been checked or integrated. The original
Q0 seed in the southeast application is the horizontal (1.74,1).
Source translation only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousActual
open S12 S12Pilot
set_option Elab.async false

private def southeastChart (Q : OpenSquare) : OpenSquare :=
  C1092RigidCharts.translate (pullY Q) 2 2

private def northwestChart (Q : OpenSquare) : OpenSquare :=
  C1092RigidCharts.translate (pullY (pullSwap Q)) 2 2

private theorem southeast_inside (Q : OpenSquare) (x y : ℝ) :
    (southeastChart Q).Inside x y↔Q.Inside (x+2) (2-y) := by
  dsimp only [southeastChart]
  rw [C1092RigidCharts.inside_translate,inside_pullY]
  congr 2 <;> ring

private theorem northwest_inside (Q : OpenSquare) (x y : ℝ) :
    (northwestChart Q).Inside x y↔Q.Inside (2-y) (x+2) := by
  dsimp only [northwestChart]
  rw [C1092RigidCharts.inside_translate,inside_pullY,inside_pullSwap]
  congr 2 <;> ring

/-- The actual southeast inward owner forces its center and the origin
of the actual right wall. The foreign bottom seed stays in Q0. -/
theorem southeast (q : Fin 12 → OpenSquare)
    (side : ∀ i,1<(q i).side) (same : ∀ i j,(q i).side=(q j).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (centralMarker : (q 5).Inside (47/20) (33/20))
    (centralF4 : (q 5).Inside 2 (87/50))
    (centralG6 : (q 5).Inside (113/50) 2)
    (southwestMarker : (q 4).Inside (33/20) (33/20))
    (rightMarker : (q 10).Inside (1543/500) 2)
    (rightF8 : (q 10).Inside 3 (87/50)) (rightSign : centerY (q 10)≤2)
    (bottomMarker : (q 9).Inside 2 (457/500))
    (bottomF6 : (q 9).Inside (12/5) 1)
    (singletonG2 : (q 0).Inside (87/50) 1)
    (cornerMarker : (q 1).Inside (1543/500) 1)
    (cornerPoint : (q 1).Inside 3 1) :
    (q 5).Inside 2 2 ∧ (q 10).Inside 3 2 := by
  let qs (i : Fin 12) := southeastChart (q i)
  have chart (i : Fin 12) (x y : ℝ) :
      (qs i).Inside x y↔(q i).Inside (x+2) (2-y) := southeast_inside _ _ _
  have localApart (i j : Fin 12) (different : i≠j) (x y : ℝ) :
      ¬((qs i).Inside x y ∧ (qs j).Inside x y) := by
    intro own
    exact apart i j different _ _ ⟨(chart _ _ _).mp own.1,(chart _ _ _).mp own.2⟩
  have center : centerY (qs 10)=2-centerY (q 10) := by
    dsimp only [qs,southeastChart,C1092RigidCharts.translate,pullY,centerY]
    linear_combination 2*(q 10).unit_normal
  have input : ContinuousCenter.Input (qs 5) (qs 10) (qs 9) (qs 1) := {
    side := side 5
    sameW := same 5 10
    sameB := same 5 9
    sameK := same 5 1
    apartCW := localApart 5 10 (by decide)
    apartCB := localApart 5 9 (by decide)
    apartCK := localApart 5 1 (by decide)
    apartWB := localApart 10 9 (by decide)
    apartWK := localApart 10 1 (by decide)
    apartBK := localApart 9 1 (by decide)
    centralMarker := by norm_num [chart]; exact centralMarker
    centralNorth := by norm_num [chart]; exact centralF4
    centralEast := by norm_num [chart]; exact centralG6
    missingNorth := by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apart 5 4 (by decide) _ _ ⟨actual,southwestMarker⟩
    rightMarker := by norm_num [chart]; exact rightMarker
    rightInner := by norm_num [chart]; exact rightF8
    rightWall := by
      intro x y own
      have wall := contained 10 _ _ ((chart _ _ _).mp own)
      linarith only [wall.2.1]
    rightSign := by rw [center]; linarith only [rightSign]
    bottomMarker := by norm_num [chart]; exact bottomMarker
    bottomInner := by norm_num [chart]; exact bottomF6
    bottomWall := by
      intro x y own
      have wall := contained 9 _ _ ((chart _ _ _).mp own)
      linarith only [wall.2.2.1]
    bottomMissing := by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apart 9 0 (by decide) _ _ ⟨actual,singletonG2⟩
    cornerMarker := by norm_num [chart]; exact cornerMarker
    cornerPoint := by norm_num [chart]; exact cornerPoint
    cornerWalls := by
      intro x y own
      have wall := contained 1 _ _ ((chart _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],by linarith only [wall.2.2.1]⟩ }
  have result := ContinuousCenter.points _ _ _ _ input
  constructor
  · have actual := (chart 5 0 0).mp result.1
    norm_num at actual
    exact actual
  · have actual := (chart 10 1 0).mp result.2
    norm_num at actual
    exact actual

/-- The actual northwest inward owner forces its center and the origin
of the actual top wall. Its excluded left point belongs to Q4, not Q0. -/
theorem northwest (q : Fin 12 → OpenSquare)
    (side : ∀ i,1<(q i).side) (same : ∀ i j,(q i).side=(q j).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (centralMarker : (q 7).Inside (33/20) (47/20))
    (centralG3 : (q 7).Inside (87/50) 2)
    (centralF5 : (q 7).Inside 2 (113/50))
    (southwestMarker : (q 4).Inside (33/20) (33/20))
    (topMarker : (q 11).Inside 2 (1543/500))
    (topG4 : (q 11).Inside (87/50) 3) (topSign : centerX (q 11)≤2)
    (leftMarker : (q 8).Inside (457/500) 2)
    (leftG1 : (q 8).Inside 1 (12/5))
    (southwestF0 : (q 4).Inside 1 (87/50))
    (cornerMarker : (q 3).Inside 1 (1543/500))
    (cornerPoint : (q 3).Inside 1 3) :
    (q 7).Inside 2 2 ∧ (q 11).Inside 2 3 := by
  let qs (i : Fin 12) := northwestChart (q i)
  have chart (i : Fin 12) (x y : ℝ) :
      (qs i).Inside x y↔(q i).Inside (2-y) (x+2) := northwest_inside _ _ _
  have localApart (i j : Fin 12) (different : i≠j) (x y : ℝ) :
      ¬((qs i).Inside x y ∧ (qs j).Inside x y) := by
    intro own
    exact apart i j different _ _ ⟨(chart _ _ _).mp own.1,(chart _ _ _).mp own.2⟩
  have center : centerY (qs 11)=2-centerX (q 11) := by
    dsimp only [qs,northwestChart,C1092RigidCharts.translate,pullY,pullSwap,centerY,centerX]
    linear_combination 2*(q 11).unit_normal
  have input : ContinuousCenter.Input (qs 7) (qs 11) (qs 8) (qs 3) := {
    side := side 7
    sameW := same 7 11
    sameB := same 7 8
    sameK := same 7 3
    apartCW := localApart 7 11 (by decide)
    apartCB := localApart 7 8 (by decide)
    apartCK := localApart 7 3 (by decide)
    apartWB := localApart 11 8 (by decide)
    apartWK := localApart 11 3 (by decide)
    apartBK := localApart 8 3 (by decide)
    centralMarker := by norm_num [chart]; exact centralMarker
    centralNorth := by norm_num [chart]; exact centralG3
    centralEast := by norm_num [chart]; exact centralF5
    missingNorth := by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apart 7 4 (by decide) _ _ ⟨actual,southwestMarker⟩
    rightMarker := by norm_num [chart]; exact topMarker
    rightInner := by norm_num [chart]; exact topG4
    rightWall := by
      intro x y own
      have wall := contained 11 _ _ ((chart _ _ _).mp own)
      linarith only [wall.2.2.2]
    rightSign := by rw [center]; linarith only [topSign]
    bottomMarker := by norm_num [chart]; exact leftMarker
    bottomInner := by norm_num [chart]; exact leftG1
    bottomWall := by
      intro x y own
      have wall := contained 8 _ _ ((chart _ _ _).mp own)
      linarith only [wall.1]
    bottomMissing := by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apart 8 4 (by decide) _ _ ⟨actual,southwestF0⟩
    cornerMarker := by norm_num [chart]; exact cornerMarker
    cornerPoint := by norm_num [chart]; exact cornerPoint
    cornerWalls := by
      intro x y own
      have wall := contained 3 _ _ ((chart _ _ _).mp own)
      exact ⟨by linarith only [wall.2.2.2],by linarith only [wall.1]⟩ }
  have result := ContinuousCenter.points _ _ _ _ input
  constructor
  · have actual := (chart 7 0 0).mp result.1
    norm_num at actual
    exact actual
  · have actual := (chart 11 1 0).mp result.2
    norm_num at actual
    exact actual

#print axioms southeast
#print axioms northwest
end N12Compact.Completion.OtherCases.C1089.ContinuousActual
