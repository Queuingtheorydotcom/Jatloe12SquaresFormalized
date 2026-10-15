import Compact.Completion.OtherCases.C976MergedLeft.Main
import Compact.Completion.OtherCases.C976MergedLeft.TopTransfers
import Compact.Completion.OtherCases.C976LeftTop.ActualOwners
import Compact.Completion.OtherCases.UpperBarPoint

/-! The actual C976 owner map. Q8 retains the original merged northwest
marker. The foreign bottom, left, right, and top segments are each formed
inside their single named owner. No claim about the finite family entrance
is included in Data or in these continuous theorems. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft.ActualOwners
open S12 S12Pilot
set_option Elab.async false

structure Data (q : Fin 12 → OpenSquare) : Prop extends C976LeftTop.ActualOwners.Data q where
  northeastMarker : (q 7).Inside (47/20) (47/20)
  northeastF7 : (q 7).Inside (12/5) 3
  northeastCorner : (q 3).Inside 3 3
  southeastF8 : (q 6).Inside 3 (87/50)
  southeastEast : (q 6).Inside (5/2) 2
  rightMarker : (q 10).Inside (1543/500) 2
  rightF9 : (q 10).Inside 3 (113/50)
  rightG9 : (q 10).Inside 3 (12/5)

theorem right_high (q : Fin 12 → OpenSquare) (h : Data q) : (q 10).Inside 3 (64/25) := by
  have advance := WallUpperMissingReach.point (pullX (q 10)) (h.side 10)
    (container_pullX _ (h.box 10))
    (by norm_num only [inside_pullX]; exact h.rightMarker)
    (by norm_num only [inside_pullX]; exact h.rightG9)
    (by
      norm_num only [inside_pullX]
      exact fun own => h.apart 10 6 (by decide) _ _ ⟨own,h.southeastF8⟩)
    (by
      norm_num only [inside_pullX]
      exact fun own => h.apart 10 7 (by decide) _ _ ⟨own,h.northeastMarker⟩)
  norm_num only [inside_pullX] at advance
  exact advance

theorem right_bar (q : Fin 12 → OpenSquare) (h : Data q)
    (y : ℝ) (low : 113/50≤y) (high : y≤64/25) : (q 10).Inside 3 y := by
  let t := (10/3)*(y-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 10) 3 (113/50) 3 (64/25) t h.rightF9 (right_high q h) tn tu
    using 1 <;> dsimp only [t] <;> ring

theorem northeast_sharp (q : Fin 12 → OpenSquare) (h : Data q)
    (missing : ¬(q 7).Inside 2 (113/50)) : (q 7).Inside (101/40) (17/8) := by
  have origin := C976LeftTop.ActualOwners.top_origin q h.toData
  exact UpperBarPoint.point_original (q 7) (h.side 7) h.northeastMarker h.northeastF7 missing
    (fun own => h.apart 7 11 (by decide) _ _ ⟨own,origin⟩)
    (fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun y low high own => h.apart 7 10 (by decide) _ _ ⟨own,right_bar q h y low high⟩)

theorem northeast_inward (q : Fin 12 → OpenSquare) (h : Data q)
    (missing : ¬(q 7).Inside 2 (113/50)) : (q 7).Inside 2 (131/50) := by
  have origin := C976LeftTop.ActualOwners.top_origin q h.toData
  exact TopOnlyLeftPoint.point_original (q 7) (h.side 7) h.northeastMarker h.northeastG7
    (northeast_sharp q h missing) missing
    (fun own => h.apart 7 11 (by decide) _ _ ⟨own,origin⟩)
    (fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun y low high own => h.apart 7 10 (by decide) _ _ ⟨own,right_bar q h y low high⟩)

/-- The local merged-left theorem uses the actual Q11 advance and
derives the duplicate point; it does not assume that target in Q8. -/
theorem of_top_advance (q : Fin 12 → OpenSquare) (h : C976LeftTop.ActualOwners.Data q)
    (advance : (q 11).Inside (127/100) 3) : False := by
  have chart (x y : ℝ) : ((q 8).translated 1 2).Inside x y↔(q 8).Inside (1+x) (2+y) :=
    inside_translated_iff _ _ _ _ _
  have input : Input ((q 8).translated 1 2) where
    side := h.side 8
    left := (chart _ _).mpr (by convert h.leftMarker using 1 <;> norm_num)
    marker := (chart _ _).mpr (by convert h.northwestMarker using 1 <;> norm_num)
    inward := (chart _ _).mpr (by convert h.leftF1 using 1 <;> norm_num)
    middle := by
      intro own
      apply h.apart 8 5 (by decide) _ _ ⟨?_,h.southwestWest⟩
      convert (chart _ _).mp own using 1 <;> norm_num
    corner := by
      intro own
      apply h.apart 8 4 (by decide) _ _ ⟨?_,h.cornerPoint⟩
      convert (chart _ _).mp own using 1 <;> norm_num
    top := by
      intro x low high own
      let t := (100/47)*(x-27/100)
      have tn : 0≤t := by dsimp only [t]; linarith only [low]
      have tu : t≤1 := by dsimp only [t]; linarith only [high]
      have foreign : (q 11).Inside (1+x) 3 := by
        convert inside_segment (q 11) (127/100) 3 (87/50) 3 t advance h.topG4 tn tu
          using 1 <;> dsimp only [t] <;> ring
      apply h.apart 8 11 (by decide) _ _ ⟨?_,foreign⟩
      convert (chart _ _).mp own using 1 <;> norm_num
    segment := by
      intro t low high own
      have foreign : (q 1).Inside (1+(-6/25+(6/25)*t))
          (2+(-13/100-(13/100)*t)) := by
        convert inside_segment (q 1) (19/25) (187/100) 1 (87/50) t
          h.singleton1Seed h.singleton1Near low high using 1 <;> ring
      exact h.apart 8 1 (by decide) _ _ ⟨(chart _ _).mp own,foreign⟩
  have leftPoint : (q 8).Inside (127/100) (49/25) := by
    convert (chart _ _).mp (point _ input) using 1 <;> norm_num
  exact h.apart 8 5 (by decide) _ _
    ⟨leftPoint,C976LeftTop.ActualOwners.southwest_point q h⟩

/-- Both exact northeast alternatives are retained by the F5 case split.
The omitted-F5 branch needs no invented foreign owner for that point. -/
theorem nonnegative_impossible (q : Fin 12 → OpenSquare) (h : Data q)
    (N : OpenSquare) (shape : N.side=(q 7).side)
    (inside : ∀ x y,N.Inside x y↔(q 7).Inside x y)
    (cp : 0<N.c) (sn : 0≤N.s) (order : N.s≤N.c) : False := by
  have nSide : 1<N.side := by simpa only [shape] using h.side 7
  have apart : ∀ x y,¬(N.Inside x y ∧ (q 11).Inside x y) :=
    fun x y pair => h.apart 7 11 (by decide) x y ⟨(inside _ _).mp pair.1,pair.2⟩
  have wall : ∀ x y,(q 11).Inside x y → y≤4 := fun x y own => (h.box 11 x y own).2.2.2
  by_cases mixed : (q 7).Inside 2 (113/50)
  · have advance := mixed_top_advance N (q 11) nSide (h.side 11) cp sn order
      ((inside _ _).mpr h.northeastG7) ((inside _ _).mpr mixed)
      (fun own => h.apart 7 6 (by decide) _ _ ⟨(inside _ _).mp own,h.southeastG6⟩)
      h.topMarker h.topF3 wall apart
    exact of_top_advance q h.toData advance
  · have advance := top_only_advance N (q 11) nSide (h.side 11) cp sn order
      ((inside _ _).mpr h.northeastMarker) ((inside _ _).mpr h.northeastG7)
      ((inside _ _).mpr (northeast_sharp q h mixed))
      (fun own => mixed ((inside _ _).mp own))
      (fun own => h.apart 7 3 (by decide) _ _ ⟨(inside _ _).mp own,h.northeastCorner⟩)
      (fun y low high own => h.apart 7 10 (by decide) _ _
        ⟨(inside _ _).mp own,right_bar q h y low high⟩)
      (C976LeftTop.ActualOwners.top_origin q h.toData) wall apart
    have shorter : (q 11).Inside (127/100) 3 := by
      convert inside_segment (q 11) (6/5) 3 (87/50) 3 (7/54)
        advance h.topG4 (by norm_num) (by norm_num) using 1 <;> norm_num
    exact of_top_advance q h.toData shorter

#print axioms of_top_advance
#print axioms nonnegative_impossible
end N12Compact.Completion.OtherCases.C976MergedLeft.ActualOwners
