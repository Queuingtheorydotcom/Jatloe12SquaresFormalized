import Compact.Completion.OtherCases.C1089.ContinuousAnchorCenter
import Compact.Completion.OtherCases.C1089.ContinuousOrigin
import Compact.Completion.OtherCases.C1089.ContinuousNegative
import Compact.Completion.C1092.InwardBarCenter
import Compact.Geometry.WallSignChord

/-! C1089-CONTINUOUS-REDUCTION Theorem 3, with all actual sources.
No missing point is assigned an owner that the input does not supply.
The foreign north marker and the bottom-wall exclusion remain distinct.
No orientation or center bound on C,B,K, and no side cap, is assumed.
This is translated source only; no Lean replay is claimed. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousCenter
open S12 S12Pilot
set_option Elab.async false

structure Input (C W B K : OpenSquare) : Prop where
  side : 1<C.side
  sameW : C.side=W.side
  sameB : C.side=B.side
  sameK : C.side=K.side
  apartCW : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)
  apartCB : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)
  apartCK : ∀ x y,¬(C.Inside x y ∧ K.Inside x y)
  apartWB : ∀ x y,¬(W.Inside x y ∧ B.Inside x y)
  apartWK : ∀ x y,¬(W.Inside x y ∧ K.Inside x y)
  apartBK : ∀ x y,¬(B.Inside x y ∧ K.Inside x y)
  centralMarker : C.Inside (7/20) (7/20)
  centralNorth : C.Inside 0 (13/50)
  centralEast : C.Inside (13/50) 0
  missingNorth : ¬C.Inside (-7/20) (7/20)
  rightMarker : W.Inside (543/500) 0
  rightInner : W.Inside 1 (13/50)
  rightWall : ∀ x y,W.Inside x y → x≤2
  rightSign : 0≤centerY W
  bottomMarker : B.Inside 0 (543/500)
  bottomInner : B.Inside (2/5) 1
  bottomWall : ∀ x y,B.Inside x y → y≤2
  bottomMissing : ¬B.Inside (-13/50) 1
  cornerMarker : K.Inside (543/500) 1
  cornerPoint : K.Inside 1 1
  cornerWalls : ∀ x y,K.Inside x y → x≤2 ∧ y≤2

/-- The reflected actual right wall supplies the strict .39 endpoint.
The only excluded point used by the chord theorem is C's actual marker. -/
theorem right_near (C W : OpenSquare) (side : 1<W.side)
    (markerC : C.Inside (7/20) (7/20)) (markerW : W.Inside (543/500) 0)
    (wall : ∀ x y,W.Inside x y → x≤2) (sign : 0≤centerY W)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : W.Inside 1 (39/100) := by
  let R := C1092RigidCharts.translate (pullX W) 2 (-2)
  have chart (x y : ℝ) : R.Inside x y↔W.Inside (2-x) (y-2) := by
    dsimp only [R]
    rw [C1092RigidCharts.inside_translate,inside_pullX]
    congr 2 <;> ring
  have center : centerY R=centerY W+2 := by
    dsimp only [R,C1092RigidCharts.translate,pullX,centerY]
    linear_combination 2*W.unit_normal
  have chord := WallSignChord.chord R side
    (by
      intro x y own
      have bound := wall _ _ ((chart _ _).mp own)
      linarith only [bound])
    (by norm_num [chart]; exact markerW)
    (by
      intro own
      have actual := (chart _ _).mp own
      norm_num at actual
      exact apart _ _ ⟨markerC,actual⟩)
    (by rw [center]; linarith only [sign]) (239/100) (by norm_num) le_rfl
  have actual := (chart _ _).mp chord
  norm_num at actual
  exact actual

/-- The whole interval includes its endpoints strictly, because both
the origin and .39 endpoint belong to the same open square W. -/
theorem right_bar (C W B K : OpenSquare) (h : Input C W B K) :
    B.Inside (14/25) 1 ∧ ∀ y : ℝ,0≤y → y≤39/100 → W.Inside 1 y := by
  have reach := ContinuousOrigin.right_origin_of_points C W B K
    (by simpa only [←h.sameW] using h.side) (by simpa only [←h.sameB] using h.side)
    (h.sameW.symm.trans h.sameK) h.rightWall h.bottomWall h.cornerWalls
    h.centralNorth h.rightMarker h.rightInner h.bottomMarker h.bottomInner h.bottomMissing
    h.cornerMarker h.cornerPoint
    (fun x y own => h.apartCB _ _ ⟨own.2,own.1⟩)
    (fun x y own => h.apartBK _ _ ⟨own.2,own.1⟩)
    (fun x y own => h.apartWK _ _ ⟨own.2,own.1⟩)
  have near := right_near C W (by simpa only [←h.sameW] using h.side)
    h.centralMarker h.rightMarker h.rightWall h.rightSign h.apartCW
  exact ⟨reach.1,WallProfile.vertical_owned W 1 0 (39/100) (by norm_num) reach.2 near⟩

/-- Both the center and right origin are conclusions of the raw local
four-square geometry. The canonical boundary cases occur in the first branch. -/
theorem points (C W B K : OpenSquare) (h : Input C W B K) :
    C.Inside 0 0 ∧ W.Inside 1 0 := by
  classical
  have bar := right_bar C W B K h
  refine ⟨?_,bar.2 0 le_rfl (by norm_num)⟩
  obtain ⟨V,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame C
  have side : 1<V.side := by simpa only [shape] using h.side
  have M := (inside _ _).mpr h.centralMarker
  have P := (inside _ _).mpr h.centralNorth
  have Q := (inside _ _).mpr h.centralEast
  have apartW : ∀ x y,¬(V.Inside x y ∧ W.Inside x y) :=
    fun x y own => h.apartCW _ _ ⟨(inside _ _).mp own.1,own.2⟩
  have apartB : ∀ x y,¬(V.Inside x y ∧ B.Inside x y) :=
    fun x y own => h.apartCB _ _ ⟨(inside _ _).mp own.1,own.2⟩
  have missingA : ¬V.Inside (2/5) 1 := fun own => apartB _ _ ⟨own,h.bottomInner⟩
  apply (inside 0 0).mp
  by_cases sign : 0≤V.s
  · exact C1092InwardBarCenter.point V side cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) M P Q missingA
      (fun own => apartB _ _ ⟨own,bar.1⟩)
      (fun y lower upper own => apartW _ _ ⟨own,bar.2 y lower upper⟩)
  · have sn : V.s≤0 := (lt_of_not_ge sign).le
    by_cases anchor : V.Inside 1 (2/5)
    · exact ContinuousAnchorCenter.point V W side (shape.trans h.sameW)
        M P Q anchor missingA h.rightMarker h.rightInner h.rightWall h.rightSign apartW
    · by_contra missing
      exact ContinuousNegative.impossible V W B side (shape.trans h.sameW) (shape.trans h.sameB)
        cp sn (by simpa only [abs_of_nonpos sn] using canonical) M P Q missing anchor missingA
        (fun own => h.missingNorth ((inside _ _).mp own)) h.rightMarker h.rightInner
        (bar.2 (39/100) (by norm_num) le_rfl) h.rightWall h.rightSign h.bottomWall
        h.bottomMarker h.bottomInner apartW apartB

#print axioms right_near
#print axioms right_bar
#print axioms points
end N12Compact.Completion.OtherCases.C1089.ContinuousCenter
