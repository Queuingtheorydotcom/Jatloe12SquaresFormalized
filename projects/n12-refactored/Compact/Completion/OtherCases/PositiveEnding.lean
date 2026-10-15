import Compact.Completion.OtherCases.PositiveEndingSupports

/-! The complete positive southeast ending over the two original physical
squares. All western orientations, actual SAT axes and reverse directions
are exhausted; neither ownership nor exclusion of F4 is assumed. -/
namespace N12Compact.Completion.OtherCases.PositiveEnding
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem impossible (W E : OpenSquare) (side : 1<E.side) (same : W.side=E.side)
    (cap : W.side≤1001/1000) (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-13/50))
    (missingOrigin : ¬E.Inside 1 0) (missingSharp : ¬E.Inside (21/40) (1/8))
    (bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (left : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y)
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : False := by
  have data := PositiveEndingFaces.faces E side cp sp order marker elbow outer
    missingOrigin missingSharp bottom
  obtain ⟨w,wp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame W
  have p := (inside _ _).mpr west
  have o := (inside _ _).mpr center
  have same' : w.side=E.side := shape.trans same
  have side' : 1<w.side := by simpa only [same'] using side
  have cap' : w.side≤1001/1000 := by simpa only [shape] using cap
  have disjoint : ∀ x y,¬(w.Inside x y ∧ E.Inside x y) :=
    fun x y own => apart x y ⟨(inside _ _).mp own.1,own.2⟩
  have bar (y : ℝ) (low : 0≤y) (high : y≤4/5) : ¬w.Inside (-1) y :=
    fun own => left y low high ((inside _ _).mp own)
  have missingZ : ¬w.Inside 0 (-C1092WallProfileScalars.half E.c E.s) :=
    fun own => disjoint _ _ ⟨own,data.lowerPoint⟩
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper w nx ny≤lower E nx ny) : 0<nx ∧ ny<0 := by
    have first := (strict_bounds w _ _ nx ny unit p).2
    have last := (strict_bounds E _ _ nx ny unit marker).1
    have firstY := (strict_bounds w 0 0 nx ny unit o).2
    have lastY := (strict_bounds E _ _ nx ny unit data.lowerPoint).1
    have product : 0<(-ny)*(C1092WallProfileScalars.half E.c E.s) := by
      linarith only [firstY,lastY,sep]
    have negative := (mul_pos_iff_of_pos_right data.halfPositive).mp product
    constructor <;> linarith only [first,last,sep,negative]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower w nx ny) :
      upper w (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have bounds := abs_le.mp range
  have noWU (sep : upper w w.c w.s≤lower E w.c w.s ∨
      upper E w.c w.s≤lower w w.c w.s) : False := by
    rcases sep with forward | backward
    · by_cases sign : 0≤w.s
      · have signCone := cone w.c w.s w.unit_normal forward
        linarith only [signCone.2,sign]
      · exact PositiveEndingSupports.negative_w_axis w E (-w.s) (by ring) wp
          (by linarith only [sign]) (by linarith only [bounds.1]) side' cap' data p o bar forward
    · have signCone := cone (-w.c) (-w.s)
        (by simpa only [neg_sq] using w.unit_normal) (reverse _ _ backward)
      linarith only [signCone.1,wp]
  have noWV (sep : upper w (-w.s) w.c≤lower E (-w.s) w.c ∨
      upper E (-w.s) w.c≤lower w (-w.s) w.c) : False := by
    have unit : (-w.s)^2+w.c^2=1 := by nlinarith only [w.unit_normal]
    rcases sep with forward | backward
    · have signCone := cone (-w.s) w.c unit forward
      linarith only [signCone.2,wp]
    · have opposite : upper w w.s (-w.c)≤lower E w.s (-w.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      by_cases sign : 0≤w.s
      · exact PositiveEndingSupports.positive_w_axis w E wp sign bounds.2
          side' cap' data p o missingZ bar opposite
      · have signCone := cone w.s (-w.c) (by nlinarith only [w.unit_normal]) opposite
        linarith only [signCone.1,sign]
  have noEU (sep : upper w E.c E.s≤lower E E.c E.s ∨
      upper E E.c E.s≤lower w E.c E.s) : False := by
    rcases sep with forward | backward
    · have signCone := cone E.c E.s E.unit_normal forward
      linarith only [signCone.2,sp]
    · have signCone := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [signCone.1,cp]
  have noEV (sep : upper w (-E.s) E.c≤lower E (-E.s) E.c ∨
      upper E (-E.s) E.c≤lower w (-E.s) E.c) : False := by
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    rcases sep with forward | backward
    · have signCone := cone (-E.s) E.c unit forward
      linarith only [signCone.1,sp]
    · apply PositiveEndingSupports.own_axis w E data p
      simpa only [neg_neg] using reverse _ _ backward
  have axes := CongruentSAT.faceSeparation_of_disjoint w E same' disjoint
  change pairRadius w E≤|w.c*(centerX E-centerX w)+w.s*(centerY E-centerY w)| ∨
    pairRadius w E≤|-w.s*(centerX E-centerX w)+w.c*(centerY E-centerY w)| ∨
    pairRadius E w≤|E.c*(centerX E-centerX w)+E.s*(centerY E-centerY w)| ∨
    pairRadius E w≤|-E.s*(centerX E-centerX w)+E.c*(centerY E-centerY w)| at axes
  have separate (nx ny R : ℝ)
      (radius : supportRadius w nx ny+supportRadius E nx ny=R)
      (axis : R≤|nx*(centerX E-centerX w)+ny*(centerY E-centerY w)|) :=
    separated w E nx ny (by rwa [radius])
  rcases axes with wu | wv | eu | ev
  · exact noWU (separate _ _ _ (parallel_radius w E) wu)
  · exact noWV (separate _ _ _ (transverse_radius w E) wv)
  · have radius : supportRadius w E.c E.s+supportRadius E E.c E.s=pairRadius E w := by
      rw [add_comm]
      exact parallel_radius E w
    exact noEU (separate _ _ _ radius eu)
  · have radius : supportRadius w (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E w := by
      rw [add_comm]
      exact transverse_radius E w
    exact noEV (separate _ _ _ radius ev)


/-- The axial case is excluded by the two true southeast anchors and the
foreign right origin. This extends the ending through the zero endpoint. -/
theorem nonnegative_impossible (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side) (cap : W.side≤1001/1000)
    (cp : 0<E.c) (sn : 0≤E.s) (order : E.s≤E.c)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-13/50))
    (missingOrigin : ¬E.Inside 1 0) (missingSharp : ¬E.Inside (21/40) (1/8))
    (bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (left : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y)
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : False := by
  by_cases positive : 0<E.s
  · exact impossible W E side same cap cp positive order west center marker elbow outer
      missingOrigin missingSharp bottom left apart
  · have zero : E.s=0 := by linarith only [sn,positive]
    have f := outer
    have d := elbow
    apply missingOrigin
    simp only [OpenSquare.Inside,InBands,zero,mul_zero,zero_mul,neg_zero,zero_add,
      add_zero,mul_one] at f d ⊢
    exact ⟨f.1,f.2.1,by linarith only [f.2.2.1,cp],d.2.2.2⟩

#print axioms impossible
#print axioms nonnegative_impossible
end N12Compact.Completion.OtherCases.PositiveEnding
