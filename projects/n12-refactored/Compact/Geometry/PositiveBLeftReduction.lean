import Compact.Geometry.LeftUpperCover
import Compact.Geometry.C849PositiveSupport

/-! Exact positive-B reduction for the unfinished 849/851 configuration.
The upper face premise is the real cap supplied by the foreign point
(2.26,3), not the stronger cap from the earlier four-square template.
The conclusion is a pair of necessary face bounds, not a case exclusion. -/

namespace N12Compact.PositiveBLeftReduction

open S12 S12Pilot FourSquareAnchors

theorem low_inside (B : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (ha : 1 < B.side)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (upper : B.loU+B.side ≤ (113/50)*B.c+3*B.s)
    (lower : -2*B.s+(5/2)*B.c ≤ B.loV) :
    B.Inside (7/5) (5/2) := by
  have shortU := (short_projections B (43/50) (1/2) (by norm_num)).2.1
  have shortV := (short_projections B (-(3/5)) 0 (by norm_num)).2.2.2
  exact ⟨by linarith only [upper,shortU,ha],
    by linarith only [top.2.1,bc,bs],
    by linarith only [bottom.2.2.1,bc,bs],
    by linarith only [lower,shortV,ha]⟩

/-- Genuine pair coupling strengthens B's lower longitudinal face to the
height 2.83, and identifies L's lower transverse face. No C-square premise
has been discarded: its upper-U cap remains an explicit hypothesis. -/
theorem coupled_faces (B L : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (haB : 1 < B.side) (haL : 1 < L.side)
    (boxL : InsideContainer L)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (upper : B.loU+B.side ≤ (113/50)*B.c+3*B.s)
    (lower : -2*B.s+(5/2)*B.c ≤ B.loV)
    (left : ClosedInside L (457/500) 2)
    (lTop : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) :
    B.c+(283/100)*B.s ≤ B.loU ∧
      -L.s*(19/25)+L.c*(187/100) ≤ L.loV := by
  have low := low_inside B bc bs bsc haB bottom top upper lower
  obtain ⟨high,lFace⟩ := LeftUpperCover.high_of_not_low L lc lsc haL boxL
    left lTop missingLow missingRight (fun h => apart _ _ ⟨low,h⟩)
  have cSeven : 7/10 ≤ B.c := by
    have square := mul_nonneg (sub_nonneg.mpr bsc) (add_nonneg bc.le bs)
    nlinarith only [B.unit_normal,square,bc,sq_nonneg (B.c-7/10)]
  have sumBound : B.c+B.s ≤ 10/7 := by
    nlinarith only [B.unit_normal,sq_nonneg (B.c-B.s),
      sq_nonneg (B.c+B.s-10/7)]
  have highUpperU : B.c+B.s*(283/100) < B.loU+B.side := by
    linarith only [top.2.1,bc,bs]
  have highLowerV : B.loV < -B.s+B.c*(283/100) := by
    linarith only [bottom.2.2.1,bc,bs]
  have highUpperV : -B.s+B.c*(283/100) < B.loV+B.side := by
    linarith only [lower,haB,cSeven,sumBound]
  refine ⟨?_,lFace⟩
  apply le_of_not_gt
  intro highLowerU
  have inside : B.Inside 1 (283/100) := by
    simpa only [mul_one,mul_comm (283/100) B.s] using
      (show InBands B.loU B.loV B.side
        (B.c+B.s*(283/100)) (-B.s+B.c*(283/100)) from
        ⟨by linarith only [highLowerU],highUpperU,highLowerV,highUpperV⟩)
  exact apart _ _ ⟨inside,high⟩

/-- The fourth owner's actual marker (1,3) is stronger than the previously
used missing point (1,3.086). Its transverse alternative forces a steep
positive B frame, uniformly over all angles. -/
theorem upper_left_marker_modes (B : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (ha : 1 < B.side)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (lower : -2*B.s+(5/2)*B.c ≤ B.loV)
    (missing : ¬ B.Inside 1 3) :
    B.c+3*B.s ≤ B.loU ∨
      (B.loV+B.side ≤ -B.s+3*B.c ∧
        B.side ≤ B.s+B.c/2 ∧ 3*B.c/4 < B.s) := by
  have upperU : B.c+3*B.s < B.loU+B.side := by
    linarith only [top.2.1,bc]
  have lowerV : B.loV < -B.s+3*B.c := by
    linarith only [bottom.2.2.1,bc,bs]
  by_cases below : B.c+3*B.s ≤ B.loU
  · exact Or.inl below
  · have upperV : B.loV+B.side ≤ -B.s+3*B.c := by
      apply le_of_not_gt
      intro hv
      apply missing
      exact ⟨by simpa only [mul_one] using lt_of_not_ge below,
        by simpa only [mul_one] using upperU,
        by simpa only [mul_one] using lowerV,
        by simpa only [mul_one] using hv⟩
    have height : B.side ≤ B.s+B.c/2 := by
      linarith only [lower,upperV]
    refine Or.inr ⟨upperV,height,?_⟩
    apply lt_of_not_ge
    intro shallow
    have product := mul_nonneg bc.le
      (show 0 ≤ 3*B.c/4-B.s by linarith only [shallow])
    have above : 1 < B.s+B.c/2 := lt_of_lt_of_le ha height
    nlinarith only [B.unit_normal,product,above,
      sq_nonneg (B.s+B.c/2-1)]

/-- If C's original missing point is above its upper U face, the actual
forced C point (2.086,3) eliminates B's lower-U alternative outright.
This theorem consumes the correctly weakened C point cap explicitly. -/
theorem not_lower_U_of_right_cap (B : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (ha : 1 < B.side)
    (bottom : ClosedInside B (33/20) (47/20))
    (lower : -2*B.s+(5/2)*B.c ≤ B.loV)
    (rightCap : B.loU+B.side ≤ (1043/500)*B.c+3*B.s) :
    ¬ (B.c+3*B.s ≤ B.loU) := by
  intro below
  have ratio : 3*B.c ≤ 7*B.s := by
    linarith only [bottom.2.2.1,lower]
  have square := mul_nonneg (sub_nonneg.mpr ratio)
    (show 0 ≤ 7*B.s+3*B.c by linarith only [bc,bs])
  have wide : 500/543 < B.c := by linarith only [below,rightCap,ha]
  have positiveSquare := mul_pos (sub_pos.mpr wide)
    (show 0 < B.c+500/543 by linarith only [bc])
  nlinarith only [B.unit_normal,square,positiveSquare]

/-- The same actual right cap and the newly available upper-left marker
rule out separation along B's U axis after the proved left-wall support
bound. The L-axis alternative remains a separate mathematical obligation. -/
theorem no_longitudinal_gap (c s a support : ℝ)
    (hc : 0 < c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (ha : 1 < a) (height : a ≤ s+c/2)
    (leftSupport : c+(283/100)*s ≤ support)
    (rightCap : support+a ≤ (1043/500)*c+3*s) : False := by
  have steep : 3*c/4 < s := by
    apply lt_of_not_ge
    intro shallow
    have product := mul_nonneg hc.le
      (show 0 ≤ 3*c/4-s by linarith only [shallow])
    have above : 1 < s+c/2 := lt_of_lt_of_le ha height
    nlinarith only [unit,product,above,sq_nonneg (s+c/2-1)]
  have square := mul_pos (sub_pos.mpr steep)
    (show 0 < s+3*c/4 by linarith only [hc,hs])
  have cBound : c ≤ 4/5 := by
    nlinarith only [unit,square,sq_nonneg (c-4/5)]
  have sumBound : c+s ≤ 10/7 := by
    nlinarith only [unit,sq_nonneg (c-s),sq_nonneg (c+s-10/7)]
  linarith only [ha,leftSupport,rightCap,cBound,sumBound]

/-- A genuine B/L contradiction with the new top-left marker and the
weaker right cap supplied by the actual C point (2.086,3). This closes the
positive-B / above-U-C sector once that C point is bound geometrically.
The other C sector and the negative-B sectors are not asserted here. -/
theorem impossible_with_right_cap (B L : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < B.side) (same : B.side = L.side)
    (boxL : InsideContainer L)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (lower : -2*B.s+(5/2)*B.c ≤ B.loV)
    (rightCap : B.loU+B.side ≤ (1043/500)*B.c+3*B.s)
    (cornerMissing : ¬ B.Inside 1 3)
    (left : ClosedInside L (457/500) 2)
    (lTop : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) : False := by
  have haL : 1 < L.side := by simpa only [same] using ha
  have upper : B.loU+B.side ≤ (113/50)*B.c+3*B.s := by
    linarith only [rightCap,bc]
  have lFace := (coupled_faces B L bc bs bsc lc lsc ha haL boxL bottom top
    upper lower left lTop missingLow missingRight apart).2
  obtain mode | ⟨vCap,height,steep⟩ :=
    upper_left_marker_modes B bc bs ha bottom top lower cornerMissing
  · exact not_lower_U_of_right_cap B bc bs ha bottom lower rightCap mode
  have dot := FourSquareBLBridge.dot_nonneg B L bc.le bs bsc lc.le lsc
  have walls := FourSquareBLBridge.left_upper_bounds L lc boxL left lFace
  have axes := BLLongitudinal.two_directed_alternatives B L bc bs bsc lc lsc
    haL bottom top left lTop missingLow missingRight same apart
  rcases axes with bAxis | lAxis
  · have cap := FourSquareBLBridge.right_axis_cap B L bAxis
    have radius : ThreeSquare.supportRadius L B.c B.s = B.side/2*
        ((B.c*L.c+B.s*L.s)+|B.c*L.s-B.s*L.c|) := by
      have cross : -B.c*L.s+B.s*L.c = -(B.c*L.s-B.s*L.c) := by ring
      simp only [ThreeSquare.supportRadius,cross,abs_neg,
        abs_of_nonneg dot,same]
    rw [radius] at cap
    have wall : B.side*(L.c+|L.s|)/2 ≤ centerX L := by
      simpa only [same] using FourSquareBLBridge.left_wall L lc.le boxL
    have low : -L.s*(19/25)+L.c*(187/100) ≤
        -L.s*centerX L+L.c*centerY L-B.side/2 := by
      have identity := (center_coordinates L).2
      rw [← same] at identity
      linarith only [lFace,identity]
    have support := FourSquareLongitudinal.left_support B.side B.c B.s L.c L.s
      (centerX L) (centerY L) ha bc bs bsc lc lsc L.unit_normal wall low
    exact no_longitudinal_gap B.c B.s B.side _ bc bs B.unit_normal ha height
      support (by linarith only [cap,rightCap])
  · have cap := FourSquareBLBridge.left_axis_cap L B lAxis
    rw [FourSquareBLBridge.minimum_projection B L dot] at cap
    have unC := congrArg (fun x : ℝ => L.c*x) B.unit_normal
    have unS := congrArg (fun x : ℝ => L.s*x) B.unit_normal
    dsimp only at unC unS
    have aNonneg : 0 ≤ B.side-1 := le_of_lt (sub_pos.mpr ha)
    apply C849PositiveSupport.l_axis_impossible B.c B.s L.c L.s
      (L.loU+L.side) bc bs bsc lc lsc B.unit_normal L.unit_normal steep
    · intro sign
      have reciprocal : 0 ≤ L.s/L.c := div_nonneg sign lc.le
      have product := mul_nonneg aNonneg
        (show 0 ≤ 1+L.s/L.c by linarith only [reciprocal])
      have wall := walls.1 sign
      rw [← same] at wall
      nlinarith only [product,wall]
    · intro sign
      have wall := walls.2 sign
      rw [← same] at wall
      linarith only [wall,ha]
    · intro cross
      rw [abs_of_nonneg cross] at cap
      have u := mul_le_mul_of_nonneg_left rightCap dot
      have v := mul_le_mul_of_nonneg_left vCap cross
      have radiusNonneg : 0 ≤ B.c*L.c+B.s*L.s+(B.c*L.s-B.s*L.c) := by
        linarith only [dot,cross]
      have product := mul_nonneg aNonneg radiusNonneg
      nlinarith only [cap,u,v,unC,unS,product]
    · intro cross
      rw [abs_of_nonpos cross] at cap
      have u := mul_le_mul_of_nonneg_left rightCap dot
      have v := mul_le_mul_of_nonpos_left lower cross
      have radiusNonneg : 0 ≤ B.c*L.c+B.s*L.s-(B.c*L.s-B.s*L.c) := by
        linarith only [dot,cross]
      have product := mul_nonneg aNonneg radiusNonneg
      nlinarith only [cap,u,v,unC,unS,product]

#print axioms coupled_faces
#print axioms no_longitudinal_gap
#print axioms impossible_with_right_cap
end N12Compact.PositiveBLeftReduction
