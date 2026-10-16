import Compact.Geometry.ClosedFrames
import S12.TransformFacts

/-! Two genuine foreign auxiliary points force outward reach by a corner
owner. The argument uses its complete side length and container support;
two corner markers alone do not imply these points. -/
namespace N12Compact.CornerBudgetReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem normal_margin (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) : 1+(4/5)*c*s ≤ c+s := by
  have low : 1 ≤ c+s := by
    nlinarith only [unit,mul_nonneg hc hs,hc,hs,sq_nonneg (c+s-1)]
  have high : c+s ≤ 3/2 := by
    nlinarith only [unit,sq_nonneg (c-s),sq_nonneg (c+s-3/2)]
  have product := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ (3/5)-(2/5)*(c+s) by linarith only [high])
  nlinarith only [product,unit]

private theorem positive (E : OpenSquare) (side : 1 < E.side)
    (hc : 0 < E.c) (hs : 0 ≤ E.s)
    (wall : ∀ x y, E.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (P : E.Inside 1 (457/500)) (Q : E.Inside (457/500) 1)
    (right : ¬ E.Inside (8/5) 1)
    (above : ¬ E.Inside 1 (8/5)) : E.Inside (4/5) 1 := by
  have cu : E.c ≤ 1 := by nlinarith only [E.unit_normal,sq_nonneg E.s,hc]
  have su : E.s ≤ 1 := by nlinarith only [E.unit_normal,sq_nonneg E.c,hs]
  have upperU : (4/5)*E.c+E.s < E.loU+E.side := by
    linarith only [Q.2.1,hc]
  have lowerV : E.loV < E.c-(4/5)*E.s := by
    linarith only [Q.2.2.1,hs]
  have rightFaces : E.loU+E.side ≤ (8/5)*E.c+E.s ∨
      E.c-(8/5)*E.s ≤ E.loV := by
    by_cases cap : E.loU+E.side ≤ (8/5)*E.c+E.s
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro low
      apply right
      exact ⟨by linarith only [Q.1,hc],by linarith only [cap],by linarith only [low],
        by linarith only [Q.2.2.2,hs]⟩
  rcases rightFaces with cap | low
  · have lowerU : E.loU < (4/5)*E.c+E.s := by
      linarith only [cap,side,cu]
    refine ⟨by linarith only [lowerU],by linarith only [upperU],by linarith only [lowerV],?_⟩
    apply lt_of_not_ge
    intro high
    have wallY := (positive_frame_wall_bounds E hc.le hs wall).2
    dsimp [centerY] at wallY
    have wallFace : 0 ≤ E.s*E.loU+E.c*E.loV := by
      nlinarith only [wallY]
    have along := mul_nonneg hs (sub_nonneg.mpr cap)
    have across := mul_nonneg hc.le (sub_nonneg.mpr high)
    have margin := normal_margin E.c E.s hc.le hs E.unit_normal
    have excess := mul_pos (sub_pos.mpr side)
      (show 0 < E.c+E.s by linarith only [hc,hs])
    nlinarith only [wallFace,along,across,margin,excess,E.unit_normal]
  · have cap : E.loU+E.side ≤ E.c+(8/5)*E.s := by
      apply le_of_not_gt
      intro high
      have sum : E.c+E.s ≤ 3/2 := by
        nlinarith only [E.unit_normal,sq_nonneg (E.c-E.s),
          sq_nonneg (E.c+E.s-3/2)]
      apply above
      refine ⟨?_,by linarith only [high],?_,?_⟩
      · linarith only [P.1,hs]
      · linarith only [P.2.2.1,hc]
      · linarith only [low,side,sum]
    refine ⟨?_,by linarith only [upperU],by linarith only [lowerV],?_⟩
    · linarith only [cap,side,cu,su]
    · linarith only [low,side,su]

/-- All orientations. Both excluded points must be supplied by actual
ownership or an original auxiliary budget. -/
theorem first_quadrant (E : OpenSquare) (side : 1 < E.side)
    (wall : ∀ x y, E.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (P : E.Inside 1 (457/500)) (Q : E.Inside (457/500) 1)
    (right : ¬ E.Inside (8/5) 1)
    (above : ¬ E.Inside 1 (8/5)) : E.Inside (4/5) 1 := by
  obtain ⟨A,hc,hs,same,inside,_⟩ := ClosedFrames.positive_frame E
  exact (inside _ _).mp (positive A (by simpa only [same] using side) hc hs
    (fun x y h => wall x y ((inside x y).mp h))
    ((inside _ _).mpr P) ((inside _ _).mpr Q)
    (fun h => right ((inside _ _).mp h))
    (fun h => above ((inside _ _).mp h)))

/-- The upper-left corner reaches leftwards at height three. In the
merged-left families, the top wall owns the right excluded point and the
left wall owns the lower excluded point. -/
theorem upper_left (E : OpenSquare) (side : 1 < E.side)
    (box : InsideContainer E)
    (P : E.Inside 1 (1543/500)) (Q : E.Inside (457/500) 3)
    (right : ¬ E.Inside (8/5) 3)
    (below : ¬ E.Inside 1 (12/5)) : E.Inside (4/5) 3 := by
  have walls := container_pullY E box
  have point := first_quadrant (pullY E) side
    (fun x y h => ⟨(walls x y h).1,(walls x y h).2.2.1⟩)
    ((inside_pullY E _ _).mpr (by convert P using 1; norm_num))
    ((inside_pullY E _ _).mpr (by convert Q using 1; norm_num))
    (fun h => right (by convert (inside_pullY E _ _).mp h using 1; norm_num))
    (fun h => below (by convert (inside_pullY E _ _).mp h using 1; norm_num))
  convert (inside_pullY E _ _).mp point using 1; norm_num

#print axioms first_quadrant
#print axioms upper_left
end N12Compact.CornerBudgetReach
