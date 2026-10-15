import Compact.Completion.CommonCases.SingletonMissingFan
import S12.PackingEnclosure

/-! The stronger missing-corner singleton seeds, from Appendix A.3 of
05_C580_MATH_DONE__FORMAL_PENDING.  This uses the actual omitted corner and
all actual foreign markers.  It does not import the unavailable historical
SingletonMissingTriangles or MissingCornerCubic modules. -/
namespace N12Compact.CommonCases.SingletonMissing
open S12 S12Pilot
set_option Elab.async false

private theorem wall096_nonnegative (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0≤wallCubic (24/25) (6/25) t := by
  by_cases h : t≤1/6
  · have hu : 0≤1/6-t := sub_nonneg.mpr h
    have identity : wallCubic (24/25) (6/25) t =
        (216/25)*(1/6-t)^3+(36/5)*t*(1/6-t)^2+
          (6/25)*t^2*(1/6-t)+(17/25)*t^3 := by
      dsimp [wallCubic]; ring
    rw [identity]
    positivity
  · have hl : 0≤t-1/6 := by linarith only [h]
    have hu : 0≤1-t := sub_nonneg.mpr ht1
    have identity : wallCubic (24/25) (6/25) t =
        (17/3125)*(1-t)^3+(276/3125)*(t-1/6)*(1-t)^2+
          (5976/3125)*(t-1/6)^2*(1-t)+(2592/3125)*(t-1/6)^3 := by
      dsimp [wallCubic]; ring
    rw [identity]
    positivity

theorem point182 (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 := by
  have hw : ∀ x y,q.Inside x y → 0≤y := fun x y hi => (hbox x y hi).2.2.1
  apply singleton_forcing_template q ha hsize hbox hp hout (91/50) 1 1
  · intro hx0 hx1 hy
    by_cases hx : centerX q≤1
    · exact False.elim (hcorner (corner_nonavoidance_horizontal q ha
        (fun x y hi => ⟨(hbox x y hi).1,(hbox x y hi).2.2.1⟩)
        hx hy 1 (by norm_num) (by norm_num)))
    · exact Or.inr ((bottom_segment_hit q ha hw 1 (91/50) 1
        (by linarith only [hx]) hx1 hy (by norm_num) (by norm_num)).resolve_left hcorner)
  · intro hx0 hx1 hy
    apply general_segment_descending q ha hw (91/50) 2 1 (457/500) hx0 hx1 hy
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    intro c s hc hs hn
    exact normal_bound_small _ _ _ c s (by norm_num) (by norm_num) (by norm_num) hc hs hn
  · intro hx0 hx1 hy0 hy1
    exact replacement182_left q ha hx0 hx1 hy0 hy1 hout hcorner
  · intro hx0 hx1 hy0 hy1
    exact replacement182_right q ha hx0 hx1 hy0 hy1 hout

theorem point196 (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (49/25) (19/25) := by
  have hw : ∀ x y,q.Inside x y → 0≤y := fun x y hi => (hbox x y hi).2.2.1
  apply singleton_forcing_template q ha hsize hbox hp hout (49/25) (19/25) (457/500)
  · intro hx0 hx1 hy
    by_cases hx : centerX q≤1
    · exact False.elim (hcorner (corner_nonavoidance_horizontal q ha
        (fun x y hi => ⟨(hbox x y hi).1,(hbox x y hi).2.2.1⟩)
        hx hy 1 (by norm_num) (by norm_num)))
    · apply Or.inr
      apply Or.resolve_left _ hcorner
      apply general_segment_descending q ha hw 1 (49/25) 1 (19/25)
        (by linarith only [hx]) hx1 hy
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      intro c s hc hs hn
      have h := normal_bound_from_cubic (24/25) (6/25) wall096_nonnegative c s hc hs hn
      nlinarith only [h]
  · intro hx0 hx1 hy
    apply general_segment_hit q ha hw (49/25) 2 (19/25) (457/500) hx0 hx1 hy
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    intro c s hc hs hn
    exact normal_bound_small _ _ _ c s (by norm_num) (by norm_num) (by norm_num) hc hs hn
  · intro hx0 hx1 hy0 hy1
    exact replacement196_left q ha hx0 hx1 hy0 hy1 hout hcorner
  · intro hx0 hx1 hy0 hy1
    exact replacement196_right q ha hx0 hx1 hy0 hy1 hout

/-- The genuine omitted-corner premise forces both stronger singleton seeds. -/
theorem forces (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 ∧ q.Inside (49/25) (19/25) :=
  ⟨point182 q ha hsize hbox hp hout hcorner,
    point196 q ha hsize hbox hp hout hcorner⟩

theorem zero_missing_points (q : OpenSquare) (ha : 1<q.side)
    (hs : q.side≤1001/1000) (hb : InsideContainer q)
    (he : ExactMarkers q {0}) (hm : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 ∧ q.Inside (49/25) (19/25) := by
  apply forces q ha hs hb ((he 0).mpr (by simp))
  · intro i hi hh
    exact hi (Finset.mem_singleton.mp ((he i).mp hh))
  · exact hm

theorem one_missing_points (q : OpenSquare) (ha : 1<q.side)
    (hs : q.side≤1001/1000) (hb : InsideContainer q)
    (he : ExactMarkers q {1}) (hm : ¬q.Inside 1 1) :
    q.Inside 1 (91/50) ∧ q.Inside (19/25) (49/25) := by
  have ht : ExactMarkers (pullSwap q) {0} := by
    intro i
    rw [owns_pullSwap,he]
    fin_cases i <;> decide
  have hmiss : ¬(pullSwap q).Inside 1 1 := by simpa only [inside_pullSwap] using hm
  have hh := zero_missing_points (pullSwap q) ha hs (container_pullSwap q hb) ht hmiss
  simpa only [inside_pullSwap] using hh

#print axioms forces
#print axioms one_missing_points
end N12Compact.CommonCases.SingletonMissing
