import S12.SingletonForcing
import S12.SingletonMissingTriangles
import S12.MissingCornerCubic
namespace S12
open S12Pilot
set_option maxHeartbeats 0

theorem singleton_missing_forces_182 (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 := by
  have hw : ∀ x y,q.Inside x y → 0≤y := fun x y hi => (hbox x y hi).2.2.1
  apply singleton_forcing_template q ha hsize hbox hp hout (91/50) 1 1
  · intro hx0 hx1 hy
    by_cases hx : centerX q≤1
    · exact False.elim (hcorner (corner_nonavoidance_horizontal q ha
        (fun x y hi => ⟨(hbox x y hi).1,(hbox x y hi).2.2.1⟩) hx hy 1 (by norm_num) (by norm_num)))
    · exact Or.inr ((bottom_segment_hit q ha hw 1 (91/50) 1
        (by linarith) hx1 hy (by norm_num) (by norm_num)).resolve_left hcorner)
  · intro hx0 hx1 hy
    apply general_segment_descending q ha hw (91/50) 2 1 (457/500) hx0 hx1 hy
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    intro c s hc hs hn
    exact normal_bound_small _ _ _ c s (by norm_num) (by norm_num) (by norm_num) hc hs hn
  · intro hx0 hx1 hy0 hy1
    exact missingReplacement0_left q ha hx0 hx1 hy0 hy1 hout hcorner
  · intro hx0 hx1 hy0 hy1
    exact missingReplacement0_right q ha hx0 hx1 hy0 hy1 hout hcorner

theorem singleton_missing_forces_196 (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (49/25) (19/25) := by
  have hw : ∀ x y,q.Inside x y → 0≤y := fun x y hi => (hbox x y hi).2.2.1
  apply singleton_forcing_template q ha hsize hbox hp hout (49/25) (19/25) (457/500)
  · intro hx0 hx1 hy
    by_cases hx : centerX q≤1
    · exact False.elim (hcorner (corner_nonavoidance_horizontal q ha
        (fun x y hi => ⟨(hbox x y hi).1,(hbox x y hi).2.2.1⟩) hx hy 1 (by norm_num) (by norm_num)))
    · apply Or.inr
      apply Or.resolve_left _ hcorner
      apply general_segment_descending q ha hw 1 (49/25) 1 (19/25) (by linarith) hx1 hy
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
    exact missingReplacement1_left q ha hx0 hx1 hy0 hy1 hout hcorner
  · intro hx0 hx1 hy0 hy1
    exact missingReplacement1_right q ha hx0 hx1 hy0 hy1 hout hcorner

/-- The two stronger compulsory points used in missing-inner-corner branches. -/
theorem corner_singleton_missing_forces (q : OpenSquare) (ha : 1<q.side)
    (hsize : q.side≤1001/1000) (hbox : InsideContainer q) (hp : Owns q 0)
    (hout : ∀ i : Marker, i≠0 → ¬Owns q i) (hcorner : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 ∧ q.Inside (49/25) (19/25) :=
  ⟨singleton_missing_forces_182 q ha hsize hbox hp hout hcorner,
    singleton_missing_forces_196 q ha hsize hbox hp hout hcorner⟩
#print axioms corner_singleton_missing_forces
end S12
