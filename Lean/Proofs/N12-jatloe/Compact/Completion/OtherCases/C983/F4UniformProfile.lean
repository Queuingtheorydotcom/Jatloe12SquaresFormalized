import Compact.Completion.OtherCases.C983.F4NortheastTransfer
import Compact.Completion.OtherCases.C983.F4SoutheastSign
import Compact.Completion.OtherCases.C983.F4BarAngle

/-! One actual southeast profile for both northeast components. The two
different sharp points keep their literal coordinates. The existing
whole-bar theorem supplies a common half-angle bound, sufficient for both
midpoint arguments; the stronger top-only bound is unnecessary here. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_uniform_negative_bounds (E : OpenSquare) (t alpha beta : ℝ)
    (signed : E.s= -t) (side : 1<E.side) (cp : 0<E.c) (tp : 0<t) (order : t≤E.c)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-13/50)) (missingF : ¬E.Inside 0 (-13/50))
    (missingK : ¬E.Inside alpha beta) (missingRight : ¬E.Inside 1 0)
    (bar : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (parameters : (alpha=21/40 ∧ beta=1/8) ∨ (alpha=21/50 ∧ beta=4/25)) :
    F4BottomMidpoint.SoutheastData E t ∧ t/(1+E.c)<3/20 ∧ (13/50)*t≤E.loU := by
  have bounds := F4BarAngle.bounds E t alpha beta signed side cp tp.le order
    marker elbow outer missingF missingK bar parameters
  have unit : E.c^2+t^2=1 := by simpa only [signed,neg_sq] using E.unit_normal
  have cu : E.c≤1 := by nlinarith only [unit,sq_nonneg t,cp]
  have angle := (div_lt_iff₀ (show 0<1+E.c by linarith only [cp])).mp bounds.2.2.2
  have small : t<3/10 := by linarith only [angle,cu]
  have square := mul_pos (show 0<3/10-t by linarith only [small])
    (show 0<3/10+t by linarith only [tp])
  have cosine : 19/20<E.c := by
    apply lt_of_not_ge
    intro low
    have product := mul_nonneg (show 0≤19/20-E.c by linarith only [low])
      (show 0≤19/20+E.c by linarith only [cp])
    nlinarith only [unit,square,product]
  have d := elbow
  have a := outer
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,
    mul_one,add_zero] at d a
  have upperV : E.loV+E.side≤t := by
    apply le_of_not_gt
    intro high
    apply missingRight
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one,mul_zero,
      add_zero]
    refine ⟨?_,?_,?_,high⟩ <;> linarith only [d.1,a.2.1,a.2.2.1,cp,tp]
  exact ⟨⟨signed,side,cosine,tp,small,upperV,marker,elbow,outer⟩,
    bounds.2.2.2,bounds.1⟩

/-- All profile premises are derived from the same actual owners. A
canonical frame only reindexes Q5; the merged Q7 is never split. -/
theorem f4_southeast_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    ∃ E : OpenSquare,∃ t : ℝ,E.side=(owners p 5).side ∧
      (∀ x y,E.Inside x y↔(owners p 5).Inside (x+2) (y+2)) ∧
      F4BottomMidpoint.SoutheastData E t ∧ t/(1+E.c)<3/20 ∧
        (13/50)*t≤E.loU := by
  let W := (owners p 7).translated 2 2
  let S := (owners p 5).translated 2 2
  have southwest : (owners p 7).Inside (33/20) (33/20) := by
    convert seed_inside p hf 7 (33/20,33/20) (by decide +kernel) using 1 <;> norm_num
  have northwest : (owners p 7).Inside (33/20) (47/20) := by
    convert seed_inside p hf 7 (33/20,47/20) (by decide +kernel) using 1 <;> norm_num
  have inward : (owners p 7).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 7 4 (by decide +kernel) f4
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    convert seed_inside p hf 5 (47/20,33/20) (by decide +kernel) using 1 <;> norm_num
  have elbow : (owners p 5).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 5 16 (by decide +kernel)
      (f4_southeast_g6 p hf f4)
  have outer : (owners p 5).Inside 3 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 5 8 (by decide +kernel)
      (f4_southeast p hf f4)
  have right : ¬(owners p 5).Inside 3 2 := fun own =>
    owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨own,f4_right_origin p hf f4⟩
  have missingF : ¬(owners p 5).Inside 2 (87/50) := fun own =>
    owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨own,inward⟩
  obtain ⟨E,t,shape,physical,cp,signed,tp,order⟩ :=
    F4SoutheastSign.exists_negative W S (owners_side p 5) (owners_same_side p 7 5)
      (by dsimp only [W]; norm_num [inside_translated_iff]; exact southwest)
      (by dsimp only [W]; norm_num [inside_translated_iff]; exact northwest)
      (by dsimp only [W]; norm_num [inside_translated_iff]; exact inward)
      (by dsimp only [W]; norm_num [inside_translated_iff]; exact f4_merged_center p hf f4)
      (by dsimp only [S]; norm_num [inside_translated_iff]; exact marker)
      (by dsimp only [S]; norm_num [inside_translated_iff]; exact elbow)
      (by dsimp only [S]; norm_num [inside_translated_iff]; exact outer)
      (by dsimp only [S]; norm_num [inside_translated_iff]; exact right)
      (by dsimp only [S]; norm_num [inside_translated_iff]; exact missingF)
      (by
        intro x y both
        exact owners_apart p hf 7 5 (by decide +kernel) (2+x) (2+y)
          ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
            (inside_translated_iff _ _ _ _ _).mp both.2⟩)
  have transport (x y : ℝ) : E.Inside x y↔(owners p 5).Inside (2+x) (2+y) := by
    rw [physical]
    exact inside_translated_iff _ _ _ _ _
  have profile (alpha beta : ℝ)
      (parameters : (alpha=21/40 ∧ beta=1/8) ∨ (alpha=21/50 ∧ beta=4/25))
      (foreign : (owners p 6).Inside (2+alpha) (2+beta)) :
      F4BottomMidpoint.SoutheastData E t ∧ t/(1+E.c)<3/20 ∧
        (13/50)*t≤E.loU := by
    apply f4_uniform_negative_bounds E t alpha beta signed
      (by simpa only [shape,S,OpenSquare.translated] using owners_side p 5) cp tp order
    · apply (transport _ _).mpr; norm_num; exact marker
    · apply (transport _ _).mpr; norm_num; exact elbow
    · apply (transport _ _).mpr; norm_num; exact outer
    · intro own; apply missingF; convert (transport _ _).mp own using 1 <;> norm_num
    · intro own
      exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨(transport _ _).mp own,foreign⟩
    · intro own; apply right; convert (transport _ _).mp own using 1 <;> norm_num
    · intro x low high own
      have actual := (transport _ _).mp own
      norm_num at actual
      exact owners_apart p hf 5 9 (by decide +kernel) _ _
        ⟨actual,bottom_bar p hf (2+x) (by linarith only [low]) (by linarith only [high])⟩
    · exact parameters
  refine ⟨E,t,shape,?_,?_⟩
  · intro x y
    simpa only [add_comm] using transport x y
  · rcases f4_northeast_sharp p hf f4 with first | second
    · exact profile (21/40) (1/8) (Or.inl ⟨rfl,rfl⟩)
        (by convert first using 1 <;> norm_num)
    · exact profile (21/50) (4/25) (Or.inr ⟨rfl,rfl⟩)
        (by convert second using 1 <;> norm_num)

end
#print axioms f4_uniform_negative_bounds
#print axioms f4_southeast_profile
end N12Compact.Completion.OtherCases.C983
