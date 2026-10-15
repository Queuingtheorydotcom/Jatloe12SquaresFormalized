import S12.AxisAlgebra
namespace S12
noncomputable section
set_option maxHeartbeats 0

/-- Four quarter-turns cover all vectors; this rotates a vector and its whole
predicate together and does not identify unrelated packing branches. -/
theorem quadrant_cover (P : ℝ → ℝ → Prop)
    (hpos : ∀ x y,0≤x → 0≤y → P x y)
    (hturn : ∀ x y,P y (-x) → P x y) (x y : ℝ) : P x y := by
  by_cases hx : 0≤x
  · by_cases hy : 0≤y
    · exact hpos x y hx hy
    · apply hturn x y
      apply hturn y (-x)
      apply hturn (-x) (-y)
      simpa only [neg_neg] using hpos (-y) x (by linarith) hx
  · by_cases hy : 0≤y
    · exact hturn x y (hpos y (-x) hy (by linarith))
    · apply hturn x y
      apply hturn y (-x)
      exact hpos (-x) (-y) (by linarith) (by linarith)

theorem planeL1_turn (c s x y : ℝ) : planeL1 c s y (-x)=planeL1 c s x y := by
  unfold planeL1
  rw [show c*y+s*(-x)=-s*x+c*y by ring,
    show -s*y+c*(-x)=-(c*x+s*y) by ring,abs_neg,add_comm]

theorem axisOverlap_turn {a b c s dx dy : ℝ} (h : AxisOverlap a b c s dx dy) :
    AxisOverlap a b c s dy (-dx) := by
  refine ⟨h.2.1,by simpa only [abs_neg] using h.1,?_,?_⟩
  · simpa only [show c*dy+s*(-dx)=-s*dx+c*dy by ring] using h.2.2.2
  · simpa only [show -s*dy+c*(-dx)=-(c*dx+s*dy) by ring,abs_neg] using h.2.2.1

def NormalGap (a b c s dx dy nx ny : ℝ) : Prop :=
  nx*dx+ny*dy<a*(|nx|+|ny|)+b*planeL1 c s nx ny

theorem normalGap_turn_iff (a b c s dx dy nx ny : ℝ) :
    NormalGap a b c s dy (-dx) ny (-nx) ↔ NormalGap a b c s dx dy nx ny := by
  unfold NormalGap
  rw [planeL1_turn,abs_neg,show ny*dy+(-nx)*(-dx)=nx*dx+ny*dy by ring,
    show |ny|+|nx|=|nx|+|ny| by ring]

theorem axis_normal_gap (a b c s dx dy nx ny : ℝ)
    (hc : 0≤c) (hs : 0≤s) (hu : c^2+s^2=1)
    (h : AxisOverlap a b c s dx dy) (hn : nx≠0 ∨ ny≠0) :
    NormalGap a b c s dx dy nx ny := by
  have hall : ∀ nx ny,nx≠0 ∨ ny≠0 → ∀ dx dy,
      AxisOverlap a b c s dx dy → NormalGap a b c s dx dy nx ny := by
    apply quadrant_cover
    · intro x y hx hy hn dx dy hh
      have hr := positive_normal_gap a b c s dx dy x y hc hs hu hh hx hy hn
      simpa only [NormalGap,abs_of_nonneg hx,abs_of_nonneg hy] using hr
    · intro x y ih hn dx dy hh
      have hne : y≠0 ∨ -x≠0 := by
        rcases hn with hn|hn
        · exact Or.inr (neg_ne_zero.mpr hn)
        · exact Or.inl hn
      exact (normalGap_turn_iff a b c s dx dy x y).mp (ih hne dy (-dx) (axisOverlap_turn hh))
  exact hall nx ny hn dx dy h

def AxisOverlapAbs (a b c s dx dy : ℝ) : Prop :=
  |dx|<a+b*(|c|+|s|) ∧ |dy|<a+b*(|c|+|s|) ∧
  |c*dx+s*dy|<b+a*(|c|+|s|) ∧ |-s*dx+c*dy|<b+a*(|c|+|s|)

theorem planeL1_frame_turn (c s x y : ℝ) : planeL1 s (-c) x y=planeL1 c s x y := by
  unfold planeL1
  rw [show s*x+(-c)*y=-(-s*x+c*y) by ring,
    show -(-c)*x+s*y=c*x+s*y by ring,abs_neg,add_comm]

theorem axisOverlapAbs_frame_turn {a b c s dx dy : ℝ}
    (h : AxisOverlapAbs a b c s dx dy) : AxisOverlapAbs a b s (-c) dx dy := by
  unfold AxisOverlapAbs at *
  rw [abs_neg,show |s|+|c|=|c|+|s| by ring]
  refine ⟨h.1,h.2.1,?_,?_⟩
  · simpa only [show s*dx+(-c)*dy=-(-s*dx+c*dy) by ring,abs_neg] using h.2.2.2
  · simpa only [show -(-c)*dx+s*dy=c*dx+s*dy by ring] using h.2.2.1

/-- Algebraic completeness of the four square axes, with no sign restriction
on the relative orientation or on the separating normal. -/
theorem four_axes_algebra (a b c s dx dy nx ny : ℝ) (hu : c^2+s^2=1)
    (h : AxisOverlapAbs a b c s dx dy) (hn : nx≠0 ∨ ny≠0) :
    NormalGap a b c s dx dy nx ny := by
  have hall : ∀ c s,c^2+s^2=1 → AxisOverlapAbs a b c s dx dy →
      NormalGap a b c s dx dy nx ny := by
    apply quadrant_cover
    · intro c s hc hs hunit hh
      apply axis_normal_gap a b c s dx dy nx ny hc hs hunit _ hn
      simpa only [AxisOverlapAbs,abs_of_nonneg hc,abs_of_nonneg hs] using hh
    · intro c s ih hunit hh
      have ht := ih (by nlinarith : s^2+(-c)^2=1) (axisOverlapAbs_frame_turn hh)
      simpa only [NormalGap,planeL1_frame_turn] using ht
  exact hall c s hu h

#print axioms four_axes_algebra
end
end S12
