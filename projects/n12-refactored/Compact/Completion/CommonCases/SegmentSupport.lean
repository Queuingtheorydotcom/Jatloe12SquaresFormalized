import Compact.Geometry.SegmentCorner
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact support consequences for a segment avoiding an open rectangle.
The support inequality is derived from an explicit interior crossing witness;
no separating-axis hypothesis or positive distance from the segment is used. -/
namespace N12Compact.CommonCases.SegmentSupport
set_option Elab.async false

private theorem endpoint_exits (lU hU lV hV u v : ℝ)
    (outside : ¬ (lU < u ∧ u < hU ∧ lV < v ∧ v < hV)) :
    u ≤ lU ∨ hU ≤ u ∨ v ≤ lV ∨ hV ≤ v := by
  simpa only [not_and_or, not_lt] using outside

/-- The equality threshold between the two signed slope alternatives. -/
theorem vertical (lU hU lV hV u0 v0 u1 v1 : ℝ)
    (origin : lU < 0 ∧ 0 < hU ∧ lV < 0 ∧ 0 < hV)
    (sameU : u1 = u0) (u0neg : u0 < 0)
    (v0neg : v0 < 0) (v1pos : 0 < v1)
    (avoid : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ¬ (lU < (1-t)*u0+t*u1 ∧ (1-t)*u0+t*u1 < hU ∧
        lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV)) :
    u0 ≤ lU := by
  have gap : 0 < v1-v0 := by linarith only [v0neg,v1pos]
  let t : ℝ := -v0/(v1-v0)
  have tn : 0 ≤ t := div_nonneg (by linarith only [v0neg]) gap.le
  have tu : t ≤ 1 := (div_le_one gap).mpr (by linarith only [v1pos])
  have hv : (1-t)*v0+t*v1=0 := by
    dsimp [t]
    field_simp [ne_of_gt gap]
    <;> ring
  have hu : (1-t)*u0+t*u1=u0 := by rw [sameU]; ring
  by_contra low
  apply avoid t tn tu
  rw [hu,hv]
  exact ⟨lt_of_not_ge low,u0neg.trans origin.2.1,origin.2.2.1,origin.2.2.2⟩

/-- An increasing segment whose line places the owned origin above it.
Its projection spans are shorter than the rectangle widths. -/
theorem increasing (lU hU lV hV u0 v0 u1 v1 : ℝ)
    (origin : lU < 0 ∧ 0 < hU ∧ lV < 0 ∧ 0 < hV)
    (u0neg : u0 < 0) (v0neg : v0 < 0) (v1pos : 0 < v1)
    (du : 0 < u1-u0) (dv : 0 < v1-v0)
    (shortU : u1-u0 < hU-lU) (shortV : v1-v0 < hV-lV)
    (line : (v1-v0)*u0-(u1-u0)*v0 < 0)
    (avoid : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ¬ (lU < (1-t)*u0+t*u1 ∧ (1-t)*u0+t*u1 < hU ∧
        lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV)) :
    u1 ≤ lU ∨
      (v1-v0)*lU-(u1-u0)*hV ≥ (v1-v0)*u0-(u1-u0)*v0 := by
  have e0 := endpoint_exits lU hU lV hV u0 v0
    (by simpa using avoid 0 (by norm_num) (by norm_num))
  have e1 := endpoint_exits lU hU lV hV u1 v1
    (by simpa using avoid 1 (by norm_num) (by norm_num))
  have first : u0 ≤ lU ∨ v0 ≤ lV := by
    rcases e0 with h | h | h | h
    · exact Or.inl h
    · linarith only [origin.2.1,u0neg,h]
    · exact Or.inr h
    · linarith only [origin.2.2.2,v0neg,h]
  have last : u1 ≤ lU ∨ hU ≤ u1 ∨ hV ≤ v1 := by
    rcases e1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · linarith only [origin.2.2.1,v1pos,h]
    · exact Or.inr (Or.inr h)
  rcases first with firstU | firstV
  · rcases last with lastU | lastU | lastV
    · exact Or.inl lastU
    · linarith only [firstU,lastU,shortU]
    · by_cases low : u1 ≤ lU
      · exact Or.inl low
      · have cross := SegmentCorner.crossing_order lU hU lV hV u0 v0 u1 v1
          firstU (lt_of_not_ge low)
          (by linarith only [firstU,shortU])
          (by linarith only [lastV,shortV])
          (by linarith only [origin.2.2.2,v0neg]) lastV avoid
        right
        nlinarith only [cross]
  · rcases last with lastU | lastU | lastV
    · exact Or.inl lastU
    · have avoid' (t : ℝ) (tn : 0 ≤ t) (tu : t ≤ 1) :
          ¬ (lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV ∧
            lU < (1-t)*u0+t*u1 ∧ (1-t)*u0+t*u1 < hU) := by
        rintro ⟨a,b,c,d⟩
        exact avoid t tn tu ⟨c,d,a,b⟩
      have cross := SegmentCorner.crossing_order lV hV lU hU v0 u0 v1 u1
        firstV (by linarith only [origin.2.2.1,v1pos])
        (by linarith only [firstV,shortV])
        (by linarith only [lastU,shortU])
        (by linarith only [origin.2.1,u0neg]) lastU avoid'
      have upperU := mul_pos dv origin.2.1
      have lowerV := mul_pos du (neg_pos.mpr origin.2.2.1)
      nlinarith only [cross,upperU,lowerV,line]
    · linarith only [firstV,lastV,shortV]

/-- A decreasing segment whose line places the owned origin above it.
This is the other signed orientation; zero slope is handled by `vertical`. -/
theorem decreasing (lU hU lV hV u0 v0 u1 v1 : ℝ)
    (origin : lU < 0 ∧ 0 < hU ∧ lV < 0 ∧ 0 < hV)
    (u1neg : u1 < 0) (v0neg : v0 < 0) (v1pos : 0 < v1)
    (du : 0 < u0-u1) (dv : 0 < v1-v0)
    (shortU : u0-u1 < hU-lU) (shortV : v1-v0 < hV-lV)
    (line : (v1-v0)*u0+(u0-u1)*v0 < 0)
    (avoid : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ¬ (lU < (1-t)*u0+t*u1 ∧ (1-t)*u0+t*u1 < hU ∧
        lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV)) :
    u0 ≤ lU ∨
      (v1-v0)*lU+(u0-u1)*lV ≥ (v1-v0)*u0+(u0-u1)*v0 := by
  have e0 := endpoint_exits lU hU lV hV u0 v0
    (by simpa using avoid 0 (by norm_num) (by norm_num))
  have e1 := endpoint_exits lU hU lV hV u1 v1
    (by simpa using avoid 1 (by norm_num) (by norm_num))
  have first : u0 ≤ lU ∨ hU ≤ u0 ∨ v0 ≤ lV := by
    rcases e0 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · linarith only [origin.2.2.2,v0neg,h]
  have last : u1 ≤ lU ∨ hV ≤ v1 := by
    rcases e1 with h | h | h | h
    · exact Or.inl h
    · linarith only [origin.2.1,u1neg,h]
    · linarith only [origin.2.2.1,v1pos,h]
    · exact Or.inr h
  rcases first with firstU | firstU | firstV
  · exact Or.inl firstU
  · rcases last with lastU | lastV
    · linarith only [firstU,lastU,shortU]
    · have avoid' (t : ℝ) (tn : 0 ≤ t) (tu : t ≤ 1) :
          ¬ (-hV < (1-t)*(-v1)+t*(-v0) ∧
            (1-t)*(-v1)+t*(-v0) < -lV ∧
            lU < (1-t)*u1+t*u0 ∧ (1-t)*u1+t*u0 < hU) := by
        rintro ⟨a,b,c,d⟩
        apply avoid (1-t) (by linarith only [tu]) (by linarith only [tn])
        refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [a,b,c,d]
      have cross := SegmentCorner.crossing_order (-hV) (-lV) lU hU
        (-v1) u1 (-v0) u0
        (by linarith only [lastV])
        (by linarith only [origin.2.2.2,v0neg])
        (by linarith only [lastV,shortV])
        (by linarith only [firstU,shortU])
        (by linarith only [origin.2.1,u1neg]) firstU avoid'
      have upperU := mul_pos dv origin.2.1
      have upperV := mul_pos du origin.2.2.2
      nlinarith only [cross,upperU,upperV,line]
  · rcases last with lastU | lastV
    · by_cases low : u0 ≤ lU
      · exact Or.inl low
      · have avoid' (t : ℝ) (tn : 0 ≤ t) (tu : t ≤ 1) :
          ¬ (lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV ∧
            -hU < (1-t)*(-u0)+t*(-u1) ∧
            (1-t)*(-u0)+t*(-u1) < -lU) := by
          rintro ⟨a,b,c,d⟩
          apply avoid t tn tu
          refine ⟨?_,?_,a,b⟩ <;> nlinarith only [c,d]
        have cross := SegmentCorner.crossing_order lV hV (-hU) (-lU)
          v0 (-u0) v1 (-u1)
          firstV (by linarith only [origin.2.2.1,v1pos])
          (by linarith only [firstV,shortV])
          (by linarith only [lastU,shortU])
          (by linarith only [low])
          (by linarith only [lastU]) avoid'
        right
        nlinarith only [cross]
    · linarith only [firstV,lastV,shortV]

end N12Compact.CommonCases.SegmentSupport
