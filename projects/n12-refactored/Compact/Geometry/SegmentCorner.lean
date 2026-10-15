import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! A closed segment avoiding an open rectangle must pass outside its corner.
This is a two-dimensional geometric implication, with no numerical search or
enumeration of sample points. The midpoint of the two crossing parameters is
an explicit interior witness if the claimed ordering fails. -/

namespace N12Compact.SegmentCorner

theorem crossing_order (lU hU lV hV u0 v0 u1 v1 : ℝ)
    (hu0 : u0 ≤ lU) (hu1 : lU < u1) (hu2 : u1 < hU)
    (hv0 : lV < v0) (hv1 : v0 < hV) (hv2 : hV ≤ v1)
    (avoid : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ¬ (lU < (1 - t) * u0 + t * u1 ∧
        (1 - t) * u0 + t * u1 < hU ∧
        lV < (1 - t) * v0 + t * v1 ∧
        (1 - t) * v0 + t * v1 < hV)) :
    (hV - v0) * (u1 - u0) ≤ (lU - u0) * (v1 - v0) := by
  by_contra hn
  have hcross := lt_of_not_ge hn
  have hu : 0 < u1 - u0 := by linarith
  have hv : 0 < v1 - v0 := by linarith
  let a := (lU - u0) / (u1 - u0)
  let b := (hV - v0) / (v1 - v0)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hu0) hu.le
  have hb : b ≤ 1 := (div_le_one hv).mpr (by linarith)
  have hab : a < b := (div_lt_div_iff₀ hu hv).mpr hcross
  let t := (a + b) / 2
  have hat : a < t := by dsimp [t]; linarith
  have htb : t < b := by dsimp [t]; linarith
  have ht : 0 < t := lt_of_le_of_lt ha hat
  have ht1 : t < 1 := lt_of_lt_of_le htb hb
  have hul : lU - u0 < t * (u1 - u0) := (div_lt_iff₀ hu).mp hat
  have hvu : t * (v1 - v0) < hV - v0 := (lt_div_iff₀ hv).mp htb
  have huh : 0 < (1 - t) * (u1 - u0) :=
    mul_pos (sub_pos.mpr ht1) hu
  have hvl : 0 < t * (v1 - v0) := mul_pos ht hv
  exact avoid t ht.le ht1.le ⟨by nlinarith, by nlinarith,
    by nlinarith, by nlinarith⟩

#print axioms crossing_order
end N12Compact.SegmentCorner
