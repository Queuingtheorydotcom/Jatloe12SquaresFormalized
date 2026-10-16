import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Exact half-angle identities on the canonical quarter circle. -/
namespace N12Compact.C981CompletionHalfAngle

set_option Elab.async false

noncomputable def half (c s : ℝ) : ℝ := s/(1+c)

theorem data (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) :
    0 ≤ half c s ∧ half c s ≤ 1/2 ∧ half c s*(1+c)=s ∧
      (1+(half c s)^2)*c=1-(half c s)^2 ∧
      (1+(half c s)^2)*s=2*half c s := by
  have cp : 0 < 1+c := by linarith only [hc]
  have sone : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  let t := half c s
  have tn : 0 ≤ t := div_nonneg hs cp.le
  have tu : t ≤ 1/2 := (div_le_iff₀ cp).mpr (by linarith only [sone,order])
  have relation : t*(1+c)=s := by dsimp [t,half]; field_simp [cp.ne']
  have relation_sq := congrArg (fun x : ℝ => x^2) relation
  have zero : (1+c)*((1+c)*(1+t^2)-2)=0 := by
    nlinarith only [relation_sq,unit]
  have denominator : (1+c)*(1+t^2)=2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left cp.ne')
  have cform : (1+t^2)*c=1-t^2 := by nlinarith only [denominator]
  have sform : (1+t^2)*s=2*t := by
    calc
      _ = (1+t^2)*(t*(1+c)) := by rw [relation]
      _ = t*((1+c)*(1+t^2)) := by ring
      _ = 2*t := by rw [denominator]; ring
  exact ⟨tn,tu,relation,cform,sform⟩

theorem quarter_lt (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (width : 1 < s+(3/5)*c) : 1/4 < half c s := by
  have d := data c s hc hs order unit
  let t := half c s
  have identity : (1+t^2)*(s+(3/5)*c-1)=(2/5)*(4*t-1)*(1-t) := by
    calc
      _ = (1+t^2)*s+(3/5)*((1+t^2)*c)-(1+t^2) := by ring
      _ = _ := by rw [d.2.2.2.2,d.2.2.2.1]; ring
  have positive : 0 < (1+t^2)*(s+(3/5)*c-1) :=
    mul_pos (by nlinarith only [sq_nonneg t]) (by linarith only [width])
  have last : 0 ≤ 1-t := by dsimp [t]; linarith only [d.2.1]
  have first : 0 < (2/5)*(4*t-1) := pos_of_mul_pos_left (by rwa [identity] at positive) last
  dsimp [t] at first
  linarith only [first]

theorem steep_lt (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (width : 1 < s+(11/25)*c) : 7/18 < half c s := by
  have d := data c s hc hs order unit
  let t := half c s
  have identity : (1+t^2)*(s+(11/25)*c-1)=(2/25)*(18*t-7)*(1-t) := by
    calc
      _ = (1+t^2)*s+(11/25)*((1+t^2)*c)-(1+t^2) := by ring
      _ = _ := by rw [d.2.2.2.2,d.2.2.2.1]; ring
  have positive : 0 < (1+t^2)*(s+(11/25)*c-1) :=
    mul_pos (by nlinarith only [sq_nonneg t]) (by linarith only [width])
  have last : 0 ≤ 1-t := by dsimp [t]; linarith only [d.2.1]
  have first : 0 < (2/25)*(18*t-7) := pos_of_mul_pos_left (by rwa [identity] at positive) last
  dsimp [t] at first
  linarith only [first]

/-- Identity c+γs−1=s(γ(1+c)−s)/(1+c), with a strict sign. -/
theorem short_of_half (c s γ : ℝ) (hc : 0 ≤ c) (hs : 0 < s)
    (unit : c^2+s^2=1) (angle : γ < half c s) : c+γ*s < 1 := by
  have cp : 0 < 1+c := by linarith only [hc]
  have scaled : γ*(1+c) < s := (lt_div_iff₀ cp).mp angle
  have identity : (1+c)*(c+γ*s-1)=s*(γ*(1+c)-s) := by
    linear_combination unit
  have negative := mul_neg_of_pos_of_neg hs (show γ*(1+c)-s < 0 by linarith only [scaled])
  apply lt_of_not_ge
  intro no
  have product := mul_nonneg cp.le (show 0 ≤ c+γ*s-1 by linarith only [no])
  nlinarith only [product,identity,negative]

theorem sine38_short (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) : s+(19/50)*c < 1 := by
  have second : 0 ≤ (1+2*(19/50)-(19/50)^2)*c+
      (1-2*(19/50)-(19/50)^2)*s := by linarith only [hc,hs]
  have product := mul_nonneg (sub_nonneg.mpr order) second
  have identity :
      (69/50)^2*(c^2+s^2)-2*((19/50)*c+s)^2 =
        (c-s)*((1+2*(19/50)-(19/50)^2)*c+(1-2*(19/50)-(19/50)^2)*s) := by ring
  rw [unit] at identity
  by_contra no
  have square := mul_nonneg (show 0 ≤ (19/50)*c+s-1 by linarith only [no])
    (show 0 ≤ (19/50)*c+s+1 by linarith only [hc,hs])
  nlinarith only [identity,product,square]

end N12Compact.C981CompletionHalfAngle
