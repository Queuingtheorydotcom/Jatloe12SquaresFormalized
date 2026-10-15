import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace S12

structure Quadratic where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq

def Quadratic.evalRat (q : Quadratic) (t : ℚ) : ℚ := q.a*t^2+q.b*t+q.c
noncomputable def Quadratic.eval (q : Quadratic) (t : ℝ) : ℝ := q.a*t^2+q.b*t+q.c

def Quadratic.CheckOn (q : Quadratic) (l h : ℚ) : Prop :=
  l<h ∧ 0≤q.evalRat l ∧ 0≤q.evalRat l+(h-l)*(2*q.a*l+q.b)/2 ∧ 0≤q.evalRat h
instance Quadratic.decidableCheckOn (q : Quadratic) (l h : ℚ) : Decidable (q.CheckOn l h) := inferInstanceAs (Decidable (_ ∧ _))

/-- Degree-two Bernstein positivity, with the interval and all coefficient
signs checked exactly. The identity and its implication are kernel proofs. -/
theorem Quadratic.sound (q : Quadratic) (l h : ℚ) (hq : q.CheckOn l h)
    (t : ℝ) (ht0 : (l:ℝ)≤t) (ht1 : t≤(h:ℝ)) : 0≤q.eval t := by
  dsimp [Quadratic.CheckOn,Quadratic.evalRat] at hq
  have hlt : (l:ℝ)<h := by exact_mod_cast hq.1
  have h0 : 0≤q.eval l := by dsimp [Quadratic.eval]; exact_mod_cast hq.2.1
  have h1 : 0≤q.eval l+((h:ℝ)-l)*(2*q.a*l+q.b)/2 := by dsimp [Quadratic.eval]; exact_mod_cast hq.2.2.1
  have h2 : 0≤q.eval h := by dsimp [Quadratic.eval]; exact_mod_cast hq.2.2.2
  have hid : ((h:ℝ)-l)^2*q.eval t =
      q.eval l*((h:ℝ)-t)^2+
      2*(q.eval l+((h:ℝ)-l)*(2*q.a*l+q.b)/2)*(t-l)*((h:ℝ)-t)+
      q.eval h*(t-l)^2 := by dsimp [Quadratic.eval]; ring
  have hn0 := mul_nonneg h0 (sq_nonneg ((h:ℝ)-t))
  have hn1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) h1)
    (sub_nonneg.mpr ht0)) (sub_nonneg.mpr ht1)
  have hn2 := mul_nonneg h2 (sq_nonneg (t-(l:ℝ)))
  have hcoef : 0<((h:ℝ)-l)^2 := sq_pos_of_pos (sub_pos.mpr hlt)
  have hprod : 0≤((h:ℝ)-l)^2*q.eval t := by rw [hid]; linarith only [hn0,hn1,hn2]
  exact (mul_nonneg_iff_of_pos_left hcoef).mp hprod

#print axioms Quadratic.sound
end S12
