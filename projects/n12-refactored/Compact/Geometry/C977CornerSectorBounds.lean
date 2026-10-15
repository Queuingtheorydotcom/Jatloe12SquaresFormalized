import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! The two early continuous angle comparisons in the actual corner
coupling. The apparent angular convexity argument is replaced by an exact
chord identity in the sine coordinate. No trigonometry, angle subdivision,
numerical search, or saved pose premise occurs in these inequalities. -/
namespace N12Compact.C977CornerSectorBounds

open C977CornerCubic

theorem dot_le_one {c t C T : ℝ} (h : Normal c t) (H : Normal C T) :
    c*C+t*T ≤ 1 := by
  nlinarith only [h.2.2,H.2.2,sq_nonneg (c-C),sq_nonneg (t-T)]

theorem cosine_order {c t C T : ℝ} (h : Normal c t) (H : Normal C T)
    (order : T ≤ t) : c ≤ C := by
  have b := normal_bounds h
  have B := normal_bounds H
  have squares := mul_nonneg (sub_nonneg.mpr order) (add_nonneg h.1 H.1)
  by_contra no
  have positive := mul_pos (sub_pos.mpr (lt_of_not_ge no))
    (show 0<c+C by linarith only [b.1,B.1])
  nlinarith only [h.2.2,H.2.2,squares,positive]

/-- The cross-product order agrees with the sine order on the canonical
quarter arc. This includes either zero-tilt endpoint. -/
theorem sine_order {c t C T : ℝ} (h : Normal c t) (H : Normal C T)
    (cross : c*T-t*C ≤ 0) : T ≤ t := by
  have b := normal_bounds h
  have B := normal_bounds H
  by_contra no
  have htT : t < T := lt_of_not_ge no
  have hcC : C ≤ c := cosine_order H h htT.le
  have positive := mul_pos (show 0<c by linarith only [b.1]) (sub_pos.mpr htT)
  have nonnegative := mul_nonneg h.1 (sub_nonneg.mpr hcC)
  nlinarith only [positive,nonnegative,cross]

/-- A linear functional increases to the endpoint of a unit-circle arc
whenever its coefficient slope is at least the endpoint slope. The proof
uses only the dot-product bound; no angle parameter is needed. -/
theorem linear_arc_max {c t C T a b : ℝ}
    (h : Normal c t) (H : Normal C T) (order : T ≤ t)
    (ha : 0 ≤ a) (slope : a*t ≤ b*c) :
    a*C+b*T ≤ a*c+b*t := by
  have bounds := normal_bounds h
  have first := mul_nonneg ha (sub_nonneg.mpr (dot_le_one h H))
  have second := mul_nonneg (sub_nonneg.mpr slope) (sub_nonneg.mpr order)
  have identity :
      c*((a*c+b*t)-(a*C+b*T)) =
        a*(1-(c*C+t*T))+(b*c-a*t)*(t-T) := by
    linear_combination a*h.2.2
  have scaled : 0 ≤ c*((a*c+b*t)-(a*C+b*T)) := by
    nlinarith only [identity,first,second]
  have difference := nonneg_of_mul_nonneg_right scaled
    (show 0<c by linarith only [bounds.1])
  linarith only [difference]

theorem boundary_parallel {c t : ℝ} (h : Normal c t) :
    2*(c+t)-1 ≤ boundary c t := by
  have b := normal_bounds h
  have hc : 0<c := by linarith only [b.1]
  have product := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤t-(1-c) by linarith only [b.2.2.2.2.1])
  have multiply : c*boundary c t=c+c*t+t*(1-t) := by
    unfold boundary
    field_simp [ne_of_gt hc]
    <;> ring
  have scaled : 0 ≤ c*(boundary c t-(2*(c+t)-1)) := by
    nlinarith only [multiply,h.2.2,product]
  have difference := nonneg_of_mul_nonneg_right scaled hc
  linarith only [difference]

theorem boundary_horizontal {c t : ℝ} (h : Normal c t) :
    c+(87/50)*t ≤ boundary c t := by
  have b := normal_bounds h
  have hc : 0<c := by linarith only [b.1]
  have product := mul_nonneg
    (show 0≤c+t-1 by linarith only [b.2.2.2.2.1])
    (show 0≤10/7-(c+t) by linarith only [b.2.2.2.2.2])
  have ct := mul_nonneg hc.le h.1
  have margin : 0 ≤ c+t-1-(37/50)*c*t := by
    nlinarith only [product,ct,h.2.2]
  have multiply : c*boundary c t=c+c*t+t*(1-t) := by
    unfold boundary
    field_simp [ne_of_gt hc]
    <;> ring
  have scaled : 0 ≤ c*(boundary c t-(c+(87/50)*t)) := by
    nlinarith only [multiply,h.2.2,margin]
  have difference := nonneg_of_mul_nonneg_right scaled hc
  linarith only [difference]

/-- The exact sine-coordinate chord inequality. Its nonnegative remainder
is `c*(t*(C-1)+T*(1-c)) + k*t*T*(1-dot)`. -/
theorem arc_chord {c t C T k : ℝ} (h : Normal c t) (H : Normal C T)
    (order : T ≤ t) (hk : 0 ≤ k) :
    (t-T)*c+T*(1-k*t) ≤ t*((1-k*T)*(c*C+t*T)) := by
  have b := normal_bounds h
  have B := normal_bounds H
  have hc : 0<c := by linarith only [b.1]
  have hC : 0<C := by linarith only [B.1]
  have cosOrder := cosine_order h H order
  have dc : 0<1+c := by linarith only [hc]
  have dC : 0<1+C := by linarith only [hC]
  have fraction : T/(1+C) ≤ t/(1+c) := by
    apply (div_le_div_iff₀ dC dc).mpr
    have first := mul_nonneg (sub_nonneg.mpr order) dC.le
    have second := mul_nonneg H.1 (sub_nonneg.mpr cosOrder)
    nlinarith only [first,second]
  have small : 1-c=t^2/(1+c) :=
    (eq_div_iff (ne_of_gt dc)).mpr (by nlinarith only [h.2.2])
  have large : 1-C=T^2/(1+C) :=
    (eq_div_iff (ne_of_gt dC)).mpr (by nlinarith only [H.2.2])
  have bracketIdentity :
      t*(C-1)+T*(1-c)=t*T*(t/(1+c)-T/(1+C)) := by
    calc
      _ = -t*(1-C)+T*(1-c) := by ring
      _ = _ := by rw [small,large]; ring
  have bracket : 0≤t*(C-1)+T*(1-c) := by
    rw [bracketIdentity]
    exact mul_nonneg (mul_nonneg h.1 H.1) (sub_nonneg.mpr fraction)
  have first := mul_nonneg hc.le bracket
  have second := mul_nonneg (mul_nonneg (mul_nonneg hk h.1) H.1)
    (sub_nonneg.mpr (dot_le_one h H))
  have identity :
      t*((1-k*T)*(c*C+t*T))-((t-T)*c+T*(1-k*t)) =
        c*(t*(C-1)+T*(1-c))+k*t*T*(1-(c*C+t*T)) := by
    linear_combination T*h.2.2
  nlinarith only [identity,first,second]

/-- The O-axis separating bound in the nonpositive relative-angle sector.
This is the complete comparison formerly obtained from angular convexity. -/
theorem o_axis_below {c t C T : ℝ} (h : Normal c t) (H : Normal C T)
    (order : T ≤ t) :
    c*(2+(13/50)*C*T-C)+t*(87/50+(13/50)*T^2-T) ≤ boundary c t := by
  by_cases zero : t=0
  · have Tzero : T=0 := by linarith only [order,H.1,zero]
    have b := normal_bounds h
    have B := normal_bounds H
    have cone : c=1 := by nlinarith only [h.2.2,zero,b.1]
    have Cone : C=1 := by nlinarith only [H.2.2,Tzero,B.1]
    norm_num [zero,Tzero,cone,Cone,boundary]
  have positive : 0<t := lt_of_le_of_ne h.1 (Ne.symm zero)
  have chord := arc_chord h H order (show (0:ℝ)≤13/50 by norm_num)
  have first := mul_nonneg (sub_nonneg.mpr order)
    (sub_nonneg.mpr (boundary_horizontal h))
  have second := mul_nonneg H.1 (sub_nonneg.mpr (boundary_parallel h))
  have scaled : 0 ≤ t*(boundary c t-
      (c*(2+(13/50)*C*T-C)+t*(87/50+(13/50)*T^2-T))) := by
    nlinarith only [chord,first,second]
  have difference := nonneg_of_mul_nonneg_right scaled positive
  linarith only [difference]

/-- The A-axis comparison when the central tilt is no larger than the
corner tilt. Its endpoint maximum is a linear-arc inequality. -/
theorem a_axis_below {c t C T : ℝ} (h : Normal c t) (H : Normal C T)
    (order : T ≤ t) :
    2*(C+T) ≤ (T/c)*(c-t)+(c*C+t*T)*(1+t/c)+1 := by
  have bounds := normal_bounds h
  have hc : 0<c := by linarith only [bounds.1]
  let a := 2-c-t
  let b := (1-t)*(c+t)/c
  have ha : 0≤a := by dsimp [a]; linarith only [bounds.2.2.2.2.2]
  have bmul : b*c=(1-t)*(c+t) := by
    dsimp [b]; exact div_mul_cancel₀ _ (ne_of_gt hc)
  have slope : a*t≤b*c := by
    dsimp [a]
    nlinarith only [bmul,h.2.1]
  have arc := linear_arc_max h H order ha slope
  have remainder := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤t-(1-c) by linarith only [bounds.2.2.2.2.1])
  have endpoint : a*c+b*t≤1 := by
    have identity : c*(1-(a*c+b*t))=(1-c)*(t-(1-c)) := by
      dsimp [a]
      calc
        _ = c-(2-c-t)*c^2-(b*c)*t := by ring
        _ = _ := by
          rw [bmul]
          linear_combination (c+t-1)*h.2.2
    have scaled : 0≤c*(1-(a*c+b*t)) := by rw [identity]; exact remainder
    have difference := nonneg_of_mul_nonneg_right scaled hc
    linarith only [difference]
  have identity :
      (T/c)*(c-t)+(c*C+t*T)*(1+t/c)+1-2*(C+T)=1-(a*C+b*T) := by
    dsimp [a,b]
    field_simp [ne_of_gt hc]
    <;> ring
  have below : a*C+b*T ≤ 1 := arc.trans endpoint
  have nonnegative : 0 ≤ (T/c)*(c-t)+(c*C+t*T)*(1+t/c)+1-2*(C+T) := by
    rw [identity]
    exact sub_nonneg.mpr below
  exact sub_nonneg.mp nonnegative

/-- The A-axis comparison in the opposite relative-angle sector. -/
theorem a_axis_above {c t C T : ℝ} (h : Normal c t) (H : Normal C T)
    (order : t ≤ T) :
    2*(C+T) ≤ (T/c)*(c-t+1)+(c*C+t*T)+1 := by
  have b := normal_bounds h
  have B := normal_bounds H
  have hc : 0<c := by linarith only [b.1]
  have cosOrder := cosine_order H h order
  have quotient : 0≤T*(1-t)/c :=
    div_nonneg (mul_nonneg H.1 (sub_nonneg.mpr b.2.2.2.1)) hc.le
  have factor : C-T*(1-t)/c≤1 := by linarith only [quotient,B.2.1]
  have product := mul_nonneg (sub_nonneg.mpr b.2.1) (sub_nonneg.mpr factor)
  have difference : 0≤(1-C)-(1-c)*(C-T*(1-t)/c) := by
    nlinarith only [product,cosOrder]
  have identity :
      (T/c)*(c-t+1)+(c*C+t*T)+1-2*(C+T)=
        (1-C)-(1-c)*(C-T*(1-t)/c) := by
    field_simp [ne_of_gt hc]
    <;> ring
  linarith only [identity,difference]

end N12Compact.C977CornerSectorBounds
