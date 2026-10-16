import Compact.Geometry.C977CornerHalfAngle
import Compact.Geometry.C977CornerSectorBounds

namespace N12Compact.C977CornerSupportBounds
open C977CornerCubic C977CornerSectorBounds

theorem positive_dot {c t C T : ℝ} (ho : Normal c t) (ha : Normal C T) :
    0 < c*C+t*T := by
  have bo := normal_bounds ho
  have ba := normal_bounds ha
  have first := mul_pos (show 0<c by linarith only [bo.1])
    (show 0<C by linarith only [ba.1])
  have second := mul_nonneg ho.1 ha.1
  linarith only [first, second]

theorem own_axis_above {c t C T u v a : ℝ}
    (ho : Normal c t) (ha : Normal C T) (side : 1<a)
    (corner : c-t ≤ u) (wall : t*(u+a) ≤ c*v)
    (sign : 0 ≤ c*T-t*C) :
    2*(C+T) < (c*T-t*C)*(u+a)+(c*C+t*T)*(v+a)+a := by
  let d := c*T-t*C
  let K := c*C+t*T
  have bo := normal_bounds ho
  have hc : 0<c := by linarith only [bo.1]
  have hK : 0<K := positive_dot ho ha
  have order := (ordered_normals ho ha sign).2
  have scalar := a_axis_above ho ha order
  have weighted := mul_le_mul_of_nonneg_left scalar hc.le
  change c*(2*(C+T)) ≤ c*((T/c)*(c-t+1)+K+1) at weighted
  have dual : c*d+t*K=T := by
    dsimp [d,K]
    linear_combination T*ho.2.2
  have multiply : c*((T/c)*(c-t+1)+K+1)=T*(c-t+1)+c*K+c := by
    field_simp [hc.ne']
  have wallWeight := mul_nonneg hK.le (sub_nonneg.mpr wall)
  have cornerWeight := mul_nonneg ha.1 (sub_nonneg.mpr corner)
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<T+c*K+c by nlinarith only [ha.1, hc, mul_pos hc hK])
  have decompose : c*(d*(u+a)+K*(v+a)+a) =
      K*(c*v-t*(u+a))+T*(u+a)+c*K*a+c*a := by
    calc
      _ = K*(c*v-t*(u+a))+(c*d+t*K)*(u+a)+c*K*a+c*a := by ring
      _ = _ := by rw [dual]
  rw [multiply] at weighted
  have gain : T*(c-t+1)+c*K+c < c*(d*(u+a)+K*(v+a)+a) := by
    apply sub_pos.mp
    rw [decompose]
    convert add_pos_of_nonneg_of_pos (add_nonneg wallWeight cornerWeight) strict using 1 <;> ring
  have result := weighted.trans_lt gain
  exact (mul_lt_mul_iff_right₀ hc).mp result

theorem own_axis_below {c t C T u v a : ℝ}
    (ho : Normal c t) (ha : Normal C T) (side : 1<a)
    (corner : c-t ≤ u) (wall : t*(u+a) ≤ c*v)
    (sign : c*T-t*C ≤ 0) :
    2*(C+T) < (c*T-t*C)*u+(c*C+t*T)*(v+a)+a := by
  let d := c*T-t*C
  let K := c*C+t*T
  have bo := normal_bounds ho
  have hc : 0<c := by linarith only [bo.1]
  have hK : 0<K := positive_dot ho ha
  have scalar := a_axis_below ho ha (sine_order ho ha sign)
  have weighted := mul_le_mul_of_nonneg_left scalar hc.le
  change c*(2*(C+T)) ≤ c*((T/c)*(c-t)+K*(1+t/c)+1) at weighted
  have dual : c*d+t*K=T := by
    dsimp [d,K]
    linear_combination T*ho.2.2
  have multiply : c*((T/c)*(c-t)+K*(1+t/c)+1)=T*(c-t)+K*(c+t)+c := by
    field_simp [hc.ne'] <;> ring
  have wallWeight := mul_nonneg hK.le (sub_nonneg.mpr wall)
  have cornerWeight := mul_nonneg ha.1 (sub_nonneg.mpr corner)
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<K*(c+t)+c by
      have product := mul_pos hK (show 0<c+t by linarith only [hc, ho.1])
      linarith only [product, hc])
  have decompose : c*(d*u+K*(v+a)+a) =
      K*(c*v-t*(u+a))+T*u+K*a*(c+t)+c*a := by
    calc
      _ = K*(c*v-t*(u+a))+(c*d+t*K)*u+K*a*(c+t)+c*a := by ring
      _ = _ := by rw [dual]
  rw [multiply] at weighted
  have gain : T*(c-t)+K*(c+t)+c < c*(d*u+K*(v+a)+a) := by
    apply sub_pos.mp
    rw [decompose]
    convert add_pos_of_nonneg_of_pos (add_nonneg wallWeight cornerWeight) strict using 1 <;> ring
  have result := weighted.trans_lt gain
  exact (mul_lt_mul_iff_right₀ hc).mp result

theorem corner_axis_below {c t C T U V a : ℝ}
    (ho : Normal c t) (ha : Normal C T) (side : 1<a)
    (cross : U ≤ (87/50)*C-2*T) (top : V+a ≤ 2*(C+T))
    (sign : c*T-t*C ≤ 0) :
    -(c*T-t*C)*U+(c*C+t*T)*V < boundary c t := by
  let d := c*T-t*C
  let K := c*C+t*T
  change -d*U+K*V < boundary c t
  have hK : 0<K := positive_dot ho ha
  have scalar := o_axis_below ho ha (sine_order ho ha sign)
  have uWeight := mul_nonneg (show 0 ≤ -d by dsimp [d]; linarith only [sign])
    (sub_nonneg.mpr cross)
  have vWeight := mul_nonneg hK.le (sub_nonneg.mpr top)
  have strict := mul_pos hK (sub_pos.mpr side)
  have identity : -d*((87/50)*C-2*T)+K*(2*(C+T)-1) =
      c*(2+(13/50)*C*T-C)+t*(87/50+(13/50)*T^2-T) := by
    calc
      _ = c*(2+(13/50)*C*T-C)+t*(87/50+(13/50)*T^2-T)+
          (2*c+(87/50)*t)*(C^2+T^2-1) := by dsimp [d,K]; ring
      _ = _ := by rw [ha.2.2]; ring
  have enclosure : -d*U+K*V < -d*((87/50)*C-2*T)+K*(2*(C+T)-1) := by
    apply sub_pos.mp
    convert add_pos_of_nonneg_of_pos (add_nonneg uWeight vWeight) strict using 1 <;> ring
  rw [identity] at enclosure
  exact enclosure.trans_le scalar

theorem remaining_section_bounds {c t C T U V a : ℝ}
    (ho : Normal c t) (ha : Normal C T) (side : 1<a) (tilt : 0<T)
    (top : V+a ≤ 2*(C+T)) (sign : 0<c*T-t*C)
    (separation : boundary c t < -(c*T-t*C)*(U+a)+(c*C+t*T)*V) :
    C*U+T*V < 1 ∧ U < C-(28/25)*T := by
  let d := c*T-t*C
  let K := c*C+t*T
  change boundary c t < -d*(U+a)+K*V at separation
  have bo := normal_bounds ho
  have ba := normal_bounds ha
  have hc : 0<c := by linarith only [bo.1]
  have hC : 0<C := by linarith only [ba.1]
  have hK : 0<K := positive_dot ho ha
  have hd : 0<d := sign
  have dual : C*K+T*d=c := by
    dsimp [d,K]
    linear_combination c*ha.2.2
  have vWeight := mul_nonneg hK.le (sub_nonneg.mpr top)
  constructor
  · by_contra no
    have xmin : 1 ≤ C*U+T*V := le_of_not_gt no
    have pointWeight := mul_nonneg hd.le (sub_nonneg.mpr xmin)
    have topWeight := mul_nonneg hc.le (sub_nonneg.mpr top)
    have scalar := left_projection ho ha tilt sign.le
    have scalarWeight := mul_le_mul_of_nonneg_left scalar hC.le
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<c+C*d by nlinarith only [hc, mul_pos hC hd])
    have sepWeight := mul_lt_mul_of_pos_left separation hC
    have scale : C*(c*(2+(T-1)/C-T)+t*(1+C)) =
        c*(2*(C+T)-1)-d-C*d := by
      dsimp [d]
      field_simp [hC.ne']; ring
    have decompose : C*(-d*(U+a)+K*V) =
        c*V-d-C*d*a-d*(C*U+T*V-1) := by
      calc
        _ = (C*K+T*d)*V-d-C*d*a-d*(C*U+T*V-1) := by ring
        _ = _ := by rw [dual]
    have enclosure : C*(-d*(U+a)+K*V) <
        C*(c*(2+(T-1)/C-T)+t*(1+C)) := by
      apply sub_pos.mp
      rw [scale,decompose]
      convert add_pos_of_nonneg_of_pos (add_nonneg topWeight pointWeight) strict using 1 <;> ring
    exact (not_lt_of_ge scalarWeight) (sepWeight.trans enclosure)
  · apply lt_of_not_ge
    intro near
    have uWeight := mul_nonneg hd.le (sub_nonneg.mpr near)
    have scalar := near_projection ho ha tilt sign.le
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<d+K by linarith only [hd, hK])
    have identity : -d*(C-(28/25)*T+1)+K*(2*(C+T)-1) =
        c*(2-(22/25)*T^2+C*T-C-T)+t*(1+T^2+(22/25)*C*T+C-T) := by
      calc
        _ = c*(2-(22/25)*T^2+C*T-C-T)+t*(1+T^2+(22/25)*C*T+C-T)+
            (2*c+t)*(C^2+T^2-1) := by dsimp [d,K]; ring
        _ = _ := by rw [ha.2.2]; ring
    have enclosure : -d*(U+a)+K*V < -d*(C-(28/25)*T+1)+K*(2*(C+T)-1) := by
      apply sub_pos.mp
      convert add_pos_of_nonneg_of_pos (add_nonneg uWeight vWeight) strict using 1 <;> ring
    rw [identity] at enclosure
    exact (not_lt_of_ge (enclosure.le.trans scalar)) separation

end N12Compact.C977CornerSupportBounds
