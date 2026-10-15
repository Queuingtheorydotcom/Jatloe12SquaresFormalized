import Compact.Geometry.C977CornerCubic

namespace N12Compact.C977CornerCubic

noncomputable def half (c t : ℝ) : ℝ := (1-t)/c

theorem half_data {c t : ℝ} (h : Normal c t) :
    0 < half c t ∧ half c t ≤ 1 ∧
    c*half c t=1-t ∧ half c t*(1+t)=c ∧
    (1+(half c t)^2)*c=2*half c t ∧
    (1+(half c t)^2)*t=1-(half c t)^2 ∧
    (1+(half c t)^2)*boundary c t=2+half c t-(half c t)^3 := by
  have b := normal_bounds h
  have hc : 0 < c := by linarith only [b.1]
  have ht1 : t < 1 := by
    nlinarith only [h.2.2, sq_pos_of_pos hc, sq_nonneg (t-1)]
  let r := half c t
  have hr : 0 < r := div_pos (by linarith only [ht1]) hc
  have hr1 : r ≤ 1 := (div_le_iff₀ hc).mpr (by linarith only [b.2.2.2.2.1])
  have cr : c*r=1-t := by dsimp [r, half]; field_simp [hc.ne']
  have cr' : r*(1+t)=c := by
    have scale := congrArg (fun x : ℝ => x*(1+t)) cr
    dsimp at scale
    have zero : c*(r*(1+t)-c)=0 := by nlinarith only [scale, h.2.2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left hc.ne')
  have cform : (1+r^2)*c=2*r := by
    have crsq := congrArg (fun x : ℝ => x^2) cr
    dsimp at crsq
    have zero : c*((1+r^2)*c-2*r)=0 := by
      nlinarith only [crsq, cr, h.2.2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left hc.ne')
  have tform : (1+r^2)*t=1-r^2 := by
    have scale := congrArg (fun x : ℝ => x*r) cform
    dsimp at scale
    have identity : (1+r^2)*(1-t)=2*r^2 := by
      calc
        _ = (1+r^2)*(c*r) := by rw [cr]
        _ = 2*r^2 := by nlinarith only [scale]
    nlinarith only [identity]
  have boundform : (1+r^2)*boundary c t=2+r-r^3 := by
    have value : boundary c t=1+t+t*r := by dsimp [boundary, r, half]; ring
    rw [value]
    calc
      _ = (1+r^2)+(1+r^2)*t+r*((1+r^2)*t) := by ring
      _ = _ := by rw [tform]; ring
  exact ⟨hr, hr1, cr, cr', cform, tform, boundform⟩

theorem ordered_normals {c t C T : ℝ} (ho : Normal c t) (ha : Normal C T)
    (delta : 0 ≤ c*T-t*C) : C ≤ c ∧ t ≤ T := by
  have bo := normal_bounds ho
  have ba := normal_bounds ha
  have hc : 0 < c := by linarith only [bo.1]
  have hC : 0 < C := by linarith only [ba.1]
  have hcC : C ≤ c := by
    by_contra no
    have cc := mul_pos (show 0 < C-c by linarith only [no])
      (show 0 < C+c by linarith only [hc, hC])
    have hTt : T < t := by
      by_contra bad
      have tt := mul_nonneg (show 0 ≤ T-t by linarith only [bad])
        (add_nonneg ho.1 ha.1)
      nlinarith only [cc, tt, ho.2.2, ha.2.2]
    have small := mul_lt_mul_of_pos_left hTt hc
    have big := mul_lt_mul_of_pos_right (show c < C by linarith only [no])
      (show 0 < t by linarith only [ha.1, hTt])
    nlinarith only [small, big, delta]
  have htT : t ≤ T := by
    have cc := mul_nonneg (sub_nonneg.mpr hcC)
      (show 0 ≤ c+C by linarith only [hc, hC])
    by_contra no
    have tt := mul_pos (show 0 < t-T by linarith only [no])
      (show 0 < t+T by linarith only [no, ha.1])
    nlinarith only [cc, tt, ho.2.2, ha.2.2]
  exact ⟨hcC, htT⟩

theorem half_order {c t C T : ℝ} (ho : Normal c t) (ha : Normal C T)
    (delta : 0 ≤ c*T-t*C) : half C T ≤ half c t := by
  have ord := ordered_normals ho ha delta
  have ro := half_data ho
  have ra := half_data ha
  have prod := mul_le_mul_of_nonneg_left ord.2 ra.1.le
  have scaled : half C T*(1+t) ≤ half c t*(1+t) := by
    nlinarith only [prod, ro.2.2.2.1, ra.2.2.2.1, ord.1]
  exact (mul_le_mul_right (show 0 < 1+t by linarith only [ho.1])).mp scaled

theorem half_lower {C T : ℝ} (h : Normal C T) : (2/5 : ℝ) ≤ half C T := by
  have b := normal_bounds h
  have hc : 0 < C := by linarith only [b.1]
  apply (le_div_iff₀ hc).mpr
  nlinarith only [h.2.1, b.2.2.2.2.2]

theorem half_lower_small {C T : ℝ} (h : Normal C T) (small : T ≤ 3/5) :
    (1/2 : ℝ) ≤ half C T := by
  have b := normal_bounds h
  have hc : 0 < C := by linarith only [b.1]
  have prod := mul_nonneg (show 0 ≤ 1-T by linarith only [b.2.2.2.1])
    (show 0 ≤ 3-5*T by linarith only [small])
  have bound : C ≤ 2*(1-T) := by
    nlinarith only [prod, h.2.2, b.2.2.2.1, hc]
  exact (le_div_iff₀ hc).mpr (by linarith only [bound])

theorem parallel_boundary {C T : ℝ} (h : Normal C T) :
    2*(C+T)-1 ≤ boundary C T := by
  have b := normal_bounds h
  have hc : 0 < C := by linarith only [b.1]
  have prod := mul_nonneg (show 0 ≤ 1-C by linarith only [b.2.1])
    (show 0 ≤ T-(1-C) by linarith only [b.2.2.2.2.1])
  have formula : C*(boundary C T-(2*(C+T)-1))=(1-C)*(T-(1-C)) := by
    have value : C*boundary C T=C+C*T+T*(1-T) := by
      dsimp [boundary]; field_simp [hc.ne']; ring
    nlinarith only [value, h.2.2]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right
    (by nlinarith only [formula, prod]) hc)

/-- Convert two cubic endpoint comparisons and the chord-factor sign
into an inequality on the original unit normal. -/
theorem compare_from_cubic {c t C T f g : ℝ}
    (ho : Normal c t) (ha : Normal C T) (hT : 0 < T)
    (delta : 0 ≤ c*T-t*C)
    (cubic : 0 ≤ H f g (half c t)) : c*f+t*g ≤ boundary c t := by
  have data := half_data ho
  have pos : 0 < 1+(half c t)^2 := by nlinarith [sq_nonneg (half c t)]
  have identity : (1+(half c t)^2)*(boundary c t-c*f-t*g)=H f g (half c t) := by
    calc
      _ = (1+(half c t)^2)*boundary c t-
          ((1+(half c t)^2)*c)*f-((1+(half c t)^2)*t)*g := by ring
      _ = _ := by rw [data.2.2.2.2.1, data.2.2.2.2.2.1, data.2.2.2.2.2.2]; unfold H; ring
  have scaled : 0 ≤ (1+(half c t)^2)*(boundary c t-c*f-t*g) := by
    rw [identity]
    exact cubic
  have difference := nonneg_of_mul_nonneg_right scaled pos
  have grouped : 0 ≤ boundary c t-(c*f+t*g) := by
    convert difference using 1 <;> ring
  exact sub_nonneg.mp grouped

theorem endpoint_cubic {C T f g : ℝ} (ha : Normal C T)
    (identity : C*f+T*g=2*(C+T)-1) : 0 ≤ H f g (half C T) := by
  have data := half_data ha
  have bound := parallel_boundary ha
  have gap : 0 ≤ boundary C T-C*f-T*g := by linarith only [identity, bound]
  have product := mul_nonneg (show 0 ≤ 1+(half C T)^2 by nlinarith [sq_nonneg (half C T)]) gap
  have formula : (1+(half C T)^2)*(boundary C T-C*f-T*g)=H f g (half C T) := by
    calc
      _ = (1+(half C T)^2)*boundary C T-
          ((1+(half C T)^2)*C)*f-((1+(half C T)^2)*T)*g := by ring
      _ = _ := by rw [data.2.2.2.2.1, data.2.2.2.2.2.1, data.2.2.2.2.2.2]; unfold H; ring
  rwa [formula] at product

/-- A corner's true tilted face prevents a central square avoiding (2,2)
from staying entirely to the right of x=1. -/
theorem left_projection {c t C T : ℝ}
    (ho : Normal c t) (ha : Normal C T) (hT : 0 < T)
    (delta : 0 ≤ c*T-t*C) :
    c*(2+(T-1)/C-T)+t*(1+C) ≤ boundary c t := by
  have bo := normal_bounds ho
  have ba := normal_bounds ha
  have hc : 0 < C := by linarith only [ba.1]
  have ro := half_data ho
  have ra := half_data ha
  have order := half_order ho ha delta
  have hrho : half C T < 1 := by
    have sum : 1 < C+T := by
      have positive := mul_pos hc hT
      nlinarith only [ha.2.2, positive, ba.2.2.2.2.1]
    apply (div_lt_iff₀ hc).mpr
    linarith only [sum]
  let f := 2+(T-1)/C-T
  let g := 1+C
  have fscale : C*f=2*C+T-1-C*T := by dsimp [f]; field_simp [hc.ne']; ring
  have fle : f ≤ 1 := by
    have prod := mul_nonneg (show 0 ≤ 1-T by linarith only [ba.2.2.2.1])
      (show 0 ≤ 1-C by linarith only [ba.2.1])
    apply (mul_le_mul_left hc).mp
    nlinarith only [prod, fscale]
  have endpoint : C*f+T*g=2*(C+T)-1 := by dsimp [g]; nlinarith only [fscale]
  have factor : 0 ≤ half c t+1+half C T-g := by
    have product : 0 ≤ C*(2*half C T-C) := by
      nlinarith only [ra.2.2.1, ha.2.2, sq_nonneg (1-T)]
    have small := nonneg_of_mul_nonneg_right product hc
    dsimp [g]; linarith only [small, order]
  apply compare_from_cubic ho ha hT delta
  apply cubic_chord f g (half C T) (half c t) hrho order ro.2.1
    (endpoint_cubic ha endpoint) (by dsimp [H]; nlinarith only [fle]) factor

/-- The same actual tilted face forces the central lower-U endpoint past
the near end of the foreign vertical segment. -/
theorem near_projection {c t C T : ℝ}
    (ho : Normal c t) (ha : Normal C T) (hT : 0 < T)
    (delta : 0 ≤ c*T-t*C) :
    c*(2-(22/25)*T^2+C*T-C-T)+
      t*(1+T^2+(22/25)*C*T+C-T) ≤ boundary c t := by
  have ba := normal_bounds ha
  have hc : 0 < C := by linarith only [ba.1]
  have ro := half_data ho
  have ra := half_data ha
  have order := half_order ho ha delta
  have hrho : half C T < 1 := by
    have positive := mul_pos hc hT
    have sum : 1 < C+T := by nlinarith only [ha.2.2, positive, ba.2.2.2.2.1]
    apply (div_lt_iff₀ hc).mpr
    linarith only [sum]
  let f := 2-(22/25)*T^2+C*T-C-T
  let g := 1+T^2+(22/25)*C*T+C-T
  have fle : f ≤ 1 := low_coefficient ha
  have gle : g ≤ 2 := wing_coefficient ha
  have endpoint : C*f+T*g=2*(C+T)-1 := by
    have scale := congrArg (fun x : ℝ => T*x) ha.2.2
    dsimp at scale
    dsimp [f,g]
    nlinarith only [scale, ha.2.2]
  apply compare_from_cubic ho ha hT delta
  by_cases small : T ≤ 3/5
  · have low := half_lower_small ha small
    apply cubic_chord f g (half C T) (half c t) hrho order ro.2.1
      (endpoint_cubic ha endpoint) (by dsimp [H]; nlinarith only [fle])
    linarith only [low, order, gle]
  · have high : (3/5 : ℝ) ≤ T := le_of_lt (lt_of_not_ge small)
    have fhigh : f ≤ 4/5 := high_tilt_coefficient ha high
    have rlow : (2/5 : ℝ) ≤ half c t := le_trans (half_lower ha) order
    have rr := mul_nonneg (show 0 ≤ half c t-2/5 by linarith only [rlow])
      (show 0 ≤ 8/5-half c t by linarith only [ro.2.1])
    have inside : 0 ≤ 1-2*f+2*half c t-(half c t)^2 := by
      have first := mul_nonneg (show (0:ℝ)≤2 by norm_num) (sub_nonneg.mpr fhigh)
      have total : 0 ≤ (1/25)+2*(4/5-f)+
          (half c t-2/5)*(8/5-half c t) :=
        add_nonneg (add_nonneg (by norm_num) first) rr
      convert total using 1 <;> ring
    have product := mul_nonneg ro.1.le inside
    have square : 0 ≤ 1-(half c t)^2 := by
      have prod := mul_nonneg (sub_nonneg.mpr ro.2.1)
        (show 0 ≤ 1+half c t by linarith only [ro.1])
      nlinarith only [prod]
    have correction := mul_nonneg (show 0 ≤ 2-g by linarith only [gle]) square
    have identity : H f g (half c t) =
        half c t*(1-2*f+2*half c t-(half c t)^2)+
          (2-g)*(1-(half c t)^2) := by unfold H; ring
    nlinarith only [identity, product, correction]

end N12Compact.C977CornerCubic
