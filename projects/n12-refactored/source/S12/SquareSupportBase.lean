import S12.ConvexOverlap
import S12.SquareFrame

/-! Elementary square support functions, independent of general separation. -/
namespace S12
noncomputable section
open S12Pilot
set_option maxHeartbeats 0

theorem square_center_inside (q : OpenSquare) : q.Inside (centerX q) (centerY q) := by
  rw [inside_centered_iff]
  simp only [sub_self,mul_zero,add_zero,InBands]
  have h := q.side_pos
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- A bound on every point of a half-open segment also bounds its endpoint. -/
theorem linear_endpoint_le (L d u : ℝ) (h0 : L≤u)
    (h : ∀ t : ℝ,0≤t → t<1 → L+t*d≤u) : L+d≤u := by
  by_contra hn
  have hd : 0<d := by linarith
  let t := (d+u-L)/(2*d)
  have ht0 : 0≤t := div_nonneg (by linarith) (by positivity)
  have ht1 : t<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have he : t*(2*d)=d+u-L := div_mul_cancel₀ _ (by positivity)
  have hh := h t ht0 ht1
  nlinarith

/-- Scaling any displacement in the closed square by t<1 gives an interior point. -/
theorem square_displacement_inside (q : OpenSquare) (dx dy t : ℝ)
    (hu : |q.c*dx+q.s*dy|≤q.side/2)
    (hv : |-q.s*dx+q.c*dy|≤q.side/2)
    (ht0 : 0≤t) (ht1 : t<1) :
    q.Inside (centerX q+t*dx) (centerY q+t*dy) := by
  rw [inside_centered_iff]
  rcases abs_le.mp hu with ⟨hu0,hu1⟩
  rcases abs_le.mp hv with ⟨hv0,hv1⟩
  have hp := q.side_pos
  have hu0t := mul_le_mul_of_nonneg_left hu0 ht0
  have hu1t := mul_le_mul_of_nonneg_left hu1 ht0
  have hv0t := mul_le_mul_of_nonneg_left hv0 ht0
  have hv1t := mul_le_mul_of_nonneg_left hv1 ht0
  have htp : 0<(1-t)*q.side := mul_pos (by linarith) hp
  dsimp [InBands]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem square_closed_linear_bound (q : OpenSquare) (nx ny u dx dy : ℝ)
    (h : ∀ x y,q.Inside x y → nx*x+ny*y≤u)
    (hu : |q.c*dx+q.s*dy|≤q.side/2)
    (hv : |-q.s*dx+q.c*dy|≤q.side/2) :
    nx*centerX q+ny*centerY q+(nx*dx+ny*dy)≤u := by
  apply linear_endpoint_le
  · exact h _ _ (square_center_inside q)
  · intro t ht0 ht1
    have hh := h _ _ (square_displacement_inside q dx dy t hu hv ht0 ht1)
    nlinarith

def signedOne (a : ℝ) : ℝ := if 0≤a then 1 else -1

theorem signedOne_abs (a : ℝ) : |signedOne a|=1 := by
  unfold signedOne
  split <;> norm_num

theorem signedOne_mul (a : ℝ) : a*signedOne a=|a| := by
  unfold signedOne
  split_ifs with h
  · rw [mul_one,abs_of_nonneg h]
  · rw [mul_neg_one,abs_of_neg (lt_of_not_ge h)]

def squareRadius (q : OpenSquare) (nx ny : ℝ) : ℝ :=
  q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|)

/-- Exact support function of an arbitrarily rotated square. -/
theorem square_support_bound (q : OpenSquare) (nx ny u : ℝ)
    (h : ∀ x y,q.Inside x y → nx*x+ny*y≤u) :
    nx*centerX q+ny*centerY q+squareRadius q nx ny≤u := by
  let su := signedOne (nx*q.c+ny*q.s)
  let sv := signedOne (-nx*q.s+ny*q.c)
  let dx := q.side/2*(q.c*su-q.s*sv)
  let dy := q.side/2*(q.s*su+q.c*sv)
  have hu : q.c*dx+q.s*dy=q.side/2*su := by
    dsimp [dx,dy]
    calc
      _ = q.side/2*su*(q.c^2+q.s^2) := by ring
      _ = q.side/2*su := by rw [q.unit_normal,mul_one]
  have hv : -q.s*dx+q.c*dy=q.side/2*sv := by
    dsimp [dx,dy]
    calc
      _ = q.side/2*sv*(q.c^2+q.s^2) := by ring
      _ = q.side/2*sv := by rw [q.unit_normal,mul_one]
  have habsu : |q.c*dx+q.s*dy|≤q.side/2 := by
    rw [hu,abs_mul,show |su|=1 from signedOne_abs _,mul_one,
      abs_of_nonneg (le_of_lt (half_pos q.side_pos))]
  have habsv : |-q.s*dx+q.c*dy|≤q.side/2 := by
    rw [hv,abs_mul,show |sv|=1 from signedOne_abs _,mul_one,
      abs_of_nonneg (le_of_lt (half_pos q.side_pos))]
  have he : nx*dx+ny*dy=squareRadius q nx ny := by
    dsimp [dx,dy,squareRadius]
    calc
      _ = q.side/2*((nx*q.c+ny*q.s)*su+(-nx*q.s+ny*q.c)*sv) := by ring
      _ = _ := by rw [signedOne_mul,signedOne_mul]
  simpa only [he] using square_closed_linear_bound q nx ny u dx dy h habsu habsv

theorem squareRadius_neg (q : OpenSquare) (nx ny : ℝ) :
    squareRadius q (-nx) (-ny)=squareRadius q nx ny := by
  unfold squareRadius
  rw [show (-nx)*q.c+(-ny)*q.s=-(nx*q.c+ny*q.s) by ring,
    show -(-nx)*q.s+(-ny)*q.c=-(-nx*q.s+ny*q.c) by ring,abs_neg,abs_neg]

end
end S12
