import S12.OverlapCertificate
import S12.CornerCover

namespace S12
open S12Pilot
set_option maxHeartbeats 0

theorem strict_abs_linear_bound (A B x y r : ℝ)
    (hx : |x|<r) (hy : |y|<r) (hcoef : 0< |A|+|B|) :
    |A*x+B*y| < (|A|+|B|)*r := by
  have hm : max |x| |y|<r := max_lt hx hy
  have h0 := mul_le_mul_of_nonneg_left (le_max_left |x| |y|) (abs_nonneg A)
  have h1 := mul_le_mul_of_nonneg_left (le_max_right |x| |y|) (abs_nonneg B)
  have h2 := mul_lt_mul_of_pos_left hm hcoef
  calc
    |A*x+B*y|≤ |A*x|+|B*y| := abs_add_le _ _
    _= |A| * |x|+|B| * |y| := by rw [abs_mul,abs_mul]
    _<(abs A+abs B)*r := by nlinarith only [h0,h1,h2]

/-- Changing between two unit normal frames enlarges each coordinate bound
by at most the sum of the absolute relative-normal components. -/
theorem normal_change_inner (c s u v a b x y : ℝ)
    (hcs : c^2+s^2=1) (huv : u^2+v^2=1)
    (hb : 0<b) (hsize : b*(|c*u+s*v|+|-c*v+s*u|)≤a)
    (hx : |u*x+v*y|<b/2) (hy : |-v*x+u*y|<b/2) :
    |c*x+s*y|<a/2 ∧ |-s*x+c*y|<a/2 := by
  let D := c*u+s*v
  let E := -c*v+s*u
  have hunit : D^2+E^2=1 := by
    calc
      _=(c^2+s^2)*(u^2+v^2) := by dsimp [D,E]; ring
      _=1 := by rw [hcs,huv]; norm_num
  have hpos : 0< |D|+|E| := by
    by_contra he
    have hd0 : D=0 := abs_nonpos_iff.mp (by linarith [abs_nonneg E])
    have he0 : E=0 := abs_nonpos_iff.mp (by linarith [abs_nonneg D])
    rw [hd0,he0] at hunit
    norm_num at hunit
  have hid0 : c*x+s*y=D*(u*x+v*y)+E*(-v*x+u*y) := by
    calc
      _=(c*x+s*y)*(u^2+v^2) := by rw [huv,mul_one]
      _=_ := by dsimp [D,E]; ring
  have hid1 : -s*x+c*y= -E*(u*x+v*y)+D*(-v*x+u*y) := by
    calc
      _=(-s*x+c*y)*(u^2+v^2) := by rw [huv,mul_one]
      _=_ := by dsimp [D,E]; ring
  have h0 := strict_abs_linear_bound D E _ _ (b/2) hx hy hpos
  have h1 := strict_abs_linear_bound (-E) D _ _ (b/2) hx hy (by rw [abs_neg]; linarith)
  rw [←hid0] at h0
  rw [←hid1,abs_neg] at h1
  change b*(|D|+|E|)≤a at hsize
  constructor <;> nlinarith only [h0,h1,hsize]

/-- A sufficiently small fixed reference square lies inside the actual
square at its center, uniformly under the relative-normal bound. -/
theorem reference_inner_containment (q : OpenSquare) (r : ReferenceSquare) (hr : r.Check)
    (hsize : (r.side:ℝ)*(|q.c*r.c+q.s*r.s|+|-q.c*r.s+q.s*r.c|)≤q.side) :
    ∀ P : ℝ × ℝ,P-(centerX q,centerY q)∈squareSet (r.toSquare hr) → P∈squareSet q := by
  intro P hP
  have hbands := hP
  change InBands (-(r.side:ℝ)/2) (-(r.side:ℝ)/2) r.side
    ((r.c:ℝ)*(P.1-centerX q)+(r.s:ℝ)*(P.2-centerY q))
    (-(r.s:ℝ)*(P.1-centerX q)+(r.c:ℝ)*(P.2-centerY q)) at hbands
  obtain ⟨h0,h1,h2,h3⟩ := hbands
  have hh := normal_change_inner q.c q.s r.c r.s q.side r.side
    (P.1-centerX q) (P.2-centerY q) q.unit_normal (r.toSquare hr).unit_normal
    (by exact_mod_cast hr.2) hsize
    (by rw [abs_lt]; constructor <;> linarith) (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨hu0,hu1⟩ := abs_lt.mp hh.1
  obtain ⟨hv0,hv1⟩ := abs_lt.mp hh.2
  apply (inside_centered_iff q P.1 P.2).mpr
  dsimp [InBands]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

#print axioms reference_inner_containment
end S12
