import S12.AxisGap
import Compact.Geometry.ScalarSATGeneral
namespace S12
open S12Pilot
noncomputable section
set_option maxHeartbeats 0

def relativeC (q r : OpenSquare) : ℝ := q.c*r.c+q.s*r.s
def relativeS (q r : OpenSquare) : ℝ := -q.s*r.c+q.c*r.s

theorem relative_unit (q r : OpenSquare) : (relativeC q r)^2+(relativeS q r)^2=1 := by
  unfold relativeC relativeS
  calc
    _ = (q.c^2+q.s^2)*(r.c^2+r.s^2) := by ring
    _ = 1 := by rw [q.unit_normal,r.unit_normal]; norm_num

theorem rotated_dot (c s x y X Y : ℝ) (hu : c^2+s^2=1) :
    (c*x+s*y)*(c*X+s*Y)+(-s*x+c*y)*(-s*X+c*Y)=x*X+y*Y := by
  linear_combination (x*X+y*Y)*hu

theorem rotated_coordinate (c s k l x y : ℝ) (hu : c^2+s^2=1) :
    (c*k+s*l)*(c*x+s*y)+(-s*k+c*l)*(-s*x+c*y)=k*x+l*y :=
  rotated_dot c s k l x y hu

theorem rotated_cross_coordinate (c s k l x y : ℝ) (hu : c^2+s^2=1) :
    -(-s*k+c*l)*(c*x+s*y)+(c*k+s*l)*(-s*x+c*y)=-l*x+k*y := by
  linear_combination (-l*x+k*y)*hu

theorem squareRadius_self (q : OpenSquare) : squareRadius q q.c q.s=q.side/2 := by
  unfold squareRadius
  rw [show q.c*q.c+q.s*q.s=1 by nlinarith [q.unit_normal],
    show -q.c*q.s+q.s*q.c=0 by ring]
  norm_num

theorem squareRadius_turn_axis (q : OpenSquare) (nx ny : ℝ) :
    squareRadius q (-ny) nx=squareRadius q nx ny := by
  unfold squareRadius
  rw [show (-ny)*q.c+nx*q.s=-(-nx*q.s+ny*q.c) by ring,
    show -(-ny)*q.s+nx*q.c=nx*q.c+ny*q.s by ring,abs_neg,add_comm]

theorem squareRadius_cross (q r : OpenSquare) :
    squareRadius r q.c q.s=r.side/2*(|relativeC q r|+|relativeS q r|) := by
  unfold squareRadius relativeC relativeS
  rw [show -q.c*r.s+q.s*r.c=-(-q.s*r.c+q.c*r.s) by ring,abs_neg]

theorem relative_abs_swap (q r : OpenSquare) :
    |relativeC r q|+|relativeS r q|=|relativeC q r|+|relativeS q r| := by
  unfold relativeC relativeS
  rw [show r.c*q.c+r.s*q.s=q.c*r.c+q.s*r.s by ring,
    show -r.s*q.c+r.c*q.s=-(-q.s*r.c+q.c*r.s) by ring,abs_neg]

def AxisSeparates (q r : OpenSquare) (nx ny : ℝ) : Prop :=
  squareRadius q nx ny+squareRadius r nx ny≤
    |nx*(centerX r-centerX q)+ny*(centerY r-centerY q)|

/-- Completeness of the separating-axis test for two arbitrary open squares.
Weak inequalities correctly include squares touching at a side or a vertex. -/
theorem square_separating_axes (q r : OpenSquare)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    AxisSeparates q r q.c q.s ∨ AxisSeparates q r (-q.s) q.c ∨
    AxisSeparates q r r.c r.s ∨ AxisSeparates q r (-r.s) r.c := by
  by_cases h0 : AxisSeparates q r q.c q.s
  · exact Or.inl h0
  by_cases h1 : AxisSeparates q r (-q.s) q.c
  · exact Or.inr (Or.inl h1)
  by_cases h2 : AxisSeparates q r r.c r.s
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : AxisSeparates q r (-r.s) r.c
  · exact Or.inr (Or.inr (Or.inr h3))
  exfalso
  let dx := centerX r-centerX q
  let dy := centerY r-centerY q
  let X := q.c*dx+q.s*dy
  let Y := -q.s*dx+q.c*dy
  let c := relativeC q r
  let s := relativeS q r
  have hP : c*X+s*Y=r.c*dx+r.s*dy :=
    rotated_coordinate q.c q.s r.c r.s dx dy q.unit_normal
  have hV : -s*X+c*Y=-r.s*dx+r.c*dy :=
    rotated_cross_coordinate q.c q.s r.c r.s dx dy q.unit_normal
  have haxis : AxisOverlapAbs (q.side/2) (r.side/2) c s X Y := by
    refine ⟨?_,?_,?_,?_⟩
    · have hh := lt_of_not_ge h0
      simpa only [AxisSeparates,squareRadius_self,squareRadius_cross] using hh
    · have hh := lt_of_not_ge h1
      simpa only [AxisSeparates,squareRadius_turn_axis,squareRadius_self,squareRadius_cross] using hh
    · have hh := lt_of_not_ge h2
      rw [hP]
      simpa only [AxisSeparates,squareRadius_self,squareRadius_cross,relative_abs_swap,add_comm] using hh
    · have hh := lt_of_not_ge h3
      rw [hV]
      simpa only [AxisSeparates,squareRadius_turn_axis,squareRadius_self,squareRadius_cross,relative_abs_swap,add_comm] using hh
  obtain ⟨x,y,hx,hy,hru,hrv⟩ := N12Compact.SATGeneral.overlap
    (q.side/2) (r.side/2) c s X Y (c*X+s*Y) (-s*X+c*Y)
    (half_pos q.side_pos) (half_pos r.side_pos) (relative_unit q r) rfl rfl
    haxis.1 haxis.2.1 haxis.2.2.1 haxis.2.2.2
  let px := centerX q + q.c*x-q.s*y
  let py := centerY q + q.s*x+q.c*y
  have hqu : q.c*(px-centerX q)+q.s*(py-centerY q)=x := by
    calc
      _ = x*(q.c^2+q.s^2) := by dsimp [px,py]; ring
      _ = x := by rw [q.unit_normal,mul_one]
  have hqv : -q.s*(px-centerX q)+q.c*(py-centerY q)=y := by
    calc
      _ = y*(q.c^2+q.s^2) := by dsimp [px,py]; ring
      _ = y := by rw [q.unit_normal,mul_one]
  have hru' : r.c*(px-centerX r)+r.s*(py-centerY r)=c*x+s*y-(c*X+s*Y) := by
    rw [hP]
    dsimp [px,py,c,s,relativeC,relativeS,dx,dy]
    ring
  have hrv' : -r.s*(px-centerX r)+r.c*(py-centerY r)=-s*x+c*y-(-s*X+c*Y) := by
    rw [hV]
    dsimp [px,py,c,s,relativeC,relativeS,dx,dy]
    ring
  apply hd px py
  constructor
  · apply (inside_centered_iff q px py).mpr
    rw [hqu,hqv]
    obtain ⟨hx0,hx1⟩ := abs_lt.mp hx
    obtain ⟨hy0,hy1⟩ := abs_lt.mp hy
    dsimp [InBands]
    exact ⟨by linarith only [hx0],by linarith only [hx1],
      by linarith only [hy0],by linarith only [hy1]⟩
  · apply (inside_centered_iff r px py).mpr
    rw [hru',hrv']
    obtain ⟨hx0,hx1⟩ := abs_lt.mp hru
    obtain ⟨hy0,hy1⟩ := abs_lt.mp hrv
    dsimp [InBands]
    exact ⟨by linarith only [hx0],by linarith only [hx1],
      by linarith only [hy0],by linarith only [hy1]⟩

#print axioms square_separating_axes
end
end S12
