import S12.QuadraticInterval
import S12.WallNormalBounds

namespace S12
set_option maxHeartbeats 0

noncomputable def normalC (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
noncomputable def normalS (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem normal_unit (t : ℝ) : (normalC t)^2+(normalS t)^2=1 := by
  have hd : 1+t^2≠0 := by nlinarith [sq_nonneg t]
  dsimp [normalC,normalS]
  field_simp
  ring

theorem normal_nonnegative (t : ℝ) (h0 : 0≤t) (h1 : t≤1) : 0≤normalC t ∧ 0≤normalS t := by
  have hd : 0<1+t^2 := by nlinarith [sq_nonneg t]
  exact ⟨div_nonneg (by nlinarith) hd.le,div_nonneg (by linarith) hd.le⟩

/-- Quadratic obtained by clearing the positive half-angle denominator
from out - signD*D - signE*E. -/
def supportQuadratic (u v out signD signE : ℚ) : Quadratic :=
  let A := signD*u-signE*v
  let B := signD*v+signE*u
  ⟨out+A,-2*B,out-A⟩

def wallQuadratic (wall : ℚ) : Quadratic := ⟨-1-wall,2,1-wall⟩

structure AngleEnclosure where
  lower : ℚ
  upper : ℚ
  c : ℚ
  s : ℚ
  outer : ℚ
  inner : ℚ
  wall : ℚ
  deriving DecidableEq

def AngleEnclosure.Check (w : AngleEnclosure) : Prop :=
  0≤w.lower ∧ w.upper≤1 ∧ w.c^2+w.s^2=1 ∧ 0<w.outer ∧ 0<w.inner ∧
  w.inner*w.outer≤1 ∧
  (supportQuadratic w.c w.s w.outer 1 1).CheckOn w.lower w.upper ∧
  (supportQuadratic w.c w.s w.outer 1 (-1)).CheckOn w.lower w.upper ∧
  (supportQuadratic w.c w.s w.outer (-1) 1).CheckOn w.lower w.upper ∧
  (supportQuadratic w.c w.s w.outer (-1) (-1)).CheckOn w.lower w.upper ∧
  (wallQuadratic w.wall).CheckOn w.lower w.upper
instance AngleEnclosure.decidableCheck (w : AngleEnclosure) : Decidable w.Check := inferInstanceAs (Decidable (_ ∧ _))

theorem supportQuadratic_sound (u v out d e l h : ℚ)
    (hc : (supportQuadratic u v out d e).CheckOn l h)
    (t : ℝ) (ht0 : (l:ℝ)≤t) (ht1 : t≤(h:ℝ)) :
    (d:ℝ)*((u:ℝ)*normalC t+(v:ℝ)*normalS t)+
      (e:ℝ)*(-(v:ℝ)*normalC t+(u:ℝ)*normalS t)≤out := by
  have hh := Quadratic.sound _ _ _ hc t ht0 ht1
  have hd : 0<1+t^2 := by nlinarith [sq_nonneg t]
  have hid : ((out:ℝ)-((d:ℝ)*((u:ℝ)*normalC t+(v:ℝ)*normalS t)+
      (e:ℝ)*(-(v:ℝ)*normalC t+(u:ℝ)*normalS t)))*(1+t^2)=
      (supportQuadratic u v out d e).eval t := by
    dsimp [normalC,normalS,supportQuadratic,Quadratic.eval]
    push_cast
    field_simp
    ring
  have hn : 0≤((out:ℝ)-((d:ℝ)*((u:ℝ)*normalC t+(v:ℝ)*normalS t)+
      (e:ℝ)*(-(v:ℝ)*normalC t+(u:ℝ)*normalS t)))*(1+t^2) := by rw [hid]; exact hh
  have := (mul_nonneg_iff_of_pos_right hd).mp hn
  linarith only [this]

/-- The bounds hold at every real angle in the closed interval, not just at
sampled angles. They include both signs of each relative normal component. -/
theorem AngleEnclosure.support (w : AngleEnclosure) (hw : w.Check)
    (t : ℝ) (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ)) :
    |(w.c:ℝ)*normalC t+(w.s:ℝ)*normalS t|+
      |-(w.s:ℝ)*normalC t+(w.c:ℝ)*normalS t|≤w.outer := by
  obtain ⟨_,_,_,_,_,_,h0,h1,h2,h3,_⟩ := hw
  have ha := supportQuadratic_sound _ _ _ _ _ _ _ h0 t ht0 ht1
  have hb := supportQuadratic_sound _ _ _ _ _ _ _ h1 t ht0 ht1
  have hc := supportQuadratic_sound _ _ _ _ _ _ _ h2 t ht0 ht1
  have hd := supportQuadratic_sound _ _ _ _ _ _ _ h3 t ht0 ht1
  norm_num at ha hb hc hd
  rcases le_total 0 ((w.c:ℝ)*normalC t+(w.s:ℝ)*normalS t) with hD | hD <;>
    rcases le_total 0 (-(w.s:ℝ)*normalC t+(w.c:ℝ)*normalS t) with hE | hE
  · rw [abs_of_nonneg hD,abs_of_nonneg hE]; linarith only [ha]
  · rw [abs_of_nonneg hD,abs_of_nonpos hE]; linarith only [hb]
  · rw [abs_of_nonpos hD,abs_of_nonneg hE]; linarith only [hc]
  · rw [abs_of_nonpos hD,abs_of_nonpos hE]; linarith only [hd]

theorem AngleEnclosure.wall_bound (w : AngleEnclosure) (hw : w.Check)
    (t : ℝ) (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ)) :
    (w.wall:ℝ)≤normalC t+normalS t := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hc⟩ := hw
  have hh := Quadratic.sound _ _ _ hc t ht0 ht1
  have hd : 0<1+t^2 := by nlinarith [sq_nonneg t]
  have hid : (normalC t+normalS t-w.wall)*(1+t^2)=(wallQuadratic w.wall).eval t := by
    dsimp [normalC,normalS,wallQuadratic,Quadratic.eval]
    push_cast
    field_simp
    ring
  have hn : 0≤(normalC t+normalS t-w.wall)*(1+t^2) := by rw [hid]; exact hh
  have := (mul_nonneg_iff_of_pos_right hd).mp hn
  linarith only [this]

#print axioms AngleEnclosure.support
end S12
