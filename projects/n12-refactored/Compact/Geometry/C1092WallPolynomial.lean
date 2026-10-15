import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Source-only candidate: uniform exclusion of all 72 wall systems,
including the previously missing `P_face = 0` systems.
This file has not yet been replayed by Lean.
The eleven residuals below retain the original draft's coefficients and
strictness. Nothing here asserts an entrance from an actual packing. -/

namespace N12Compact.C1092WallPolynomial
noncomputable section

def C (t : ℝ) : ℝ := 1 - t^2
def S (t : ℝ) : ℝ := 2*t
def D (t : ℝ) : ℝ := 1 + t^2

def residual (x y t z0 z1 z2 : ℝ) (bface : Fin 2) (pface : Fin 3)
    (i : Fin 11) : ℝ :=
  match i.val with
  | 0 => 1/2 - z0
  | 1 => 1/2 + z0
  | 2 => 1/2 - z1
  | 3 => 1/2 + z1
  | 4 => z2
  | 5 => 1 - z2
  | 6 => -(C t + S t)/2 - C t*z0 + S t*z1 + (457/500)*D t*z2
  | 7 => C t*z0 - S t*z1 + (43/500)*D t*z2
  | 8 => S t*z0 + C t*z1
  | 9 => if bface.val = 0 then -D t/2 - D t*z0 + S t*z2
         else -D t/2 - D t*z1 + C t*z2
  | _ => match pface.val with
    | 0 => -D t/2 + D t*z0 + ((x-457/500)*C t - (2-y)*S t)*z2
    | 1 => -D t/2 - D t*z0 + (-(x-457/500)*C t + (2-y)*S t)*z2
    | _ => -D t/2 - D t*z1 + ((x-457/500)*S t + (2-y)*C t)*z2

def WallSystem (x y t z0 z1 z2 : ℝ) (bface : Fin 2) (pface : Fin 3) : Prop :=
  ∀ i : Fin 11, if i.val < 6 then 0 < residual x y t z0 z1 z2 bface pface i
    else 0 ≤ residual x y t z0 z1 z2 bface pface i

theorem residual_nonneg {x y t z0 z1 z2 : ℝ} {bface : Fin 2} {pface : Fin 3}
    (hsys : WallSystem x y t z0 z1 z2 bface pface) (i : Fin 11) :
    0 ≤ residual x y t z0 z1 z2 bface pface i := by
  have hi := hsys i
  by_cases h : i.val < 6
  · exact le_of_lt (by simpa [h] using hi)
  · simpa [h] using hi

theorem reciprocal_band {x y t z0 z1 z2 : ℝ} {bface : Fin 2} {pface : Fin 3}
    (hsys : WallSystem x y t z0 z1 z2 bface pface) : 0 < z2 ∧ z2 < 1 := by
  have h4 := hsys (4 : Fin 11)
  have h5 := hsys (5 : Fin 11)
  change 0 < z2 at h4
  change 0 < 1-z2 at h5
  exact ⟨h4, by linarith⟩

def targetX : Fin 12 → ℝ :=
  ![457/500,457/500,23/25,23/25,47/50,47/50,24/25,24/25,49/50,49/50,1,1]
def targetY : Fin 12 → ℝ :=
  ![837/500,1999/1000,1667/1000,997/500,823/500,1973/1000,
    1627/1000,39/20,1611/1000,481/250,803/500,947/500]

/-- The two opposite faces are less than one unit apart. This proves all
twelve `B_face = 0` systems without any angle partition. -/
theorem excludes_opposite_faces (x y t z0 z1 z2 : ℝ)
    (hdist : (x-457/500)^2 + (y-1)^2 ≤ 1)
    (hsys : WallSystem x y t z0 z1 z2 0 0) : False := by
  obtain ⟨hz0,hz1⟩ := reciprocal_band hsys
  have hD : 0 < D t := by dsimp [D]; nlinarith [sq_nonneg t]
  have hunit : (C t)^2+(S t)^2=(D t)^2 := by dsimp [C,S,D]; ring
  let L := (x-457/500)*C t+(y-1)*S t
  have hid : L^2+((x-457/500)*S t-(y-1)*C t)^2 =
      ((x-457/500)^2+(y-1)^2)*(D t)^2 := by
    rw [← hunit]
    dsimp [L]
    ring
  have hb := mul_le_mul_of_nonneg_right hdist (sq_nonneg (D t))
  have hL2 : L^2 ≤ (D t)^2 := by
    have first : L^2 ≤ ((x-457/500)^2+(y-1)^2)*(D t)^2 := by
      rw [← hid]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact first.trans (by simpa only [one_mul] using hb)
  have hL : L ≤ D t := by nlinarith only [hL2,hD,sq_nonneg (L-D t)]
  have hproduct := mul_nonneg hz0.le (sub_nonneg.mpr hL)
  have hstrict := mul_pos hD (sub_pos.mpr hz1)
  have h9 := residual_nonneg hsys (9 : Fin 11)
  have h10 := residual_nonneg hsys (10 : Fin 11)
  norm_num [residual] at h9 h10
  dsimp [L] at hproduct
  nlinarith only [h9,h10,hproduct,hstrict]

theorem target_distance (i : Fin 12) :
    (targetX i-457/500)^2+(targetY i-1)^2 ≤ 1 := by
  fin_cases i <;> norm_num [targetX,targetY]

theorem excludes_target_bface0 (i : Fin 12) (t z0 z1 z2 : ℝ)
    (hsys : WallSystem (targetX i) (targetY i) t z0 z1 z2 0 0) : False :=
  excludes_opposite_faces _ _ _ _ _ _ (target_distance i) hsys

/-- The single remaining support margin after eliminating the centers. -/
def margin (x h t : ℝ) : ℝ :=
  1-x+2*h*t+(2*x-457/125)*t^2+(4-2*h)*t^3-(1+x)*t^4

/-- A parametric quartic criterion on the entire closed interval. The proof
is a square completion plus the nonnegative factor `t*(1-t)`; `r` is merely
an algebraic expansion point and is not an angle subdivision. -/
theorem quartic_taylor_nonneg (a0 a1 a2 a3 a4 r t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha4 : a4 ≤ 0)
    (hK : 0 < a2+2*a3*r+3*a4*r^2)
    (hG : 0 ≤ a3+a4*(1+2*r))
    (hdisc :
      (a1+2*a2*r+3*a3*r^2+4*a4*r^3)^2 ≤
      4*(a2+2*a3*r+3*a4*r^2)*(a0+a1*r+a2*r^2+a3*r^3+a4*r^4)) :
    0 ≤ a0+a1*t+a2*t^2+a3*t^3+a4*t^4 := by
  let K := a2+2*a3*r+3*a4*r^2
  let G := a3+a4*(1+2*r)
  let f := a0+a1*r+a2*r^2+a3*r^3+a4*r^4
  let g := a1+2*a2*r+3*a3*r^2+4*a4*r^3
  have hextra : 0 ≤ 4*K*t*(G+(-a4)*(1-t))*(t-r)^2 := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by dsimp [K]; linarith) ht0
      · exact add_nonneg hG (mul_nonneg (neg_nonneg.mpr ha4) (sub_nonneg.mpr ht1))
    · exact sq_nonneg _
  have hid : 4*K*(a0+a1*t+a2*t^2+a3*t^3+a4*t^4) =
      (2*K*(t-r)+g)^2+(4*K*f-g^2)+
        4*K*t*(G+(-a4)*(1-t))*(t-r)^2 := by
    dsimp [K,G,f,g]
    ring
  have hprod : 0 ≤ 4*K*(a0+a1*t+a2*t^2+a3*t^3+a4*t^4) := by
    have hd : 0 ≤ 4*K*f-g^2 := by dsimp [K,f,g]; linarith only [hdisc]
    nlinarith only [hid,hd,hextra,sq_nonneg (2*K*(t-r)+g)]
  have hKpos : 0 < 4*K := by dsimp [K]; linarith only [hK]
  exact nonneg_of_mul_nonneg_right hprod hKpos

/-- The cubic endpoint version uses the minimum of its linear remainder
at `t = 1`. -/
theorem cubic_taylor_nonneg (a0 a1 a2 a3 r t : ℝ)
    (ht1 : t ≤ 1) (ha3 : a3 ≤ 0)
    (hK : 0 < a2+a3*(1+2*r))
    (hdisc : (a1+2*a2*r+3*a3*r^2)^2 ≤
      4*(a2+a3*(1+2*r))*(a0+a1*r+a2*r^2+a3*r^3)) :
    0 ≤ a0+a1*t+a2*t^2+a3*t^3 := by
  let K := a2+a3*(1+2*r)
  let f := a0+a1*r+a2*r^2+a3*r^3
  let g := a1+2*a2*r+3*a3*r^2
  have hextra : 0 ≤ 4*K*(-a3)*(1-t)*(t-r)^2 := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by dsimp [K]; linarith) (neg_nonneg.mpr ha3)
      · exact sub_nonneg.mpr ht1
    · exact sq_nonneg _
  have hid : 4*K*(a0+a1*t+a2*t^2+a3*t^3) =
      (2*K*(t-r)+g)^2+(4*K*f-g^2)+4*K*(-a3)*(1-t)*(t-r)^2 := by
    dsimp [K,f,g]
    ring
  have hprod : 0 ≤ 4*K*(a0+a1*t+a2*t^2+a3*t^3) := by
    have hd : 0 ≤ 4*K*f-g^2 := by dsimp [K,f,g]; linarith only [hdisc]
    nlinarith only [hid,hd,hextra,sq_nonneg (2*K*(t-r)+g)]
  have hKpos : 0 < 4*K := by dsimp [K]; linarith only [hK]
  exact nonneg_of_mul_nonneg_right hprod hKpos

def upperX : Fin 5 → ℝ := ![457/500,23/25,47/50,24/25,49/50]
def upperH : Fin 5 → ℝ := ![1/1000,3/500,27/1000,1/20,19/250]
def expansionPoint : Fin 5 → ℝ := ![83/200,41/100,39/100,9/25,13/40]

/-- Five rational data tuples instantiate one interval-free theorem.
The three checks per tuple are strictly positive exact rational numbers. -/
theorem upper_five_margin (i : Fin 5) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ margin (upperX i) (upperH i) t := by
  unfold margin
  have result : 0 ≤ (1-upperX i)+(2*upperH i)*t+
      (2*upperX i-457/125)*t^2+(4-2*upperH i)*t^3+(-(1+upperX i))*t^4 := by
    apply quartic_taylor_nonneg (1-upperX i) (2*upperH i)
      (2*upperX i-457/125) (4-2*upperH i) (-(1+upperX i))
      (expansionPoint i) t ht0 ht1
    all_goals fin_cases i <;> norm_num [upperX,upperH,expansionPoint]
  simpa only [sub_eq_add_neg,neg_mul] using result

theorem upper_endpoint_margin (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ margin 1 (53/500) t := by
  have hp : 0 ≤ (53/250:ℝ)-(207/125)*t+(947/250)*t^2-2*t^3 := by
    have result : 0 ≤ (53/250:ℝ)+(-(207/125))*t+(947/250)*t^2+(-2)*t^3 := by
      apply cubic_taylor_nonneg (53/250) (-(207/125)) (947/250) (-2)
        (7/25) t ht1 <;> norm_num
    simpa only [sub_eq_add_neg,neg_mul] using result
  have hid : margin 1 (53/500) t =
      t*((53/250:ℝ)-(207/125)*t+(947/250)*t^2-2*t^3) := by
    dsimp [margin]; ring
  rw [hid]
  exact mul_nonneg ht0 hp

theorem margin_mono_height (x h H t : ℝ) (hh : h ≤ H)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm : 0 ≤ margin x h t) :
    0 ≤ margin x H t := by
  have hc : 0 ≤ 1-t^2 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hhterm := mul_nonneg
    (mul_nonneg (by linarith only [hh] : 0 ≤ 2*(H-h)) ht0) hc
  have hid : margin x H t = margin x h t+2*(H-h)*t*(1-t^2) := by
    dsimp [margin]; ring
  linarith only [hid,hhterm,hm]

/-- Vertical rays below the six upper targets. Their convex hull could be
used as well, because the margin is affine in the point coordinates. -/
def UpperTargetRegion (x h : ℝ) : Prop :=
  (∃ i : Fin 5, x = upperX i ∧ upperH i ≤ h) ∨ (x = 1 ∧ 53/500 ≤ h)

theorem region_margin (x h t : ℝ) (hp : UpperTargetRegion x h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ margin x h t := by
  rcases hp with ⟨i,rfl,hh⟩ | ⟨rfl,hh⟩
  · exact margin_mono_height _ _ _ _ hh ht0 ht1 (upper_five_margin i t ht0 ht1)
  · exact margin_mono_height _ _ _ _ hh ht0 ht1 (upper_endpoint_margin t ht0 ht1)

theorem target_region (i : Fin 12) :
    UpperTargetRegion (targetX i) (2-targetY i) := by
  fin_cases i
  · exact Or.inl ⟨⟨0,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨0,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨1,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨1,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨2,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨2,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨3,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨3,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨4,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inl ⟨⟨4,by decide⟩, by norm_num [targetX,upperX], by norm_num [targetY,upperH]⟩
  · exact Or.inr ⟨by norm_num [targetX], by norm_num [targetY]⟩
  · exact Or.inr ⟨by norm_num [targetX], by norm_num [targetY]⟩

/-- `B_face = 1` needs only this single support margin. -/
theorem excludes_adjacent_faces (x y t z0 z1 z2 : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm : 0 ≤ margin x (2-y) t)
    (hsys : WallSystem x y t z0 z1 z2 1 0) : False := by
  obtain ⟨hz0,hz1⟩ := reciprocal_band hsys
  have hD : 0 < D t := by dsimp [D]; nlinarith [sq_nonneg t]
  have hc : 0 ≤ C t := by
    dsimp [C]
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hs : 0 ≤ S t := by dsimp [S]; linarith
  have hcs : 0 < C t+S t := by
    have ht := mul_nonneg ht0 (sub_nonneg.mpr ht1)
    dsimp [C,S,D] at *
    nlinarith only [ht,hD]
  let L := D t*(C t+S t)
  let E := (457/500)*(D t)^2+(x-457/500)*(C t)^2+(y-1)*C t*S t
  have hEL : E ≤ L := by
    have heq : L-E = margin x (2-y) t := by
      dsimp [L,E,C,S,D,margin]; ring
    linarith only [heq,hm]
  have hL : 0 < L := mul_pos hD hcs
  have hstrict := mul_pos hL (sub_pos.mpr hz1)
  have hproduct := mul_nonneg hz0.le (sub_nonneg.mpr hEL)
  have h6 := mul_nonneg hD.le (residual_nonneg hsys (6 : Fin 11))
  have h9 := mul_nonneg hs (residual_nonneg hsys (9 : Fin 11))
  have h10 := mul_nonneg hc (residual_nonneg hsys (10 : Fin 11))
  have hid : D t*residual x y t z0 z1 z2 1 0 6+
      S t*residual x y t z0 z1 z2 1 0 9+
      C t*residual x y t z0 z1 z2 1 0 10 = E*z2-L := by
    dsimp [residual,E,L]
    ring
  nlinarith only [hid,h6,h9,h10,hstrict,hproduct]

/-- Complete coverage of both boundary faces and all twelve original
target points for `P_face = 0`, including both angle endpoints. -/
theorem excludes_target_pface0 (i : Fin 12) (bface : Fin 2) (t z0 z1 z2 : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsys : WallSystem (targetX i) (targetY i) t z0 z1 z2 bface 0) : False := by
  fin_cases bface
  · exact excludes_target_bface0 i t z0 z1 z2 hsys
  · exact excludes_adjacent_faces _ _ _ _ _ _ ht0 ht1
      (region_margin _ _ _ (target_region i) ht0 ht1) hsys

/-- The negative-U point face reduces to a second ordinary distance bound;
the boundary-face row is not needed. -/
theorem excludes_pface1 (x y t z0 z1 z2 : ℝ) (bface : Fin 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hdist : (1-x)^2+(2-y)^2 ≤ 1/4)
    (hsys : WallSystem x y t z0 z1 z2 bface 1) : False := by
  obtain ⟨hz0,hz1⟩ := reciprocal_band hsys
  have hD : 0 < D t := by dsimp [D]; nlinarith [sq_nonneg t]
  have hc : 0 ≤ C t := by
    dsimp [C]; nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hs : 0 ≤ S t := by dsimp [S]; linarith
  let L := (1-x)*C t+(2-y)*S t
  let R := (D t)^2/2
  have hidnorm : L^2+((1-x)*S t-(2-y)*C t)^2 =
      ((1-x)^2+(2-y)^2)*(D t)^2 := by dsimp [L,C,S,D]; ring
  have hb := mul_le_mul_of_nonneg_right hdist (sq_nonneg (D t))
  have hL2 : (2*L)^2 ≤ (D t)^2 := by
    have first : L^2 ≤ ((1-x)^2+(2-y)^2)*(D t)^2 := by
      rw [← hidnorm]
      exact le_add_of_nonneg_right (sq_nonneg _)
    calc
      (2*L)^2 = 4*L^2 := by ring
      _ ≤ 4*((1/4)*(D t)^2) :=
        mul_le_mul_of_nonneg_left (first.trans hb) (by norm_num)
      _ = (D t)^2 := by ring
  have hL : 2*L ≤ D t := by nlinarith only [hL2,hD,sq_nonneg (2*L-D t)]
  have hR : 0 < R := by dsimp [R]; nlinarith only [sq_pos_of_pos hD]
  have hcost : D t*L ≤ R := by
    calc
      D t*L ≤ D t*(D t/2) := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
          (by simpa only [mul_comm] using hL)) hD.le
      _ = R := by dsimp [R]; ring
  have hproduct := mul_nonneg hz0.le (sub_nonneg.mpr hcost)
  have hstrict := mul_pos hR (sub_pos.mpr hz1)
  have h7 := mul_nonneg hc (residual_nonneg hsys (7 : Fin 11))
  have h8 := mul_nonneg hs (residual_nonneg hsys (8 : Fin 11))
  have h10 := mul_nonneg hD.le (residual_nonneg hsys (10 : Fin 11))
  have hid : C t*residual x y t z0 z1 z2 bface 1 7+
      S t*residual x y t z0 z1 z2 bface 1 8+
      D t*residual x y t z0 z1 z2 bface 1 10 = D t*L*z2-R := by
    dsimp [residual,L,R,C,S,D]; ring
  nlinarith only [hid,h7,h8,h10,hproduct,hstrict]

theorem target_half_distance (i : Fin 12) :
    (1-targetX i)^2+(2-targetY i)^2 ≤ 1/4 := by
  fin_cases i <;> norm_num [targetX,targetY]

/-- One cubic controls the negative-V point face for the entire rectangle.
This replaces the more elaborate recovered quartic SOS identity. -/
theorem pface2_cubic_nonneg (t : ℝ) (ht1 : t ≤ 1) :
    0 ≤ (53/500:ℝ)-(447/500)*t+(1053/500)*t^2-(447/500)*t^3 := by
  have result : 0 ≤ (53/500:ℝ)+(-(447/500))*t+(1053/500)*t^2+(-(447/500))*t^3 := by
    apply cubic_taylor_nonneg (53/500) (-(447/500)) (1053/500) (-(447/500))
      (1/4) t ht1 <;> norm_num
  simpa only [sub_eq_add_neg,neg_mul] using result

theorem excludes_pface2 (x y t z0 z1 z2 : ℝ) (bface : Fin 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : x ≤ 1) (hh : 2-y ≤ 197/500)
    (hsys : WallSystem x y t z0 z1 z2 bface 2) : False := by
  obtain ⟨hz0,hz1⟩ := reciprocal_band hsys
  have hD : 0 < D t := by dsimp [D]; nlinarith [sq_nonneg t]
  have hc : 0 ≤ C t := by
    dsimp [C]; nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hs : 0 ≤ S t := by dsimp [S]; linarith
  let W := D t*(x*S t+(2-y)*C t)
  let R := ((D t)^2+S t*(C t+S t))/2
  have hR : 0 < R := by
    have hsc := mul_nonneg hs (add_nonneg hc hs)
    dsimp [R]; nlinarith only [sq_pos_of_pos hD,hsc]
  have hbase := mul_nonneg (sub_nonneg.mpr ht1) (pface2_cubic_nonneg t ht1)
  have hmaxid : R-D t*(S t+(197/500)*C t) =
      (1-t)*((53/500:ℝ)-(447/500)*t+(1053/500)*t^2-(447/500)*t^3) := by
    dsimp [R,C,S,D]; ring
  have hdown := mul_nonneg hD.le (add_nonneg
    (mul_nonneg (sub_nonneg.mpr hx) hs) (mul_nonneg (sub_nonneg.mpr hh) hc))
  have hcost : W ≤ R := by dsimp [W]; nlinarith only [hbase,hmaxid,hdown]
  have hproduct := mul_nonneg hz0.le (sub_nonneg.mpr hcost)
  have hstrict := mul_pos hR (sub_pos.mpr hz1)
  have h6 := mul_nonneg hs (residual_nonneg hsys (6 : Fin 11))
  have h8 := mul_nonneg hc (residual_nonneg hsys (8 : Fin 11))
  have h10 := mul_nonneg hD.le (residual_nonneg hsys (10 : Fin 11))
  have hid : S t*residual x y t z0 z1 z2 bface 2 6+
      C t*residual x y t z0 z1 z2 bface 2 8+
      D t*residual x y t z0 z1 z2 bface 2 10 = W*z2-R := by
    dsimp [residual,W,R,C,S,D]; ring
  nlinarith only [hid,h6,h8,h10,hproduct,hstrict]

theorem target_rectangle (i : Fin 12) :
    targetX i ≤ 1 ∧ 2-targetY i ≤ 197/500 := by
  fin_cases i <;> norm_num [targetX,targetY]

/-- All twelve targets, both boundary faces and all three remaining point
faces are covered uniformly over the full closed interval `[0,1]`.
This theorem is local: it has no `NormalizedPacking` or `ExcludesCase`
conclusion and does not discharge its own geometric entrance. -/
theorem excludes_all_target_systems (i : Fin 12) (bface : Fin 2) (pface : Fin 3)
    (t z0 z1 z2 : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsys : WallSystem (targetX i) (targetY i) t z0 z1 z2 bface pface) : False := by
  fin_cases pface
  · exact excludes_target_pface0 i bface t z0 z1 z2 ht0 ht1 hsys
  · exact excludes_pface1 _ _ _ _ _ _ bface ht0 ht1 (target_half_distance i) hsys
  · exact excludes_pface2 _ _ _ _ _ _ bface ht0 ht1
      (target_rectangle i).1 (target_rectangle i).2 hsys

#print axioms excludes_all_target_systems

end
end N12Compact.C1092WallPolynomial
