import Compact.Geometry.C977NegativeCorner
import Compact.Geometry.FourSquareBLBridge

/-! Actual face restrictions for a negative canonical left-wall square
that misses the shared row point (1,2). The upper-left marker exclusion
is retained explicitly. No virtual coordinate barrier is assumed. -/
namespace N12Compact.LeftWallNegativeFaces

open S12 S12Pilot FourSquareAnchors
open C977CornerCubic C977NegativeCorner

/-- The two missing points force both upper faces in a negative canonical
frame. The genuine left container wall then gives a coupled lower bound
on these same faces. -/
theorem faces (W : OpenSquare) (t : ℝ) (hs : W.s = -t)
    (normal : Normal W.c t) (side : 1 < W.side)
    (box : InsideContainer W)
    (marker : W.Inside (457/500) 2)
    (point : W.Inside 1 (113/50))
    (missing : ¬W.Inside 1 2)
    (missingTop : ¬W.Inside (457/500) 3) :
    W.loU+W.side ≤ W.c-2*t ∧
    W.loV+W.side ≤ (457/500)*t+3*W.c ∧
    W.side*(W.c+t) ≤ W.c*(W.loU+W.side)+t*(W.loV+W.side) := by
  have b := normal_bounds normal
  have hc : 0 < W.c := by linarith only [b.1]
  have m := (negative_bands W t _ _ hs).mp marker
  have p := (negative_bands W t _ _ hs).mp point
  have capU : W.loU+W.side ≤ W.c-2*t := by
    by_contra no
    apply missing
    apply (negative_bands W t 1 2 hs).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [no,p.1,p.2.2.2,m.2.2.1,hc,normal.1]
  have short : (43/500)*W.c+t < 1 := by
    linarith only [normal.2.1,b.2.2.2.2.2]
  have capV : W.loV+W.side ≤ (457/500)*t+3*W.c := by
    by_contra no
    apply missingTop
    apply (negative_bands W t (457/500) 3 hs).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [no,capU,side,short,m.2.1,m.2.2.1,hc,normal.1]
  have wall := FourSquareBLBridge.left_wall W hc.le box
  rw [hs,abs_neg,abs_of_nonneg normal.1] at wall
  dsimp [centerX] at wall
  rw [hs] at wall
  have coupled : W.side*(W.c+t) ≤
      W.c*(W.loU+W.side)+t*(W.loV+W.side) := by
    nlinarith only [wall]
  exact ⟨capU,capV,coupled⟩

private theorem far_margin {d t : ℝ} (normal : Normal d t) :
    0 < d+t-(113/100)*d*t-19/25-(77/500)*t^2 := by
  have b := normal_bounds normal
  have nonnegative : 0 ≤ d*t :=
    mul_nonneg (le_trans normal.1 normal.2.1) normal.1
  have chord := mul_nonneg
    (show 0 ≤ d+t-1 by linarith only [b.2.2.2.2.1])
    (show 0 ≤ 10/7-(d+t) by linarith only [b.2.2.2.2.2])
  have strong : 1+(14/17)*d*t ≤ d+t := by
    nlinarith only [chord,normal.2.2]
  have productHalf : d*t ≤ 1/2 := by
    nlinarith only [normal.2.2,sq_nonneg (d-t)]
  have squares := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0 ≤ d+t by linarith only [b.1,normal.1])
  have tiltHalf : t^2 ≤ 1/2 := by
    nlinarith only [squares,normal.2.2]
  nlinarith only [strong,productHalf,tiltHalf]

/-- The original lower singleton's far seed forces the wall square's lower
V face. Together with the excluded upper marker this rules out the entire
continuous range t >= 3/5. -/
theorem lower_face_and_tilt (W : OpenSquare) (t : ℝ) (hs : W.s = -t)
    (normal : Normal W.c t) (side : 1 < W.side)
    (box : InsideContainer W)
    (marker : W.Inside (457/500) 2)
    (point : W.Inside 1 (113/50))
    (missing : ¬W.Inside 1 2)
    (missingTop : ¬W.Inside (457/500) 3)
    (missingFar : ¬W.Inside (19/25) (187/100)) :
    (19/25)*t+(187/100)*W.c ≤ W.loV ∧ t < 3/5 := by
  classical
  obtain ⟨capU,capV,wall⟩ := faces W t hs normal side box marker point missing missingTop
  have b := normal_bounds normal
  have hc : 0 < W.c := by linarith only [b.1]
  have m := (negative_bands W t _ _ hs).mp marker
  have vweight := mul_nonneg normal.1 (sub_nonneg.mpr capV)
  have strict := mul_pos (sub_pos.mpr side)
    (show 0 < W.c+t by linarith only [hc,normal.1])
  have margin := far_margin normal
  have scaled : 0 < W.c*(W.loU+W.side-((19/25)*W.c-(187/100)*t)) := by
    nlinarith only [wall,vweight,strict,margin,normal.2.2]
  have farUhi : (19/25)*W.c-(187/100)*t < W.loU+W.side := by
    have gap := pos_of_mul_pos_right scaled hc.le
    linarith only [gap]
  have farVlo : (19/25)*t+(187/100)*W.c ≤ W.loV := by
    by_contra no
    apply missingFar
    apply (negative_bands W t (19/25) (187/100) hs).mpr
    refine ⟨?_,by linarith only [farUhi],?_,?_⟩ <;>
      nlinarith only [no,capU,side,b.2.1,normal.1,m.2.2.2,hc]
  have width : W.side ≤ (113/100)*W.c+(77/500)*t := by
    linarith only [farVlo,capV]
  have dotSquare : ((4/5)*W.c+(3/5)*t)^2 ≤ 1 := by
    nlinarith only [normal.2.2,sq_nonneg (3*W.c-4*t)]
  have dot : (4/5)*W.c+(3/5)*t ≤ 1 := by
    nlinarith only [dotSquare,sq_nonneg ((4/5)*W.c+(3/5)*t-1)]
  have tilt : t < 3/5 := by
    by_contra no
    have high : 3/5 ≤ t := le_of_not_gt no
    linarith only [width,dot,high,side]
  exact ⟨farVlo,tilt⟩

end N12Compact.LeftWallNegativeFaces
