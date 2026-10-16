import Compact.Geometry.LeftWallNegativeFaces
import Compact.Geometry.CentralLeftWallSeparation

/-! The central-axis separator is impossible for an actual negative
left-wall square. The original side cap and two strict central points
give a continuous angle bound; an exact square identity closes the whole
remaining scalar interval. No angle subdivision or pose enclosure enters. -/
namespace N12Compact.CentralLeftWallNegative

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

/-- The two strict points span more than one unit in V if the central
slope reaches 4/5. The original side cap therefore excludes that slope. -/
theorem central_tilt (A : OpenSquare) (normal : Normal A.c A.s)
    (cap : A.side≤1001/1000)
    (west : A.Inside 1 2) (low : A.Inside 2 (3/2)) :
    A.s<(4/5)*A.c := by
  have bounds := normal_bounds normal
  have ac : 0<A.c := by linarith only [bounds.1]
  have span : A.s+A.c/2<(1001/1000:ℝ) := by
    nlinarith only [west.2.2.2,low.2.2.1,cap]
  by_contra no
  have wide : (4/5)*A.c≤A.s := le_of_not_gt no
  have cross := mul_nonneg ac.le (sub_nonneg.mpr wide)
  have squareOrder := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0≤A.c+A.s by linarith only [ac,normal.1])
  have smallSquare := mul_pos (sub_pos.mpr span)
    (show 0<(1001/1000:ℝ)+(A.s+A.c/2) by linarith only [ac,normal.1])
  nlinarith only [normal.2.2,cross,squareOrder,smallSquare,sq_pos_of_pos ac]

/-- The only delicate range is d<.914. There the exact identity is
`(1-d)(1-.8d)+.6(d-.914)=.8(d-.75)^2+.0016`. -/
theorem margin {C S d t : ℝ} (hc : 0≤C) (hs : S≤(4/5)*C)
    (hd : 0≤d) (hd1 : d≤1) (ht : 0≤t) (ht6 : t≤3/5) :
    0≤(1-d)*(C-S*d)+C*t*(d-457/500) := by
  have slope := mul_nonneg (mul_nonneg (sub_nonneg.mpr hd1) hd)
    (sub_nonneg.mpr hs)
  by_cases upper : (457/500:ℝ)≤d
  · have first := mul_nonneg hc
      (mul_nonneg (sub_nonneg.mpr hd1)
        (show 0≤1-(4/5)*d by linarith only [hd1]))
    have second := mul_nonneg (mul_nonneg hc ht) (sub_nonneg.mpr upper)
    nlinarith only [slope,first,second]
  · have replacement := mul_nonneg hc
      (mul_nonneg (show 0≤457/500-d by linarith only [upper])
        (sub_nonneg.mpr ht6))
    have square := mul_nonneg hc (sq_nonneg (d-3/4))
    have identity :
        C*((1-d)*(1-(4/5)*d)+(3/5)*(d-457/500)) =
          (4/5)*C*(d-3/4)^2+C/625 := by ring
    nlinarith only [slope,replacement,square,identity,hc]

/-- Full W containment and the two true face caps exclude separation on
A's transverse axis. The point (1,2) is retained as an explicit premise. -/
theorem not_central_axis (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (side : 1<W.side)
    (sideCap : A.side≤1001/1000)
    (west : A.Inside 1 2) (low : A.Inside 2 (3/2))
    (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (113/50))
    (missingTop : ¬W.Inside (457/500) 3)
    (missingFar : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    ¬ A.loV+A.side≤lower W (-A.s) A.c := by
  have missing : ¬W.Inside 1 2 := fun w => apart 1 2 ⟨west,w⟩
  obtain ⟨_,capV,wall⟩ := LeftWallNegativeFaces.faces W t ws wn side box
    marker point missing missingTop
  have tilt := (LeftWallNegativeFaces.lower_face_and_tilt W t ws wn side box
    marker point missing missingTop missingFar).2
  have slope := central_tilt A an sideCap west low
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have ac : 0<A.c := by linarith only [ab.1]
  have dc : 0<W.c := by linarith only [wb.1]
  let h := A.s*W.c+A.c*t
  let k := A.c*W.c-A.s*t
  let B := A.c+A.s*W.c^2+A.c*W.c*t
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dc.le) (mul_nonneg ac.le wn.1)
  have kp : 0≤k := by
    have first := mul_nonneg dc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have bp : 0<B := by
    have first := mul_nonneg an.1 (sq_nonneg W.c)
    have second := mul_nonneg (mul_nonneg ac.le dc.le) wn.1
    dsimp [B]
    nlinarith only [ac,first,second]
  have form : lower W (-A.s) A.c = -h*(W.loU+W.side)+k*W.loV := by
    rw [lower_negative_nonpos W t (-A.s) A.c ws
      (by dsimp [h] at hp; nlinarith only [hp])
      (by dsimp [k] at kp; nlinarith only [kp])]
    dsimp [h,k]
    ring
  intro sep
  rw [form] at sep
  have scaledSep := mul_le_mul_of_nonneg_left sep dc.le
  have scaledWall := mul_nonneg hp (sub_nonneg.mpr wall)
  have identity :
      W.c*(-h*(W.loU+W.side)+k*W.loV)+
        h*(W.c*(W.loU+W.side)+t*(W.loV+W.side)-W.side*(W.c+t)) =
      A.c*(W.loV+W.side)-W.side*B := by
    dsimp [h,k,B]
    linear_combination (A.c*W.loV)*wn.2.2
  have combined : W.c*(A.loV+A.side)≤
      A.c*(W.loV+W.side)-W.side*B := by
    nlinarith only [scaledSep,scaledWall,identity]
  have top := mul_nonneg ac.le (sub_nonneg.mpr capV)
  have width := mul_pos (sub_pos.mpr side) bp
  have target := mul_lt_mul_of_pos_left west.2.2.2 dc
  have scalar := margin ac.le slope.le dc.le wb.2.1 wn.1 tilt.le
  dsimp [B] at combined width
  nlinarith only [combined,top,width,target,scalar]

/-- With actual congruence and disjointness, precisely the directed W-U
separator remains throughout the negative wall sector. -/
theorem wall_axis (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<W.side)
    (sideCap : A.side≤1001/1000)
    (west : A.Inside 1 2) (low : A.Inside 2 (3/2))
    (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (113/50))
    (missingTop : ¬W.Inside (457/500) 3)
    (missingFar : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    W.loU+W.side≤lower A W.c W.s := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have alternatives := CentralLeftWallSeparation.negative_alternatives A W
    (by linarith only [ab.1]) an.1 (by linarith only [wb.1])
    (by rw [ws]; linarith only [wn.1]) same west marker point apart
  exact alternatives.resolve_left (not_central_axis A W t an wn ws side sideCap
    west low box marker point missingTop missingFar apart)

end N12Compact.CentralLeftWallNegative
