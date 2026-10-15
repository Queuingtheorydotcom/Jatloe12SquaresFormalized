import Compact.Geometry.NegativeWallTopSeed

/-! The true upper corner marker, rather than the unavailable point
(1,2.88), bounds the negative wall's upper face. The actual foreign NW
central marker eliminates the other possible face. The valid lower-face
bound remains explicit so its original geometric derivation is visible. -/
namespace N12Compact.NegativeWallMarkerCap

open S12 S12Pilot FourSquareAnchors
open C977CornerCubic C977NegativeCorner

/-- The actual foreign NW marker also caps the U face. Its V projection
is within one side of the genuine lower face, so it cannot escape there. -/
theorem upper_u (W : OpenSquare) (t : ℝ)
    (wn : Normal W.c t) (ws : W.s=-t) (side : 1<W.side)
    (marker : W.Inside (457/500) 2)
    (lower : (19/25)*t+(187/100)*W.c≤W.loV)
    (northwest : ¬W.Inside (33/20) (47/20)) :
    W.loU+W.side≤(33/20)*W.c-(47/20)*t := by
  have wb := normal_bounds wn
  have hc : 0<W.c := by linarith only [wb.1]
  have wm := (negative_bands W t _ _ ws).mp marker
  have nUlo : W.loU<(33/20)*W.c-(47/20)*t := by
    nlinarith only [wm.1,hc,wn.1,wn.2.1]
  have nVlo : W.loV<(33/20)*t+(47/20)*W.c := by
    nlinarith only [wm.2.2.1,wn.1,hc]
  have short : (89/100)*t+(12/25)*W.c≤137/140 := by
    linarith only [wn.2.1,wb.2.2.2.2.2]
  have nVhi : (33/20)*t+(47/20)*W.c<W.loV+W.side := by
    linarith only [lower,short,side]
  apply le_of_not_gt
  intro nUhi
  exact northwest ((negative_bands W t _ _ ws).mpr ⟨nUlo,nUhi,nVlo,nVhi⟩)

/-- Actual marker exclusion forces the upper V face. No stronger corner
reach, numerical pose interval, or missing (1,2.88) premise is used. -/
theorem upper_face (W : OpenSquare) (t : ℝ)
    (wn : Normal W.c t) (ws : W.s=-t) (side : 1<W.side)
    (marker : W.Inside (457/500) 2)
    (lower : (19/25)*t+(187/100)*W.c≤W.loV)
    (northwest : ¬W.Inside (33/20) (47/20))
    (top : ¬W.Inside (457/500) 3) :
    W.loV+W.side≤(457/500)*t+3*W.c := by
  have wb := normal_bounds wn
  have hc : 0<W.c := by linarith only [wb.1]
  have wm := (negative_bands W t _ _ ws).mp marker
  have lowerU : W.loU<(457/500)*W.c-3*t := by
    apply lt_of_not_ge
    intro forbidden
    have nUlo : W.loU<(33/20)*W.c-(47/20)*t := by
      nlinarith only [wm.1,hc,wn.1,wn.2.1]
    have projection := (short_projections W (92/125) (-13/20) (by norm_num)).2.1
    rw [ws] at projection
    have nUhi : (33/20)*W.c-(47/20)*t<W.loU+W.side := by
      nlinarith only [forbidden,projection,side]
    have nVlo : W.loV<(33/20)*t+(47/20)*W.c := by
      nlinarith only [wm.2.2.1,wn.1,hc]
    have nVhi : W.loV+W.side≤(33/20)*t+(47/20)*W.c := by
      apply le_of_not_gt
      intro inside
      apply northwest
      exact (negative_bands W t _ _ ws).mpr ⟨nUlo,nUhi,nVlo,inside⟩
    have span : W.side≤(89/100)*t+(12/25)*W.c := by
      linarith only [lower,nVhi]
    have short : (89/100)*t+(12/25)*W.c≤137/140 := by
      linarith only [wn.2.1,wb.2.2.2.2.2]
    linarith only [span,short,side]
  apply le_of_not_gt
  intro upper
  apply top
  apply (negative_bands W t _ _ ws).mpr
  exact ⟨lowerU,by nlinarith only [wm.2.1,wn.1],
    by nlinarith only [wm.2.2.1,hc],upper⟩

/-- The genuine two faces leave a larger wall sector than the discarded
2.88 cap. The rational tangent gives a near-sharp upper sine bound. -/
theorem sector {d t a lo hi : ℝ} (wn : Normal d t) (side : 1<a)
    (width : hi=lo+a) (lower : (19/25)*t+(187/100)*d≤lo)
    (upper : hi≤(457/500)*t+3*d) :
    a≤(77/500)*t+(113/100)*d ∧ t<825/1387 ∧ t<3/5 ∧ 4/5<d := by
  have span : a≤(77/500)*t+(113/100)*d := by
    linarith only [width,lower,upper]
  have dotSquare : ((4/5)*d+(3/5)*t)^2≤1 := by
    nlinarith only [wn.2.2,sq_nonneg (3*d-4*t)]
  have dot : (4/5)*d+(3/5)*t≤1 := by
    nlinarith only [dotSquare,sq_nonneg ((4/5)*d+(3/5)*t-1)]
  have sine : t<825/1387 := by linarith only [span,dot,side]
  have small : t<3/5 := by linarith only [sine]
  have wb := normal_bounds wn
  have square := mul_pos (sub_pos.mpr small)
    (show 0<3/5+t by linarith only [wn.1])
  have wide : 4/5<d := by
    nlinarith only [square,wn.2.2,wb.1,sq_nonneg (d-4/5)]
  exact ⟨span,sine,small,wide⟩

#print axioms upper_face
#print axioms upper_u
#print axioms sector
end N12Compact.NegativeWallMarkerCap
