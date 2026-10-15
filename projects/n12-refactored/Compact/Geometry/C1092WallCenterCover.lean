import S12.TriangleCover
import Compact.Geometry.C1092WallPolynomial
import Compact.Geometry.C1092WallCenterRegion
import Mathlib.Tactic.FieldSimp

/-! Source-only parametric replacement for the generated C1092 center-cover
polygons. The core cap argument uses two disks and no finite geometry data.
This file has not been replayed by Lean. -/

namespace N12Compact.C1092WallCenterCover

open S12 S12Pilot

/-- The closed Euclidean disk of radius one half around the center lies
strictly inside any square whose side is greater than one. -/
theorem half_disk_inside (q : OpenSquare) (ha : 1 < q.side) (x y : ℝ)
    (hd : (x-centerX q)^2+(y-centerY q)^2 ≤ 1/4) : q.Inside x y := by
  have hscaled : (2*(x-centerX q))^2+(2*(y-centerY q))^2 ≤ 1 := by
    nlinarith only [hd]
  obtain ⟨hu0,hu1,hv0,hv1⟩ := short_projections q _ _ hscaled
  apply (inside_centered_iff q x y).mpr
  dsimp [InBands]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [ha,hu0,hu1,hv0,hv1]

/-- A cap above the segment from `(0,0)` to `(d,H)` and below `w=h`
is covered by the radius-one-half disks at those two endpoints. The only
nontrivial scalar bound is the perpendicular-bisector test on its top edge.
All boundaries are retained. -/
theorem cap_two_disks (d H h v w : ℝ)
    (hd : 0 < d) (hH : 0 < H) (hhH : h ≤ H)
    (hv : 0 ≤ v) (hcap : H*v ≤ d*w) (hw : w ≤ h)
    (hshort : d^2+H^2 ≤ 1)
    (hdisk : (d^2+H^2-2*H*h)^2+4*d^2*h^2 ≤ d^2) :
    v^2+w^2 ≤ 1/4 ∨ (d-v)^2+(H-w)^2 ≤ 1/4 := by
  have hw0 : 0 ≤ w := by
    have hnonneg : 0 ≤ d*w := le_trans (mul_nonneg hH.le hv) hcap
    exact nonneg_of_mul_nonneg_right hnonneg hd
  have hvd : v ≤ d := by
    have hp := mul_le_mul_of_nonneg_left (hw.trans hhH) hd.le
    by_contra h
    have hp' := mul_pos hH (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hcap,hp,hp']
  by_cases hhalf : w ≤ H/2
  · have hvhalf : v ≤ d/2 := by
      have hp := mul_le_mul_of_nonneg_left hhalf hd.le
      by_contra h
      have hp' := mul_pos hH (sub_pos.mpr (lt_of_not_ge h))
      nlinarith only [hcap,hp,hp']
    have hv2 := mul_nonneg (sub_nonneg.mpr hvhalf)
      (show 0 ≤ d/2+v by linarith)
    have hw2 := mul_nonneg (sub_nonneg.mpr hhalf)
      (show 0 ≤ H/2+w by linarith)
    exact Or.inl (by nlinarith only [hv2,hw2,hshort])
  · have hhalf' : H/2 ≤ w := (lt_of_not_ge hhalf).le
    let J := fun z : ℝ => (d^2+H^2)*((2*z-H)^2+d^2)
    have hmono : J w ≤ J h := by
      have hp := mul_nonneg
        (mul_nonneg (by nlinarith [sq_nonneg d,sq_nonneg H] : 0 ≤ 4*(d^2+H^2))
          (sub_nonneg.mpr hw))
        (show 0 ≤ h+w-H by linarith)
      have hid : J h-J w = 4*(d^2+H^2)*(h-w)*(h+w-H) := by dsimp [J]; ring
      linarith only [hid,hp]
    have hjh : J h ≤ d^2 := by
      have hid : J h = (d^2+H^2-2*H*h)^2+4*d^2*h^2 := by dsimp [J]; ring
      simpa only [hid] using hdisk
    have hjw : J w ≤ d^2 := hmono.trans hjh
    by_cases hnear : 2*d*v+2*H*w ≤ d^2+H^2
    · have hlow : 0 ≤ d^2+H^2-2*H*w-2*d*v := by linarith
      have hhigh : 0 ≤ d^2+H^2-2*H*w+2*d*v := by
        have hp := mul_nonneg hd.le hv
        linarith
      have hsquare := mul_nonneg hlow hhigh
      have hbound : 4*d^2*(v^2+w^2) ≤ J w := by
        dsimp [J]; nlinarith only [hsquare]
      have hprod : 0 ≤ d^2*(1-4*(v^2+w^2)) := by
        nlinarith only [hbound,hjw]
      have h := nonneg_of_mul_nonneg_right hprod (sq_pos_of_pos hd)
      exact Or.inl (by linarith only [h])
    · have hnear' : d^2+H^2 ≤ 2*d*v+2*H*w := (lt_of_not_ge hnear).le
      have hlow : 0 ≤ d^2-H^2+2*H*w-2*d*(d-v) := by nlinarith only [hnear']
      have hhigh : 0 ≤ d^2-H^2+2*H*w+2*d*(d-v) := by
        have hp := mul_nonneg hd.le (sub_nonneg.mpr hvd)
        nlinarith only [hlow,hp]
      have hsquare := mul_nonneg hlow hhigh
      have hbound : 4*d^2*((d-v)^2+(H-w)^2) ≤ J w := by
        dsimp [J]; nlinarith only [hsquare]
      have hprod : 0 ≤ d^2*(1-4*((d-v)^2+(H-w)^2)) := by
        nlinarith only [hbound,hjw]
      have h := nonneg_of_mul_nonneg_right hprod (sq_pos_of_pos hd)
      exact Or.inr (by linarith only [h])

/-- Physical consequence of the cap lemma. No information about the
square's orientation is required. -/
theorem cap_forces_point (q : OpenSquare) (ha : 1 < q.side)
    (x y d H h : ℝ) (hd : 0 < d) (hH : 0 < H) (hhH : h ≤ H)
    (hx : x ≤ centerX q)
    (hcap : H*(centerX q-x) ≤ d*(centerY q-y))
    (hy : centerY q-y ≤ h) (hshort : d^2+H^2 ≤ 1)
    (hdisk : (d^2+H^2-2*H*h)^2+4*d^2*h^2 ≤ d^2)
    (outside : ¬ q.Inside (x+d) (y+H)) : q.Inside x y := by
  have h := cap_two_disks d H h (centerX q-x) (centerY q-y)
    hd hH hhH (sub_nonneg.mpr hx) hcap hy hshort hdisk
  rcases h with h | h
  · exact half_disk_inside q ha x y (by nlinarith only [h])
  · exact False.elim (outside (half_disk_inside q ha (x+d) (y+H)
      (by nlinarith only [h])))

/-- The two short triangles BDP and PDF cover the region between BD and
PF to the right of P. This statement is parametric in P; its barycentric
coordinates are given explicitly rather than serialized as polygons. -/
theorem below_triangles_forces_point (q : OpenSquare) (ha : 1 < q.side)
    (x y : ℝ) (hxb : 457/500 ≤ x) (hxa : x < 33/20)
    (harea : 0 < (92/125)*(y-1)-(13/20)*(x-457/500))
    (hx : x ≤ centerX q) (hX : centerX q ≤ 33/20)
    (hbottom : (325/368)*centerX q+1419/7360 ≤ centerY q)
    (htop : (33/20-x)*(centerY q-y) ≤ (47/20-y)*(centerX q-x))
    (hBP : (x-457/500)^2+(y-1)^2 ≤ 1)
    (hDP : (x-33/20)^2+(y-33/20)^2 ≤ 1)
    (hFP : (x-33/20)^2+(y-47/20)^2 ≤ 1)
    (outsideB : ¬ q.Inside (457/500) 1)
    (outsideD : ¬ q.Inside (33/20) (33/20))
    (outsideF : ¬ q.Inside (33/20) (47/20)) : q.Inside x y := by
  by_contra outsideP
  let X := centerX q
  let Y := centerY q
  let d := 33/20-x
  let area := (92/125)*(y-1)-(13/20)*(x-457/500)
  have hd : 0 < d := by dsimp [d]; linarith only [hxa]
  have hA : 0 < area := harea
  by_cases hmiddle : d*(Y-y) ≤ (33/20-y)*(X-x)
  · let NB := d*(33/20-Y)-(33/20-y)*(33/20-X)
    let ND := (y-1)*(X-457/500)-(x-457/500)*(Y-1)
    let NP := (92/125)*(Y-1)-(13/20)*(X-457/500)
    have hNB : 0 ≤ NB := by dsimp [NB,d] at *; nlinarith only [hmiddle]
    have hNP : 0 ≤ NP := by dsimp [NP,X,Y]; linarith only [hbottom]
    have hND : 0 ≤ ND := by
      have hp := mul_nonneg (show 0 ≤ X-x by dsimp [X]; linarith only [hx]) hA.le
      have hb := mul_nonneg (sub_nonneg.mpr hxb) hNB
      have hid : d*ND = (X-x)*area+(x-457/500)*NB := by
        dsimp [d,ND,area,NB]; ring
      have hprod : 0 ≤ d*ND := by rw [hid]; exact add_nonneg hp hb
      exact nonneg_of_mul_nonneg_right hprod hd
    have hsum : NB/area+ND/area+NP/area=1 := by
      field_simp [ne_of_gt hA]
      dsimp [NB,ND,NP,area,d]
      ring
    have hXeq : NB/area*(457/500)+ND/area*(33/20)+NP/area*x=centerX q := by
      field_simp [ne_of_gt hA]
      dsimp [NB,ND,NP,area,d,X,Y]
      ring
    have hYeq : NB/area*1+ND/area*(33/20)+NP/area*y=centerY q := by
      field_simp [ne_of_gt hA]
      dsimp [NB,ND,NP,area,d,X,Y]
      ring
    have hh := triangle_nonavoidance q ha (457/500) 1 (33/20) (33/20) x y
      (NB/area) (ND/area) (NP/area)
      (div_nonneg hNB hA.le) (div_nonneg hND hA.le) (div_nonneg hNP hA.le)
      hsum hXeq hYeq (by norm_num)
      (by nlinarith only [hBP]) (by nlinarith only [hDP])
    exact hh.elim outsideB (fun h => h.elim outsideD outsideP)
  · let NF := d*(Y-y)-(33/20-y)*(X-x)
    let ND := (47/20-y)*(X-x)-d*(Y-y)
    let den := d*(7/10)
    have hden : 0 < den := mul_pos hd (by norm_num)
    have hNF : 0 ≤ NF := by dsimp [NF]; linarith only [lt_of_not_ge hmiddle]
    have hND : 0 ≤ ND := by dsimp [ND,d,X,Y]; linarith only [htop]
    have hNP : 0 ≤ 33/20-X := by dsimp [X]; linarith only [hX]
    have hsum : (33/20-X)/d+ND/den+NF/den=1 := by
      field_simp [ne_of_gt hd,ne_of_gt hden]
      dsimp [ND,NF,den,d]
      ring
    have hXeq : (33/20-X)/d*x+ND/den*(33/20)+NF/den*(33/20)=centerX q := by
      field_simp [ne_of_gt hd,ne_of_gt hden]
      dsimp [ND,NF,den,d,X,Y]
      ring
    have hYeq : (33/20-X)/d*y+ND/den*(33/20)+NF/den*(47/20)=centerY q := by
      field_simp [ne_of_gt hd,ne_of_gt hden]
      dsimp [ND,NF,den,d,X,Y]
      ring
    have hh := triangle_nonavoidance q ha x y (33/20) (33/20) (33/20) (47/20)
      ((33/20-X)/d) (ND/den) (NF/den)
      (div_nonneg hNP hd.le) (div_nonneg hND hden.le) (div_nonneg hNF hden.le)
      hsum hXeq hYeq hDP hFP (by norm_num)
    exact hh.elim outsideP (fun h => h.elim outsideD outsideF)

open C1092WallPolynomial in
theorem target_cover_arithmetic (i : Fin 12) :
    let x := targetX i
    let y := targetY i
    457/500 ≤ x ∧ x ≤ 1 ∧ y ≤ 2 ∧
    0 < (92/125)*(y-1)-(13/20)*(x-457/500) ∧
    (x-457/500)^2+(y-1)^2 ≤ 1 ∧
    (x-33/20)^2+(y-33/20)^2 ≤ 1 ∧
    (x-33/20)^2+(y-47/20)^2 ≤ 1 ∧
    ((33/20-x)^2+(47/20-y)^2-2*(47/20-y)*(2-y))^2+
      4*(33/20-x)^2*(2-y)^2 ≤ (33/20-x)^2 := by
  fin_cases i <;> norm_num [targetX,targetY]

open C1092WallPolynomial in
/-- Every original marker12 owner in the closed branch X≥1,Y≤2 contains
all twelve targets. This supplies the complementary physical entrance;
the X≤1 branch is the separate uniform wall-polynomial calculation. -/
theorem original_right_branch_point (q : OpenSquare) (ha : 1 < q.side)
    (cap : q.side ≤ 1001/1000) (owned : q.Inside (457/500) 2)
    (outside0 : ¬ q.Inside 1 (457/500))
    (outside1 : ¬ q.Inside (457/500) 1)
    (outside8 : ¬ q.Inside (33/20) (33/20))
    (outside11 : ¬ q.Inside (33/20) (47/20))
    (hx : 1 ≤ centerX q) (hy : centerY q ≤ 2) (i : Fin 12) :
    q.Inside (targetX i) (targetY i) := by
  obtain ⟨hxa,hbottom⟩ := C1092WallCenterRegion.original_marker_entrance q ha cap
    owned outside0 outside1 outside8 hx hy
  obtain ⟨hxb,hx1,hy2,harea,hBP,hDP,hFP,hdisk⟩ := target_cover_arithmetic i
  have hd : 0 < 33/20-targetX i := by linarith only [hx1]
  have hH : 0 < 47/20-targetY i := by linarith only [hy2]
  by_cases htop : (33/20-targetX i)*(centerY q-targetY i) ≤
      (47/20-targetY i)*(centerX q-targetX i)
  · exact below_triangles_forces_point q ha _ _ hxb (by linarith only [hx1])
      harea (by linarith only [hx,hx1]) hxa hbottom htop hBP hDP hFP
      outside1 outside8 outside11
  · apply cap_forces_point q ha (targetX i) (targetY i)
      (33/20-targetX i) (47/20-targetY i) (2-targetY i) hd hH
      (by linarith) (by linarith only [hx,hx1])
      (le_of_lt (lt_of_not_ge htop)) (by linarith only [hy])
      (by nlinarith only [hFP]) hdisk
    have hxeq : targetX i+(33/20-targetX i) = (33/20:ℝ) := by ring
    have hyeq : targetY i+(47/20-targetY i) = (47/20:ℝ) := by ring
    simpa only [hxeq,hyeq] using outside11

#print axioms cap_two_disks
#print axioms cap_forces_point
#print axioms original_right_branch_point

end N12Compact.C1092WallCenterCover
