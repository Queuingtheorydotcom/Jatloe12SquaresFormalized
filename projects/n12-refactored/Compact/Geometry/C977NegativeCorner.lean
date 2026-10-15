import Compact.Geometry.C977CornerHalfAngle
import Compact.Geometry.C977CornerSectorBounds
import Compact.Geometry.C977CornerSupportBounds
import Compact.Geometry.C977SingletonSeparation
import S12.Convex

/-! Full-square support and the actual foreign segment for the negative
corner sector. No square is replaced by an axis-aligned virtual wall. -/
namespace N12Compact.C977NegativeCorner

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds
open C977CornerSupportBounds

theorem negative_bands (q : OpenSquare) (t x y : ℝ) (hs : q.s = -t) :
    q.Inside x y ↔
      q.loU < q.c*x-t*y ∧ q.c*x-t*y < q.loU+q.side ∧
      q.loV < t*x+q.c*y ∧ t*x+q.c*y < q.loV+q.side := by
  simp only [OpenSquare.Inside, InBands, hs, neg_neg, neg_mul, sub_eq_add_neg]

theorem upper_in_bands (q : OpenSquare) (nx ny : ℝ) :
    upper q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)+
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold upper supportRadius centerX centerY
  ring

theorem lower_in_bands (q : OpenSquare) (nx ny : ℝ) :
    lower q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)-
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold lower supportRadius centerX centerY
  ring

theorem upper_negative_pos (q : OpenSquare) (t nx ny : ℝ) (hs : q.s = -t)
    (hu : 0 ≤ nx*q.c-ny*t) (hv : 0 ≤ nx*t+ny*q.c) :
    upper q nx ny = (nx*q.c-ny*t)*(q.loU+q.side)+
      (nx*t+ny*q.c)*(q.loV+q.side) := by
  rw [upper_in_bands, hs]
  have u : nx*q.c+ny*(-t)=nx*q.c-ny*t := by ring
  have v : -nx*(-t)+ny*q.c=nx*t+ny*q.c := by ring
  rw [u,v,abs_of_nonneg hu,abs_of_nonneg hv]
  ring

theorem upper_negative_nonpos (q : OpenSquare) (t nx ny : ℝ) (hs : q.s = -t)
    (hu : nx*q.c-ny*t ≤ 0) (hv : 0 ≤ nx*t+ny*q.c) :
    upper q nx ny = (nx*q.c-ny*t)*q.loU+
      (nx*t+ny*q.c)*(q.loV+q.side) := by
  rw [upper_in_bands, hs]
  have u : nx*q.c+ny*(-t)=nx*q.c-ny*t := by ring
  have v : -nx*(-t)+ny*q.c=nx*t+ny*q.c := by ring
  rw [u,v,abs_of_nonpos hu,abs_of_nonneg hv]
  ring

theorem lower_negative_pos (q : OpenSquare) (t nx ny : ℝ) (hs : q.s = -t)
    (hu : 0 ≤ nx*q.c-ny*t) (hv : 0 ≤ nx*t+ny*q.c) :
    lower q nx ny = (nx*q.c-ny*t)*q.loU+(nx*t+ny*q.c)*q.loV := by
  rw [lower_in_bands, hs]
  have u : nx*q.c+ny*(-t)=nx*q.c-ny*t := by ring
  have v : -nx*(-t)+ny*q.c=nx*t+ny*q.c := by ring
  rw [u,v,abs_of_nonneg hu,abs_of_nonneg hv]
  ring

theorem lower_negative_nonpos (q : OpenSquare) (t nx ny : ℝ) (hs : q.s = -t)
    (hu : nx*q.c-ny*t ≤ 0) (hv : 0 ≤ nx*t+ny*q.c) :
    lower q nx ny = (nx*q.c-ny*t)*(q.loU+q.side)+(nx*t+ny*q.c)*q.loV := by
  rw [lower_in_bands, hs]
  have u : nx*q.c+ny*(-t)=nx*q.c-ny*t := by ring
  have v : -nx*(-t)+ny*q.c=nx*t+ny*q.c := by ring
  rw [u,v,abs_of_nonpos hu,abs_of_nonneg hv]
  ring

/-- The actual bottom wall, missing corner and owned singleton points
give a strict bound on the true transverse face. -/
theorem corner_face (O : OpenSquare) (t : ℝ) (hs : O.s = -t)
    (normal : Normal O.c t) (side : 1 < O.side) (box : InsideContainer O)
    (marker : O.Inside 1 (457/500)) (near : O.Inside (28/25) 1)
    (far : O.Inside (187/100) (19/25)) (missing : ¬ O.Inside 1 1) :
    O.c-t ≤ O.loU ∧ t*(O.loU+O.side) ≤ O.c*O.loV ∧
      boundary O.c t < O.loV+O.side := by
  have b := normal_bounds normal
  have hc : 0 < O.c := by linarith only [b.1]
  have m := (negative_bands O t _ _ hs).mp marker
  have n := (negative_bands O t _ _ hs).mp near
  have f := (negative_bands O t _ _ hs).mp far
  have corner : O.c-t ≤ O.loU := by
    by_contra no
    apply missing
    apply (negative_bands O t 1 1 hs).mpr
    refine ⟨by nlinarith only [no], ?_, ?_, ?_⟩
    · nlinarith only [f.2.1, hc, normal.1]
    · nlinarith only [m.2.2.1, hc]
    · nlinarith only [n.2.2.2, normal.1]
  have bottom := ThreeSquare.bottom_wall O hc.le box
  have sabs : |O.s|=t := by rw [hs, abs_neg, abs_of_nonneg normal.1]
  have wall : t*(O.loU+O.side) ≤ O.c*O.loV := by
    rw [sabs] at bottom
    dsimp [centerY] at bottom
    rw [hs] at bottom
    nlinarith only [bottom]
  have multiply : O.c*boundary O.c t=O.c+O.c*t+t*(1-t) := by
    dsimp [boundary]; field_simp [hc.ne']; ring
  have wc := mul_nonneg normal.1 (sub_nonneg.mpr corner)
  have strict := mul_pos (sub_pos.mpr side)
    (show 0 < O.c+t by linarith only [hc, normal.1])
  have scaled : 0 < O.c*(O.loV+O.side-boundary O.c t) := by
    nlinarith only [multiply, wall, wc, strict]
  have gap := pos_of_mul_pos_right scaled hc.le
  exact ⟨corner, wall, by linarith only [gap]⟩

/-- The final forbidden section is a point of a real foreign square,
including the two closed segment endpoints, all strictly inside it. -/
theorem foreign_segment_overlap (A L : OpenSquare) (T : ℝ) (hs : A.s = -T)
    (normal : Normal A.c T) (tilt : 0 < T) (side : 1 < A.side)
    (crossD : A.Inside 2 (87/50)) (crossE : A.Inside (87/50) 2)
    (top : A.loV+A.side ≤ 2*(A.c+T))
    (left : A.c*A.loU+T*A.loV < 1)
    (near : A.loU < A.c-(28/25)*T)
    (lN : L.Inside 1 (28/25)) (lW : L.Inside 1 (87/50)) :
    ∃ x y, A.Inside x y ∧ L.Inside x y := by
  have b := normal_bounds normal
  have hc : 0 < A.c := by linarith only [b.1]
  have d := (negative_bands A T _ _ hs).mp crossD
  have e := (negative_bands A T _ _ hs).mp crossE
  let lo := (A.loV-T)/A.c
  let hi := (A.c-A.loU)/T
  have ordered : lo < hi := by
    apply (div_lt_div_iff₀ hc tilt).mpr
    nlinarith only [left, normal.2.2]
  have nearHi : (28/25 : ℝ) < hi := by
    apply (lt_div_iff₀ tilt).mpr
    linarith only [near]
  have lowFar : lo < 87/50 := by
    apply (div_lt_iff₀ hc).mpr
    have short : T+(13/50)*A.c ≤ 9/10 := by
      linarith only [normal.2.1, b.2.2.2.2.2]
    linarith only [short, top, side]
  have gap : max lo (28/25) < min hi (87/50) := by
    apply max_lt_iff.mpr
    exact ⟨lt_min ordered lowFar, lt_min nearHi (by norm_num)⟩
  let y := (max lo (28/25)+min hi (87/50))/2
  have yl : max lo (28/25) < y := by dsimp [y]; linarith only [gap]
  have yu : y < min hi (87/50) := by dsimp [y]; linarith only [gap]
  have ylo : lo < y := lt_of_le_of_lt (le_max_left _ _) yl
  have yhi : y < hi := lt_of_lt_of_le yu (min_le_left _ _)
  have yN : (28/25 : ℝ) < y := lt_of_le_of_lt (le_max_right _ _) yl
  have yW : y < 87/50 := lt_of_lt_of_le yu (min_le_right _ _)
  have aInside : A.Inside 1 y := by
    apply (negative_bands A T 1 y hs).mpr
    have first := (lt_div_iff₀ tilt).mp yhi
    have third := (div_lt_iff₀ hc).mp ylo
    have yNprod := mul_lt_mul_of_pos_left yN tilt
    have yWprod := mul_lt_mul_of_pos_left yW hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [first, third, yNprod, yWprod, d.2.1, e.2.2.2,
        hc, normal.1, normal.2.1]
  let lambda := (50/31 : ℝ)*(y-28/25)
  have lInside := inside_segment L 1 (28/25) 1 (87/50) lambda lN lW
    (by dsimp [lambda]; linarith only [yN])
    (by dsimp [lambda]; linarith only [yW])
  refine ⟨1,y,aInside,?_⟩
  convert lInside using 1 <;> dsimp [lambda] <;> ring

/-- Original complete squares force the central point in the continuous
negative/negative sector. The left singleton is used as an actual foreign
strict segment. All square-boundary contacts are allowed. The hypotheses
on signed frames are explicit and are not a new orientation-cover claim. -/
theorem point (O A L : OpenSquare) (t T : ℝ)
    (hsO : O.s = -t) (hsA : A.s = -T)
    (normalO : Normal O.c t) (normalA : Normal A.c T)
    (side : 1 < O.side) (same : O.side = A.side)
    (box : InsideContainer O)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25)) (corner : ¬ O.Inside 1 1)
    (aP : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aE : A.Inside (87/50) 2)
    (lN : L.Inside 1 (28/25)) (lW : L.Inside 1 (87/50))
    (apartOA : ∀ x y, ¬ (O.Inside x y ∧ A.Inside x y))
    (apartAL : ∀ x y, ¬ (A.Inside x y ∧ L.Inside x y)) :
    A.Inside 2 2 := by
  classical
  have bo := normal_bounds normalO
  have ba := normal_bounds normalA
  have hc : 0<O.c := by linarith only [bo.1]
  have hC : 0<A.c := by linarith only [ba.1]
  have sideA : 1<A.side := by rwa [← same]
  have face := corner_face O t hsO normalO side box oM oN oF corner
  have hK : 0<O.c*A.c+t*T := positive_dot normalO normalA
  have p := (negative_bands A T _ _ hsA).mp aP
  have d := (negative_bands A T _ _ hsA).mp aD
  have e := (negative_bands A T _ _ hsA).mp aE
  by_contra missing
  have top : A.loV+A.side ≤ 2*(A.c+T) := by
    by_contra no
    apply missing
    apply (negative_bands A T 2 2 hsA).mpr
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [e.1, d.2.1, p.2.2.1, no, hC, normalA.1]
  have tilt : 0<T := by nlinarith only [top, e.2.2.2]
  have alternatives := C977SingletonSeparation.bottom_alternatives O A
    hc (by rw [hsO]; linarith only [normalO.1])
    (by rw [hsO]; linarith only [normalO.2.1])
    hC (by rw [hsA]; linarith only [normalA.1])
    (by rw [hsA]; linarith only [normalA.2.1])
    same oN oF aP aD apartOA
  have actual : O.loV+O.side ≤ lower A t O.c ∨ upper O T A.c ≤ A.loV := by
    simpa only [hsO, hsA, neg_neg] using alternatives
  rcases actual with oa | aa
  · by_cases low : O.c*T-t*A.c ≤ 0
    · have support : lower A t O.c =
          -(O.c*T-t*A.c)*A.loU+(O.c*A.c+t*T)*A.loV := by
        have formula := lower_negative_pos A T t O.c hsA
          (by linarith only [low]) (by nlinarith only [hK])
        convert formula using 1 <;> ring
      have bound := corner_axis_below (U := A.loU) (V := A.loV) normalO normalA sideA
        (by nlinarith only [e.1]) top low
      rw [support] at oa
      linarith only [face.2.2, oa, bound]
    · have sign : 0<O.c*T-t*A.c := lt_of_not_ge low
      have support : lower A t O.c =
          -(O.c*T-t*A.c)*(A.loU+A.side)+(O.c*A.c+t*T)*A.loV := by
        have formula := lower_negative_nonpos A T t O.c hsA
          (by linarith only [sign]) (by nlinarith only [hK])
        convert formula using 1 <;> ring
      have sep : boundary O.c t <
          -(O.c*T-t*A.c)*(A.loU+A.side)+(O.c*A.c+t*T)*A.loV := by
        rw [support] at oa
        linarith only [face.2.2, oa]
      have bounds := remaining_section_bounds normalO normalA sideA tilt top sign sep
      obtain ⟨x,y,hA,hL⟩ := foreign_segment_overlap A L T hsA normalA tilt sideA
        aD aE top bounds.1 bounds.2 lN lW
      exact apartAL x y ⟨hA,hL⟩
  · by_cases sign : 0 ≤ O.c*T-t*A.c
    · have support : upper O T A.c =
          (O.c*T-t*A.c)*(O.loU+O.side)+(O.c*A.c+t*T)*(O.loV+O.side) := by
        have formula := upper_negative_pos O t T A.c hsO
          (by nlinarith only [sign]) (by nlinarith only [hK])
        convert formula using 1 <;> ring
      have bound := own_axis_above normalO normalA side face.1 face.2.1 sign
      rw [support] at aa
      linarith only [bound, aa, top, same]
    · have low : O.c*T-t*A.c ≤ 0 := le_of_not_ge sign
      have support : upper O T A.c =
          (O.c*T-t*A.c)*O.loU+(O.c*A.c+t*T)*(O.loV+O.side) := by
        have formula := upper_negative_nonpos O t T A.c hsO
          (by nlinarith only [low]) (by nlinarith only [hK])
        convert formula using 1 <;> ring
      have bound := own_axis_below normalO normalA side face.1 face.2.1 low
      rw [support] at aa
      linarith only [bound, aa, top, same]

end N12Compact.C977NegativeCorner
