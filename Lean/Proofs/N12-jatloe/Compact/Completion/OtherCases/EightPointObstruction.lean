import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.OutwardScalars
import Mathlib.Tactic.Ring

/-! The new user-supplied EIGHT-POINT-OBSTRUCTION.md (14 October 2026).
Two strict points and six separate weak exclusions are impossible for an
arbitrarily oriented open square of side greater than one. Both signs of
the same physical canonical frame are treated without angle optimization.
The source theorem has not been compiled. -/
namespace N12Compact.Completion.OtherCases.EightPointObstruction
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1 < q.side
  marker : q.Inside (13/20) (7/20)
  anchor : q.Inside 0 (13/50)
  origin : ¬q.Inside 0 0
  middle : ¬q.Inside (1/2) 0
  corner : ¬q.Inside 0 1
  lower : ¬q.Inside (27/100) (-(1/25))
  topNear : ¬q.Inside (11/25) 1
  topFar : ¬q.Inside (37/50) 1

theorem Input.reframe {q r : OpenSquare} (h : Input q)
    (side : r.side=q.side) (inside : ∀ x y, r.Inside x y ↔ q.Inside x y) : Input r where
  side := by simpa only [side] using h.side
  marker := (inside _ _).mpr h.marker
  anchor := (inside _ _).mpr h.anchor
  origin := fun p => h.origin ((inside _ _).mp p)
  middle := fun p => h.middle ((inside _ _).mp p)
  corner := fun p => h.corner ((inside _ _).mp p)
  lower := fun p => h.lower ((inside _ _).mp p)
  topNear := fun p => h.topNear ((inside _ _).mp p)
  topFar := fun p => h.topFar ((inside _ _).mp p)

private theorem projection (c s p q R : ℝ) (unit : c^2+s^2=1)
    (positive : 0 < R) (margin : p^2+q^2 < R^2) : p*c+q*s < R := by
  have identity : (p*c+q*s)^2+(q*c-p*s)^2=p^2+q^2 := by
    calc
      _ = (p^2+q^2)*(c^2+s^2) := by ring
      _ = _ := by rw [unit]; ring
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg (sub_nonneg.mpr high)
    (show 0 ≤ p*c+q*s+R by linarith only [high,positive])
  nlinarith only [identity,product,margin,sq_nonneg (q*c-p*s)]

theorem nonnegative_impossible (q : OpenSquare) (h : Input q)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c) : False := by
  have unit := q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order unit).2.1
  have m := h.marker
  have a := h.anchor
  simp only [OpenSquare.Inside,InBands,zero_mul,zero_add] at m a
  have middleV : -(1/2)*q.s ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply h.middle
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.2,m.2.1,cp,sn,order,low]
  have cornerV : q.loV+q.side ≤ q.c := by
    apply le_of_not_gt
    intro high
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.1,m.2.1,cp,sn,order,high]
  have originU : 0 ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply h.origin
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
    refine ⟨low,?_,?_,?_⟩ <;>
      linarith only [a.2.1,a.2.2.2,cornerV,h.side,cu,cp,sn]
  have farU : q.loU+q.side ≤ (37/50)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply h.topFar
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,m.2.2.1,middleV,h.side,cu,cp,sn,order,high]
  have nearU : q.loU+q.side ≤ (11/25)*q.c+q.s := by
    have wide := projection q.c q.s (237/50) (31/25) 5 unit (by norm_num) (by norm_num)
    have nearV : -(11/25)*q.s+q.c < q.loV+q.side := by
      apply lt_of_not_ge
      intro cap
      linarith only [cap,middleV,farU,originU,wide,h.side]
    apply le_of_not_gt
    intro high
    apply h.topNear
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,m.2.2.1,cp,sn,order,high,nearV]
  have lowerV : -(27/100)*q.s-(1/25)*q.c ≤ q.loV := by
    have short := CommonCases.OutwardScalars.increasing_projection q.c q.s
      (17/100) (26/25) cp sn order unit (by norm_num) (by norm_num) (by norm_num)
    have lowerU : q.loU < (27/100)*q.c-(1/25)*q.s := by
      apply lt_of_not_ge
      intro face
      linarith only [face,nearU,short,h.side]
    apply le_of_not_gt
    intro low
    apply h.lower
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [lowerU,low,m.2.1,a.2.2.2,cp,sn]
  have final := projection q.c q.s (37/25) (127/100) 2 unit (by norm_num) (by norm_num)
  linarith only [nearU,originU,cornerV,lowerV,h.side,final]

theorem nonpositive_impossible (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c t cp tn order unit).2.1
  have m := h.marker
  have a := h.anchor
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,zero_mul,zero_add] at m a
  have originV : 0 ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply h.origin
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_add]
    refine ⟨?_,?_,low,?_⟩ <;> linarith only [a.1,a.2.2.2,m.2.1,cp,tn,order]
  have cornerU : -t ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply h.corner
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,zero_mul,mul_one,zero_add]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.2.1,a.2.2.1,originV,h.side,cu,cp,tn,low]
  have middle : q.loU+q.side ≤ q.c/2 ∨ t/2 ≤ q.loV := by
    by_cases face : q.loU+q.side ≤ q.c/2
    · exact Or.inl face
    · right
      apply le_of_not_gt
      intro low
      apply h.middle
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a.1,m.2.2.2,face,low,cp,tn,order]
  have top : (11/25)*q.c-t ≤ q.loU ∨ q.loV+q.side ≤ q.c+(11/25)*t := by
    by_cases face : (11/25)*q.c-t ≤ q.loU
    · exact Or.inl face
    · right
      apply le_of_not_gt
      intro high
      apply h.topNear
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [m.2.1,m.2.2.1,face,high,cp,tn,order]
  have caps : q.loU+q.side ≤ q.c/2 ∧ q.loV+q.side ≤ q.c+(11/25)*t := by
    rcases middle with du | dv <;> rcases top with tu | tv
    · have short := CommonCases.OutwardScalars.increasing_projection q.c t
        (3/50) 1 cp tn order unit (by norm_num) (by norm_num) (by norm_num)
      exact False.elim (by linarith only [du,tu,short,h.side])
    · exact ⟨du,tv⟩
    · exact False.elim (by linarith only [dv,tu,a.1,a.2.2.1,cp])
    · exact False.elim (by linarith only [dv,tv,cu,tn,h.side])
  have lowerV : (27/100)*t-(1/25)*q.c ≤ q.loV := by
    have short := CommonCases.OutwardScalars.increasing_projection q.c t
      (27/100) (26/25) cp tn order unit (by norm_num) (by norm_num) (by norm_num)
    have upperU : (27/100)*q.c+(1/25)*t < q.loU+q.side := by
      apply lt_of_not_ge
      intro cap
      linarith only [cornerU,cap,short,h.side]
    apply le_of_not_gt
    intro low
    apply h.lower
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.2,upperU,low,cp,tn,order]
  have final := projection q.c t (77/50) (117/100) 2 unit (by norm_num) (by norm_num)
  linarith only [caps.1,caps.2,cornerU,lowerV,h.side,final]

/-- The theorem concerns one original physical square at arbitrary angle;
canonicalization only relabels its own four faces. -/
theorem impossible (q : OpenSquare) (h : Input q) : False := by
  obtain ⟨r,cp,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side inside
  by_cases sign : 0 ≤ r.s
  · exact nonnegative_impossible r data cp sign
      (by simpa only [abs_of_nonneg sign] using range)
  · exact nonpositive_impossible r data (-r.s) (by ring) cp
      (by linarith only [sign]) (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

#print axioms impossible
end N12Compact.Completion.OtherCases.EightPointObstruction
