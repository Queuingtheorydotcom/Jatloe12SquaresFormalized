import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Scalars

/-! Common literal input and forced faces for
INNER-CORNER-FOUR-EXCLUSIONS.md and INNER-CORNER-INWARD-POINT.md.
Only the indicated strict points and separate omissions are used. -/
namespace N12Compact.Completion.OtherCases.InnerCornerObstruction
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  origin : q.Inside 0 0
  marker : q.Inside (13/20) (13/20)
  missingLeft : ¬q.Inside (-43/500) 0
  missingNear : ¬q.Inside (3/25) 0
  missingUpper : ¬q.Inside (-43/500) 1

theorem Input.reframe {q r : OpenSquare} (h : Input q) (side : r.side=q.side)
    (same : ∀ x y,r.Inside x y ↔ q.Inside x y) : Input r where
  side := by simpa only [side] using h.side
  origin := (same _ _).mpr h.origin
  marker := (same _ _).mpr h.marker
  missingLeft := fun own => h.missingLeft ((same _ _).mp own)
  missingNear := fun own => h.missingNear ((same _ _).mp own)
  missingUpper := fun own => h.missingUpper ((same _ _).mp own)

theorem positive_faces (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) :
    -(43/500)*q.c≤q.loU ∧ -(3/25)*q.s≤q.loV := by
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have o := h.origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add] at o
  have m := h.marker
  have lowerV : -(3/25)*q.s≤q.loV := by
    apply le_of_not_gt
    intro low
    apply h.missingNear
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [o.1,o.2.2.2,m.2.1,cp,sn,low]
  have lowerU : -(43/500)*q.c≤q.loU := by
    apply le_of_not_gt
    intro low
    apply h.missingLeft
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,o.2.1,o.2.2.1,lowerV,h.side,cu,sn,order,cp]
  exact ⟨lowerU,lowerV⟩

/-- The common negative-sign contradiction uses only O,M,T,R. The
diagonal comparison is strict because the side is greater than one. -/
theorem negative_impossible (q : OpenSquare) (h : Input q) (s : ℝ)
    (signed : q.s= -s) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c) : False := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have bands (x y : ℝ) : q.Inside x y ↔
      q.loU<q.c*x-s*y ∧ q.c*x-s*y<q.loU+q.side ∧
      q.loV<s*x+q.c*y ∧ s*x+q.c*y<q.loV+q.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  have o := (bands _ _).mp h.origin
  have m := (bands _ _).mp h.marker
  have upperU : q.loU+q.side≤(3/25)*q.c := by
    apply le_of_not_gt
    intro high
    apply h.missingNear
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [o.1,o.2.2.1,m.2.2.2,cp,sn,high]
  have slope : (53/100)*q.c<(13/20)*s := by
    linarith only [m.2.1,upperU]
  have rUpperU : -(43/500)*q.c-s<q.loU+q.side := by
    linarith only [m.2.1,cp,sn]
  have rLowerV : q.loV<q.c-(43/500)*s := by
    linarith only [o.2.2.1,cp,order]
  have rUpperV : q.c-(43/500)*s<q.loV+q.side := by
    linarith only [m.2.2.2,slope,cp]
  have lowerU : -(43/500)*q.c-s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply h.missingUpper
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,rUpperU,rLowerV,rUpperV]
  have short := CommonCases.OutwardScalars.increasing_projection q.c s
    (103/500) 1 cp sn order unit (by norm_num) (by norm_num) (by norm_num)
  linarith only [upperU,lowerU,h.side,short]

end N12Compact.Completion.OtherCases.InnerCornerObstruction
