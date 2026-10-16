import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Completion.CommonCases.LowerSegmentSupport

/-! Literal hypotheses and the two closed segment supports in
ORDINARY-BAR-CROSSPOINT.md. The isolated lower marker and the foreign
segment are separate exclusions; no common owner is imposed. -/
namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  marker : q.Inside (7/20) (-7/20)
  near : q.Inside 1 (-13/50)
  far : q.Inside 1 (-2/5)
  missingRight : ¬q.Inside (543/500) 0
  missingLower : ¬q.Inside (543/500) (-1)
  segment : ∀ x : ℝ,13/50≤x → x≤22/25 → ¬q.Inside x (-1)

theorem Input.reframe {q r : OpenSquare} (h : Input q) (side : r.side=q.side)
    (same : ∀ x y,r.Inside x y ↔ q.Inside x y) : Input r where
  side := by simpa only [side] using h.side
  marker := (same _ _).mpr h.marker
  near := (same _ _).mpr h.near
  far := (same _ _).mpr h.far
  missingRight := fun own => h.missingRight ((same _ _).mp own)
  missingLower := fun own => h.missingLower ((same _ _).mp own)
  segment := fun x low high own => h.segment x low high ((same _ _).mp own)

/-- The positive frame's two actual lower exits bound its closed lowest
vertex. The segment is used throughout, including both endpoints. -/
theorem positive_segment (q : OpenSquare) (h : Input q)
    (fLowerU : (13/50)*q.c-q.s≤q.loU)
    (fLowerV : q.loV< -(13/50)*q.s-q.c)
    (fUpperV : -(13/50)*q.s-q.c<q.loV+q.side)
    (tLowerU : q.loU<(22/25)*q.c-q.s)
    (tUpperU : (22/25)*q.c-q.s<q.loU+q.side)
    (tLowerV : -(22/25)*q.s-q.c≤q.loV) :
    -1≤q.s*q.loU+q.c*q.loV := by
  have support := CommonCases.LowerSegmentSupport.support
    q.loU (q.loU+q.side) q.loV (q.loV+q.side)
    ((13/50)*q.c-q.s) (-(13/50)*q.s-q.c)
    ((22/25)*q.c-q.s) (-(22/25)*q.s-q.c)
    fLowerU tLowerU tUpperU fLowerV fUpperV tLowerV
    (by
      intro w wn wu own
      apply h.segment ((1-w)*(13/50)+w*(22/25))
        (by linarith only [wn]) (by linarith only [wu])
      change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  nlinarith only [support,q.unit_normal]

/-- Negating only the u-band converts the upper-u/lower-v pair of exits
into the same exact segment-order theorem. This is not a physical reflection. -/
theorem negative_segment (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t)
    (fLowerU : q.loU<(13/50)*q.c+t)
    (fUpperU : (13/50)*q.c+t<q.loU+q.side)
    (fLowerV : (13/50)*t-q.c≤q.loV)
    (tUpperU : q.loU+q.side≤(22/25)*q.c+t)
    (tLowerV : q.loV<(22/25)*t-q.c)
    (tUpperV : (22/25)*t-q.c<q.loV+q.side) :
    -1≤ -t*(q.loU+q.side)+q.c*q.loV := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have support := CommonCases.LowerSegmentSupport.support
    (-(q.loU+q.side)) (-q.loU) q.loV (q.loV+q.side)
    (-((22/25)*q.c+t)) ((22/25)*t-q.c)
    (-((13/50)*q.c+t)) ((13/50)*t-q.c)
    (by linarith only [tUpperU]) (by linarith only [fUpperU])
    (by linarith only [fLowerU]) tLowerV tUpperV fLowerV
    (by
      intro w wn wu own
      apply h.segment ((1-w)*(22/25)+w*(13/50))
        (by linarith only [wu]) (by linarith only [wn])
      simp only [OpenSquare.Inside,InBands,signed,neg_neg]
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  nlinarith only [support,unit]

end N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
