import S12.AngleEnclosure
import S12.ReferenceGeometry

namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- An angle enclosure's certified inner square at a lower bound on side. -/
def AngleEnclosure.reference (w : AngleEnclosure) (lowerSide : ℚ) : ReferenceSquare :=
  ⟨w.c,w.s,lowerSide*w.inner⟩

theorem AngleEnclosure.reference_checked (w : AngleEnclosure) (hw : w.Check)
    (lowerSide : ℚ) (ha : 0<lowerSide) : (w.reference lowerSide).Check :=
  ⟨hw.2.2.1,mul_pos ha hw.2.2.2.2.1⟩

/-- Geometry-to-certificate bridge for all orientations in an enclosure.
The actual square contains the fixed rational inner reference square. -/
theorem AngleEnclosure.inner_sound (w : AngleEnclosure) (hw : w.Check)
    (lowerSide : ℚ) (ha : 0<lowerSide) (q : OpenSquare) (t : ℝ)
    (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ)) (hsize : (lowerSide:ℝ)≤q.side) :
    ∀ P : ℝ × ℝ,P-(centerX q,centerY q)∈squareSet
      ((w.reference lowerSide).toSquare (w.reference_checked hw lowerSide ha)) → P∈squareSet q := by
  apply reference_inner_containment
  have hb := w.support hw t ht0 ht1
  have hin : 0<(w.inner:ℝ) := by exact_mod_cast hw.2.2.2.2.1
  have hprod : (w.inner:ℝ)*w.outer≤1 := by exact_mod_cast hw.2.2.2.2.2.1
  have ha' : 0<(lowerSide:ℝ) := by exact_mod_cast ha
  have hn := mul_le_mul_of_nonneg_left hb (mul_nonneg ha'.le hin.le)
  have hp := mul_le_mul_of_nonneg_left hprod ha'.le
  dsimp [AngleEnclosure.reference]
  push_cast
  rw [hc,hs]
  have he0 : normalC t*(w.c:ℝ)+normalS t*(w.s:ℝ)=w.c*normalC t+w.s*normalS t := by ring
  have he1 : -normalC t*(w.s:ℝ)+normalS t*(w.c:ℝ)= -w.s*normalC t+w.c*normalS t := by ring
  rw [he0,he1]
  nlinarith only [hn,hp,hsize]

#print axioms AngleEnclosure.inner_sound
end S12
