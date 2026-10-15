import Compact.Completion.OtherCases.InwardSign
import Compact.Completion.OtherCases.NegativeElbowTwoBars

/-! The full all-angle inward two-bar ending. Its positive sector uses
the actual neighboring center and upper inward point; its negative
sector uses both actual foreign bars directly. -/
namespace N12Compact.Completion.OtherCases.InwardTwoBars
open S12 S12Pilot
set_option Elab.async false

theorem impossible (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (upper : W.Inside 0 (13/50))
    (marker : E.Inside (7/20) (-7/20)) (inner : E.Inside 0 (-13/50))
    (elbow : E.Inside (13/50) 0)
    (bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (right : ∀ y : ℝ,-13/50≤y → y≤0 → ¬E.Inside 1 y)
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : False := by
  obtain ⟨r,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame E
  have marker' := (inside _ _).mpr marker
  have inner' := (inside _ _).mpr inner
  have elbow' := (inside _ _).mpr elbow
  have side' : 1<r.side := by simpa only [shape] using side
  have bottom' : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬r.Inside x (-1) :=
    fun x low high own => bottom x low high ((inside _ _).mp own)
  have right' : ∀ y : ℝ,-13/50≤y → y≤0 → ¬r.Inside 1 y :=
    fun y low high own => right y low high ((inside _ _).mp own)
  have apart' : ∀ x y,¬(W.Inside x y ∧ r.Inside x y) :=
    fun x y own => apart x y ⟨own.1,(inside _ _).mp own.2⟩
  have bounds := abs_le.mp range
  by_cases sign : 0≤r.s
  · exact InwardSign.positive_impossible W r side' (same.trans shape.symm) cp sign bounds.2
      west center upper marker' inner' elbow' (right' (-13/50) le_rfl (by norm_num))
      bottom' apart'
  · have missingCenter : ¬r.Inside 0 0 := fun own => apart' 0 0 ⟨center,own⟩
    exact NegativeElbowTwoBars.impossible r (-r.s) (by ring) side' cp
      (by linarith only [sign]) (by linarith only [bounds.1])
      marker' inner' elbow' missingCenter bottom' right'

#print axioms impossible
end N12Compact.Completion.OtherCases.InwardTwoBars

