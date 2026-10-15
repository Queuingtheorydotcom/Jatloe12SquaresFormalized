import Compact.Cases.C898.CachedPairs.Step00
import Compact.Cases.C898.CachedPairs.Step01
import Compact.Cases.C898.CachedPairs.Step02
import Compact.Cases.C898.CachedPairs.Step03
import Compact.Cases.C898.CachedPairs.Step04
import Compact.Cases.C898.CachedPairs.Step05
import Compact.Cases.C898.CachedPairs.Step06
import Compact.Cases.C898.CachedPairs.Step07
import Compact.Cases.C898.CachedPairs.Step08
import Compact.Cases.C898.CachedPairs.Step11
import Compact.Cases.C898.CachedPairs.Step12
import Compact.Cases.C898.CachedPairs.Step13
import Compact.Cases.C898.CachedPairs.Step14
import Compact.Cases.C898.ChordFused

namespace N12Compact.C898CachedAssembly
open S12 S12Pilot C898Shared C898Cached.AllPairs FourSquareAnchors

/-- The original ordered exclusion with both chord stages fused. The cap and
two closed points are derived from the original packing by CompleteCached. -/
theorem mixed_impossible (q : Fin 11 → OpenSquare)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬((q i).Inside x y ∧ (q j).Inside x y))
    (cap : (q 4).side ≤ 1001/1000)
    (left : ClosedInside (q 4) (33/20) (33/20))
    (right : ClosedInside (q 4) (47/20) (33/20))
    (h0 : OrientedPoseCovered continuousScout898Domain0_0 (q 0))
    (h1 : OrientedPoseCovered continuousScout898Domain1_0 (q 1))
    (h2 : OrientedPoseCovered continuousScout898Domain2_0 (q 2))
    (h3 : OrientedPoseCovered continuousScout898Domain3_0 (q 3))
    (h5 : OrientedPoseCovered continuousScout898Domain5_0 (q 4))
    (h6 : OrientedPoseCovered continuousScout898Domain6_0 (q 5))
    (h7 : OrientedPoseCovered continuousScout898Domain7_0 (q 6))
    (h8 : OrientedPoseCovered continuousScout898Domain8_0 (q 7))
    (h9 : OrientedPoseCovered continuousScout898Domain9_0 (q 8))
    (h10 : OrientedPoseCovered continuousScout898Domain10_0 (q 9))
    (h11 : OrientedPoseCovered continuousScout898Domain11_0 (q 10)) : False := by
  have hstep0 := pairStep0_sound (q 1) (q 7) h1 h8 (hd 1 7 (by decide))
  have hstep1 := pairStep1_sound (q 2) (q 9) h2 h10 (hd 2 9 (by decide))
  have hstep2 := pairStep2_sound (q 3) (q 10) h3 h11 (hd 3 10 (by decide))
  have hstep3 := pairStep3_sound (q 5) (q 3) h6 hstep2 (hd 5 3 (by decide))
  have hstep4 := pairStep4_sound (q 5) (q 9) hstep3 h10 (hd 5 9 (by decide))
  have hstep5 := pairStep5_sound (q 6) (q 5) h7 hstep4 (hd 6 5 (by decide))
  have hstep6 := pairStep6_sound (q 6) (q 10) hstep5 h11 (hd 6 10 (by decide))
  have hstep7 := pairStep7_sound (q 8) (q 2) h9 hstep1 (hd 8 2 (by decide))
  have hstep8 := pairStep8_sound (q 0) (q 1) h0 hstep0 (hd 0 1 (by decide))
  let indices : Fin 7 → Fin 11 := ![4,0,6,10,3,5,8]
  let window : Fin 7 → OpenSquare := fun j => q (indices j)
  have injective : Function.Injective indices := by decide +kernel
  have apart : ∀ j k, j ≠ k → ∀ x y,
      ¬((window j).Inside x y ∧ (window k).Inside x y) := by
    intro j k hne
    exact hd _ _ (fun he => hne (injective he))
  have hstep10 := C898Chord.Fused.chord_fused window
    (fun j => ha _) (fun j => hb _) apart cap left right
    h5 hstep8 hstep6 h11 hstep2 hstep4 hstep7
  have hstep11 := pairStep11_sound (q 4) (q 0) hstep10 hstep8 (hd 4 0 (by decide))
  have hstep12 := pairStep12_sound (q 4) (q 5) hstep11 hstep4 (hd 4 5 (by decide))
  have hstep13 := pairStep13_sound (q 4) (q 6) hstep12 hstep6 (hd 4 6 (by decide))
  have hstep14 := pairStep14_sound (q 4) (q 8) hstep13 hstep7 (hd 4 8 (by decide))
  obtain ⟨leaf, hleaf, _⟩ := hstep14
  exact List.not_mem_nil hleaf

#print axioms mixed_impossible
end N12Compact.C898CachedAssembly
