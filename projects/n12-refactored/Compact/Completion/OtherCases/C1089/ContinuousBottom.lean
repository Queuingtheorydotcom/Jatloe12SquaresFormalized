import Compact.Geometry.WallLowerCenterBarrier
import Compact.Geometry.WallSignChord
import Compact.Completion.C981.WallAdvance
import Compact.Completion.CommonCases.OriginalOwners

/-! Proposition 1 of C1089-CONTINUOUS-REDUCTION. The original Q0
horizontal seed and off-row seed retain Q0 as their actual owner.
The component adapter names exactly the three retained Q9 components;
it does not assert the as-yet-unjoined completeness of that component list.
All geometry is independent of wall signs and catalogue-row selection.
Source translation only; this module has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousBottom
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- The near bottom auxiliary follows from the far auxiliary and the
actual foreign singleton/central points. The center cut is proved first,
then the single-wall chord supplies the strict near point. This statement
does not assume any auxiliary component or the near point itself. -/
theorem near_of_far (W : OpenSquare) (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside 2 (457/500)) (far : W.Inside (12/5) 1)
    (singleton : ¬W.Inside (87/50) 1)
    (central : ¬W.Inside (47/20) (33/20)) :
    21/10<centerX W ∧ W.Inside (113/50) 1 := by
  have swapBox : InsideContainer (pullSwap W) := container_pullSwap W box
  have mark : (pullSwap W).Inside (457/500) 2 := (inside_pullSwap _ _ _).mpr marker
  have anchor : (pullSwap W).Inside 1 (12/5) := (inside_pullSwap _ _ _).mpr far
  have low : ¬(pullSwap W).Inside 1 (87/50) :=
    fun own => singleton ((inside_pullSwap _ _ _).mp own)
  have middle : ¬(pullSwap W).Inside (33/20) (47/20) :=
    fun own => central ((inside_pullSwap _ _ _).mp own)
  have high := WallLowerCenterBarrier.center_above (pullSwap W) side swapBox mark anchor low middle
  have near := WallSignChord.chord (pullSwap W) side
    (fun x y own => (swapBox x y own).1) mark middle
    (by linarith only [high]) (113/50) (by norm_num) (by norm_num)
  rw [center_pullSwap_y] at high
  exact ⟨high,(inside_pullSwap _ _ _).mp near⟩

/-- The underlying continuous implication, with strict foreign points
coming from their actual owners in the original-owner adapter below. -/
theorem reach (W : OpenSquare) (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside 2 (457/500)) (far : W.Inside (12/5) 1)
    (near : W.Inside (113/50) 1)
    (singleton : ¬W.Inside (87/50) 1)
    (seed : ¬W.Inside (187/100) (19/25))
    (central : ¬W.Inside (47/20) (33/20)) :
    51/25<centerX W ∧ W.Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → W.Inside x 1 := by
  have swapBox : InsideContainer (pullSwap W) := by
    intro x y own
    have actual := box y x ((inside_pullSwap W x y).mp own)
    exact ⟨actual.2.2.1,actual.2.2.2,actual.1,actual.2.1⟩
  have mark : (pullSwap W).Inside (457/500) 2 := (inside_pullSwap _ _ _).mpr marker
  have anchor : (pullSwap W).Inside 1 (12/5) := (inside_pullSwap _ _ _).mpr far
  have low : ¬(pullSwap W).Inside 1 (87/50) := fun own => singleton ((inside_pullSwap _ _ _).mp own)
  have middle : ¬(pullSwap W).Inside (33/20) (47/20) := fun own => central ((inside_pullSwap _ _ _).mp own)
  have high := WallLowerCenterBarrier.center_above (pullSwap W) side swapBox mark anchor low middle
  have advanced := C981CompletionWallAdvance.point (pullSwap W) side swapBox mark anchor low
    (fun own => seed ((inside_pullSwap _ _ _).mp own)) middle
  have last : W.Inside (14/5) 1 := (inside_pullSwap _ _ _).mp advanced
  refine ⟨?_,last,?_⟩
  · rw [center_pullSwap_y] at high
    linarith only [high]
  · intro x lower upper
    exact CommonCases.OriginalOwners.horizontal_segment W (113/50) (14/5) 1 x
      near last (by norm_num) lower upper

/-- The full unconditional bottom reach after eliminating the formerly
explicit G5 input. Both its center and G5 are derived from the actual
far anchor; the off-row singleton point supplies the farther advance. -/
theorem reach_of_far (W : OpenSquare) (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside 2 (457/500)) (far : W.Inside (12/5) 1)
    (singleton : ¬W.Inside (87/50) 1)
    (seed : ¬W.Inside (187/100) (19/25))
    (central : ¬W.Inside (47/20) (33/20)) :
    51/25<centerX W ∧ W.Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → W.Inside x 1 :=
  reach W side box marker far (near_of_far W side box marker far singleton central).2
    singleton seed central

def family : Finset Nat := {1,12,48,192,256,512,1024,2048,4096,8192,16384,32768}

/-- Literal complete Q9 component list reported by the retained C1089
entrance. Establishing membership in this list remains the finite entrance
obligation; its consequences are proved for every listed component. -/
def bottomComponents : List (Finset Nat) := [{6,15},{6,15,18},{4,6,15}]

theorem original_bottom (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (component : CommonCases.OriginalOwners.auxiliaries p 8192∈bottomComponents) :
    let W := CommonCases.OriginalOwners.owner p 8192
    51/25<centerX W ∧ W.Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → W.Inside x 1 := by
  have compulsory : ∀ row∈bottomComponents,6∈row ∧ 15∈row := by decide +kernel
  have pair := compulsory _ component
  have far : (CommonCases.OriginalOwners.owner p 8192).Inside (12/5) 1 := by
    have own := (CommonCases.OriginalOwners.auxiliary_exact p 8192 6 (by norm_num)).mpr pair.1
    simpa [auxPoints,fPoints,gPoints] using own
  have near : (CommonCases.OriginalOwners.owner p 8192).Inside (113/50) 1 := by
    have own := (CommonCases.OriginalOwners.auxiliary_exact p 8192 15 (by norm_num)).mpr pair.2
    simpa [auxPoints,fPoints,gPoints] using own
  have marker := CommonCases.OriginalOwners.seed family p hf 8192 (by decide +kernel)
    (2,457/500) (by decide +kernel)
  have singleton := CommonCases.OriginalOwners.seed family p hf 1 (by decide +kernel)
    (87/50,1) (by decide +kernel)
  have seed := CommonCases.OriginalOwners.seed family p hf 1 (by decide +kernel)
    (187/100,19/25) (by decide +kernel)
  have central := CommonCases.OriginalOwners.seed family p hf 512 (by decide +kernel)
    (47/20,33/20) (by decide +kernel)
  norm_num at marker singleton seed central
  have apart0 := CommonCases.OriginalOwners.apart family p hf 8192 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have apart5 := CommonCases.OriginalOwners.apart family p hf 8192 512
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact reach _ (CommonCases.OriginalOwners.side p 8192)
    (CommonCases.OriginalOwners.box p 8192) marker far near
    (fun own => apart0 _ _ ⟨own,singleton⟩)
    (fun own => apart0 _ _ ⟨own,seed⟩)
    (fun own => apart5 _ _ ⟨own,central⟩)

end
#print axioms reach
#print axioms near_of_far
#print axioms reach_of_far
#print axioms original_bottom
end N12Compact.Completion.OtherCases.C1089.ContinuousBottom
