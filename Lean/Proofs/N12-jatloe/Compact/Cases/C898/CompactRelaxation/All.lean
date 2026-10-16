import Compact.Cases.C898.CompactRelaxation.Data00
import Compact.Cases.C898.CompactRelaxation.Data01
import Compact.Cases.C898.CompactRelaxation.Data02
import Compact.Cases.C898.CompactRelaxation.Data03
import Compact.Cases.C898.CompactRelaxation.Data04
import Compact.Cases.C898.CompactRelaxation.Data05
import Compact.Cases.C898.CompactRelaxation.Data06
import Compact.Cases.C898.CompactRelaxation.Data07
import Compact.Cases.C898.CompactRelaxation.Data08
import Compact.Cases.C898.CompactRelaxation.Data09
import Compact.Cases.C898.CompactRelaxation.Data10
import Compact.Cases.C898.CompactRelaxation.Data11
import Compact.Cases.C898.CompactRelaxation.Data12
import Compact.Cases.C898.CompactRelaxation.Data13
import Compact.Cases.C898.CompactRelaxation.Data14

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

/-- IDs retain the exact historical non-incoming link order. -/
abbrev linksCount : Nat := 927

def entries (i : Fin linksCount) : Entry dictionary :=
  if h0 : i.val < 64 then Data00.get ⟨i.val - 0, by omega⟩ else
  if h1 : i.val < 128 then Data01.get ⟨i.val - 64, by omega⟩ else
  if h2 : i.val < 192 then Data02.get ⟨i.val - 128, by omega⟩ else
  if h3 : i.val < 256 then Data03.get ⟨i.val - 192, by omega⟩ else
  if h4 : i.val < 320 then Data04.get ⟨i.val - 256, by omega⟩ else
  if h5 : i.val < 384 then Data05.get ⟨i.val - 320, by omega⟩ else
  if h6 : i.val < 448 then Data06.get ⟨i.val - 384, by omega⟩ else
  if h7 : i.val < 512 then Data07.get ⟨i.val - 448, by omega⟩ else
  if h8 : i.val < 576 then Data08.get ⟨i.val - 512, by omega⟩ else
  if h9 : i.val < 640 then Data09.get ⟨i.val - 576, by omega⟩ else
  if h10 : i.val < 704 then Data10.get ⟨i.val - 640, by omega⟩ else
  if h11 : i.val < 768 then Data11.get ⟨i.val - 704, by omega⟩ else
  if h12 : i.val < 832 then Data12.get ⟨i.val - 768, by omega⟩ else
  if h13 : i.val < 896 then Data13.get ⟨i.val - 832, by omega⟩ else
  Data14.get ⟨i.val - 896, by have bound : i.val < 927 := i.isLt; omega⟩

private theorem checkIf {α : Type} (P : α → Prop) (test : Prop) [Decidable test]
    (yes : test → α) (no : ¬test → α)
    (hy : ∀ h, P (yes h)) (hn : ∀ h, P (no h)) :
    P (dite test yes no) := by
  by_cases h : test
  · simpa only [dif_pos h] using hy h
  · simpa only [dif_neg h] using hn h

theorem entries_checked (i : Fin linksCount) : (entries i).Check := by
  unfold entries
  refine checkIf Entry.Check _ _ _ ?_ ?_
  · intro h0; exact Data00.checked _
  · intro h0
    refine checkIf Entry.Check _ _ _ ?_ ?_
    · intro h1; exact Data01.checked _
    · intro h1
      refine checkIf Entry.Check _ _ _ ?_ ?_
      · intro h2; exact Data02.checked _
      · intro h2
        refine checkIf Entry.Check _ _ _ ?_ ?_
        · intro h3; exact Data03.checked _
        · intro h3
          refine checkIf Entry.Check _ _ _ ?_ ?_
          · intro h4; exact Data04.checked _
          · intro h4
            refine checkIf Entry.Check _ _ _ ?_ ?_
            · intro h5; exact Data05.checked _
            · intro h5
              refine checkIf Entry.Check _ _ _ ?_ ?_
              · intro h6; exact Data06.checked _
              · intro h6
                refine checkIf Entry.Check _ _ _ ?_ ?_
                · intro h7; exact Data07.checked _
                · intro h7
                  refine checkIf Entry.Check _ _ _ ?_ ?_
                  · intro h8; exact Data08.checked _
                  · intro h8
                    refine checkIf Entry.Check _ _ _ ?_ ?_
                    · intro h9; exact Data09.checked _
                    · intro h9
                      refine checkIf Entry.Check _ _ _ ?_ ?_
                      · intro h10; exact Data10.checked _
                      · intro h10
                        refine checkIf Entry.Check _ _ _ ?_ ?_
                        · intro h11; exact Data11.checked _
                        · intro h11
                          refine checkIf Entry.Check _ _ _ ?_ ?_
                          · intro h12; exact Data12.checked _
                          · intro h12
                            refine checkIf Entry.Check _ _ _ ?_ ?_
                            · intro h13; exact Data13.checked _
                            · intro h13
                              exact Data14.checked _

def links (i : Fin linksCount) : Spec poseCount := (entries i).spec

/-- Exact original oriented-pose implication for every retained link. -/
theorem link_sound (i : Fin linksCount) (q : OpenSquare)
    (holds : (poses (links i).source).OrientedRealizes q) :
    (poses (links i).target).OrientedRealizes q :=
  (entries i).sound (entries_checked i) positive_denominators q holds

#print axioms link_sound

end
end N12Compact.C898CompactRelaxation
