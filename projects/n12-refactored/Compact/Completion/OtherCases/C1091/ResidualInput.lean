import Compact.Completion.OtherCases.C1091.MergedMarkerSeedWall
import Compact.Completion.CommonCases.OriginalOwners

/-! Literal residual point table of C1091-complete-proof, §2. The owner
Q4 is one merged258 square containing both markers. This is a raw
geometric input, not a claim that the original finite entrance is proved.
The last northwest alternative retains both possible G points. -/
namespace N12Compact.Completion.OtherCases.C1091.Residual
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  cap : ∀ i,(q i).side≤1001/1000
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  cornerSW : (q 0).Inside 1 1
  singletonFar : (q 0).Inside (87/50) 1
  cornerNE : (q 2).Inside 3 3
  mergedLeft : (q 4).Inside (457/500) 1
  mergedMarker : (q 4).Inside (33/20) (33/20)
  mergedLow : (q 4).Inside 1 (87/50)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  center : (q 5).Inside 2 2
  south : (q 5).Inside 2 (3/2)
  east : (q 5).Inside (5/2) 2
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastF9 : (q 6).Inside 3 (113/50)
  northeastG9 : (q 6).Inside 3 (12/5)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF3 : (q 7).Inside (8/5) 3
  northwestG : (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3
  leftMarker : (q 8).Inside (457/500) 2
  leftF1 : (q 8).Inside 1 (113/50)
  leftG1 : (q 8).Inside 1 (12/5)
  bottomBar : ∀ x : ℝ,113/50≤x → x≤14/5 → (q 9).Inside x 1
  rightMarker : (q 10).Inside (1543/500) 2
  rightBar : ∀ y : ℝ,36/25≤y → y≤2 → (q 10).Inside 3 y
  topMarker : (q 11).Inside 2 (1543/500)
  topF7 : (q 11).Inside (12/5) 3

theorem Input.foreign {q : Fin 12 → OpenSquare} (h : Input q)
    (i j : Fin 12) (different : i≠j) (x y : ℝ) (point : (q j).Inside x y) :
    ¬(q i).Inside x y := fun own => h.apart i j different x y ⟨own,point⟩

theorem Input.southeast_cut {q : Fin 12 → OpenSquare} (h : Input q) :
    (q 5).Inside (12/5) 2 :=
  CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ h.center h.east
    (by norm_num) (by norm_num) (by norm_num)

end N12Compact.Completion.OtherCases.C1091.Residual
