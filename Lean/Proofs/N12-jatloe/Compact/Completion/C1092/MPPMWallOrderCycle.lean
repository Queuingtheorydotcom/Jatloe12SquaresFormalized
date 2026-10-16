import Compact.Completion.C1092.ShallowLeftOrder
import S12.AuxCoverGeometry

/-! The literal four-wall cancellation in
C1092-MPPM-SHALLOW-POSITIVE-WALL-ORDER.md sections 7–8.
The four wall squares are fixed actual owners 9,10,11,8. Every local
retaining-sector proof uses the existing same-face order theorem. Mixed
forward-membership patterns may supply their already-derived order directly.
This translates the completed cyclic join, not the original MPPM entrance.
No compiler replay was requested for this source addition. -/
namespace N12Compact.C1092MPPMWallOrderCycle
open S12 S12Pilot
set_option Elab.async false

def bottomRole : Fin 4 → Fin 12 := ![9,10,11,8]
def leftRole : Fin 4 → Fin 12 := ![8,9,10,11]

/-- Inverse quarter-turn charts about the container center. Each chart
acts on the whole physical boundary square, without reassigning a point. -/
def chart (i : Fin 4) (q : OpenSquare) : OpenSquare :=
  ![q.translated 2 2,
    (pullY (pullSwap q)).translated 2 2,
    (pullX (pullY q)).translated 2 2,
    (pullX (pullSwap q)).translated 2 2] i

noncomputable def centerPairs (q : Fin 12 → OpenSquare) : Fin 4 → ℝ × ℝ :=
  ![(centerX (q 9)-2,centerY (q 8)-2),
    (centerY (q 10)-2,2-centerX (q 9)),
    (2-centerX (q 11),2-centerY (q 10)),
    (2-centerY (q 8),centerX (q 11)-2)]

theorem center_pair (q : Fin 12 → OpenSquare) (i : Fin 4) :
    (centerX (chart i (q (bottomRole i))),centerY (chart i (q (leftRole i)))) =
      centerPairs q i := by
  fin_cases i <;>
    simp [chart,bottomRole,leftRole,centerPairs,center_translate_x,center_translate_y,
      center_pullX_x,center_pullX_y,center_pullY_x,center_pullY_y,
      center_pullSwap_x,center_pullSwap_y] <;> first | constructor <;> ring | ring

/-- The four strict comparisons sum to zero in the original coordinates,
even when a center lies on one of the unrelated closed branch cuts. -/
theorem cyclic_order_impossible (q : Fin 12 → OpenSquare)
    (orders : ∀ i : Fin 4,
      0 < centerX (chart i (q (bottomRole i))) +
        centerY (chart i (q (leftRole i)))) : False := by
  have order (i : Fin 4) : 0 < (centerPairs q i).1+(centerPairs q i).2 := by
    have pair := center_pair q i
    have x : centerX (chart i (q (bottomRole i))) = (centerPairs q i).1 :=
      congrArg Prod.fst pair
    have y : centerY (chart i (q (leftRole i))) = (centerPairs q i).2 :=
      congrArg Prod.snd pair
    rw [←x,←y]
    exact orders i
  have first := order 0
  have second := order 1
  have third := order 2
  have fourth := order 3
  dsimp [centerPairs] at first second third fourth
  linarith only [first,second,third,fourth]

/-- The exact already-derived local hypotheses of the retaining sector.
The central upper face in `data` is used simultaneously by both boundary
comparisons; neither wall receives a separately chosen central placement. -/
structure RetainingSector (C B L : OpenSquare) (x : ℝ) : Prop where
  side : 1<C.side
  sameB : C.side=B.side
  sameL : C.side=L.side
  data : C1092ShallowWallOrder.Data C x
  bottomMarker : B.Inside 0 (-543/500)
  bottomOuter : B.Inside (-2/5) (-1)
  bottomWall : ∀ u v, B.Inside u v → -2≤v
  leftMarker : L.Inside (-543/500) 0
  leftOrigin : L.Inside (-1) 0
  leftWall : ∀ u v, L.Inside u v → -2≤u
  apartB : ∀ u v, ¬(C.Inside u v ∧ B.Inside u v)
  apartL : ∀ u v, ¬(C.Inside u v ∧ L.Inside u v)

theorem RetainingSector.order {C B L : OpenSquare} {x : ℝ}
    (h : RetainingSector C B L x) : 0<centerX B+centerY L :=
  C1092ShallowWallOrder.order C B L x h.side h.sameB h.sameL h.data
    h.bottomMarker h.bottomOuter h.bottomWall h.leftMarker h.leftOrigin
    h.leftWall h.apartB h.apartL

theorem retaining_cycle_impossible (q : Fin 12 → OpenSquare)
    (central : Fin 4 → OpenSquare) (angle : Fin 4 → ℝ)
    (sectors : ∀ i : Fin 4,
      RetainingSector (central i) (chart i (q (bottomRole i)))
        (chart i (q (leftRole i))) (angle i)) : False :=
  cyclic_order_impossible q (fun i => (sectors i).order)

/-- The same cancellation accepts each omitted-forward sector's established
order, so it does not assume that all four forward points are retained.
The actual-packing proof of these alternatives remains a separate adapter. -/
theorem mixed_forward_cycle_impossible (q : Fin 12 → OpenSquare)
    (central : Fin 4 → OpenSquare) (angle : Fin 4 → ℝ)
    (sectors : ∀ i : Fin 4,
      RetainingSector (central i) (chart i (q (bottomRole i)))
        (chart i (q (leftRole i))) (angle i) ∨
      0<centerX (chart i (q (bottomRole i)))+centerY (chart i (q (leftRole i)))) :
    False := by
  apply cyclic_order_impossible q
  intro i
  rcases sectors i with retaining | omitted
  · exact retaining.order
  · exact omitted

#print axioms retaining_cycle_impossible
#print axioms mixed_forward_cycle_impossible
end N12Compact.C1092MPPMWallOrderCycle
