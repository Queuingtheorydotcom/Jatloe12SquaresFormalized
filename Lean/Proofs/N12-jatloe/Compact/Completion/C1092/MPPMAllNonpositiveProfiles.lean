import Compact.Completion.C1092.MPPMAllNonpositiveCore
import Compact.Completion.C1092.MPPMMissingNegativeActual

/-! Literal frame transfers of the already proved missing-negative
profile. Each transformed square has exactly the same side and interior
as the stated quarter turn of its supplied native square. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C977CornerCubic C1092MPPMMissingNegativeProfile
set_option Elab.async false
noncomputable section

def counterclockwise (q : OpenSquare) : OpenSquare where
  c := q.c
  s := q.s
  loU := q.loV
  loV := -q.loU-q.side
  side := q.side
  unit_normal := q.unit_normal
  side_pos := q.side_pos

theorem inside_counterclockwise (q : OpenSquare) (x y : ℝ) :
    (counterclockwise q).Inside x y↔q.Inside (-y) x := by
  dsimp [counterclockwise,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [a,b,c,d]

structure MissingPredecessor (W : OpenSquare) : Prop where
  normal : Normal W.c (-W.s)
  lowerU : W.s-W.c≤W.loU
  upperU : W.loU+W.side≤(13/50)*W.s
  lowerV : (14/25)*W.c+W.s≤W.loV
  upperV : W.loV+W.side≤W.c
  large : 252/373≤-W.s

structure MissingSuccessor (E : OpenSquare) : Prop where
  normal : Normal E.c (-E.s)
  lowerU : -(13/50)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -E.c≤E.loV
  upperV : E.loV+E.side≤-E.s-(14/25)*E.c
  large : 252/373≤-E.s

theorem missing_predecessor (D : OpenSquare) (side : 1<D.side)
    (normal : Normal D.c (-D.s)) (profile : StrongFaces D) :
    MissingPredecessor (counterclockwise D) := by
  refine ⟨normal,profile.lowerV,profile.upperV,?_,?_,StrongFaces.sine_lower D side normal profile⟩
  · change (14/25)*D.c+D.s≤-D.loU-D.side
    linarith only [profile.upperU]
  · change -D.loU-D.side+D.side≤D.c
    linarith only [profile.lowerU]

theorem missing_successor (D : OpenSquare) (side : 1<D.side)
    (normal : Normal D.c (-D.s)) (profile : StrongFaces D) :
    MissingSuccessor (C1092MMMPEndingAxes.clockwise D) := by
  refine ⟨normal,?_,?_,profile.lowerU,profile.upperU,StrongFaces.sine_lower D side normal profile⟩
  · change -(13/50)*D.s≤-D.loV-D.side
    linarith only [profile.upperV]
  · change -D.loV-D.side+D.side≤D.c-D.s
    linarith only [profile.lowerV]

structure ClearedSuccessor (E : OpenSquare) : Prop where
  normal : Normal E.c (-E.s)
  lowerV : -E.c≤E.loV
  close : 873/1000<E.c
  small : -E.s<61/125
  negative : E.s<0
  strictCosine : E.c<1
  vertex : E.c*(E.loU+E.side)-E.s*(E.loV+E.side)<1

theorem cleared_successor (D : OpenSquare) (core : Core D) (clear : Cleared D) :
    ClearedSuccessor (C1092MMMPEndingAxes.clockwise D) := by
  refine ⟨core.normal,clear.lowerU,clear.close,clear.small,clear.negative,clear.strictCosine,?_⟩
  change D.c*(-D.loV-D.side+D.side)-D.s*(D.loU+D.side)<1
  linarith only [clear.vertex]

end
#print axioms missing_predecessor
#print axioms missing_successor
#print axioms cleared_successor
end N12Compact.C1092MPPMAllNonpositive
