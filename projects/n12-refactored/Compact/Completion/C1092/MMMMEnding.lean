import Compact.Completion.C1092.MMMMSecondPair
import Compact.Completion.C1092.MMMMCancellation
import Compact.Completion.C1092.RigidCharts

/-! The continuous whole MMMM three-central ending, with literal rigid
charts. Its two pair inequalities involve the same original northeast faces. -/
namespace N12Compact.C1092MMMMEnding
open S12 S12Pilot C977CornerCubic C1092RigidCharts
set_option Elab.async false

structure Data (N E W : OpenSquare) : Prop where
  side : 1 < N.side
  sameE : N.side=E.side
  sameW : N.side=W.side
  origin : N.Inside 0 0
  halfX : N.Inside (1/2) 0
  halfY : N.Inside 0 (1/2)
  markerN : N.Inside (7/20) (7/20)
  markerE : E.Inside (7/20) (-7/20)
  ordinaryE1 : E.Inside 1 (-13/50)
  ordinaryE2 : E.Inside 1 (-2/5)
  markerW : W.Inside (-7/20) (7/20)
  ordinaryW1 : W.Inside (-13/50) 1
  ordinaryW2 : W.Inside (-2/5) 1
  eLeftBottom : ¬ E.Inside 1 (-1)
  eLeftTop : ¬ E.Inside 1 0
  eRightBottom : ¬ E.Inside (39/100) (-1)
  eRightTop : ¬ E.Inside (39/100) 0
  wLeftBottom : ¬ W.Inside (-1) 1
  wLeftTop : ¬ W.Inside 0 1
  wRightBottom : ¬ W.Inside (-1) (39/100)
  wRightTop : ¬ W.Inside 0 (39/100)
  apartE : ∀ x y, ¬ (N.Inside x y ∧ E.Inside x y)
  apartW : ∀ x y, ¬ (N.Inside x y ∧ W.Inside x y)

theorem Data.swapped {N E W : OpenSquare} (h : Data N E W) :
    Data (swap N) (swap W) (swap E) where
  side := h.side
  sameE := h.sameW
  sameW := h.sameE
  origin := (inside_swap _ _ _).mpr h.origin
  halfX := (inside_swap _ _ _).mpr h.halfY
  halfY := (inside_swap _ _ _).mpr h.halfX
  markerN := (inside_swap _ _ _).mpr h.markerN
  markerE := (inside_swap _ _ _).mpr h.markerW
  ordinaryE1 := (inside_swap _ _ _).mpr h.ordinaryW1
  ordinaryE2 := (inside_swap _ _ _).mpr h.ordinaryW2
  markerW := (inside_swap _ _ _).mpr h.markerE
  ordinaryW1 := (inside_swap _ _ _).mpr h.ordinaryE1
  ordinaryW2 := (inside_swap _ _ _).mpr h.ordinaryE2
  eLeftBottom := fun z => h.wLeftBottom ((inside_swap _ _ _).mp z)
  eLeftTop := fun z => h.wLeftTop ((inside_swap _ _ _).mp z)
  eRightBottom := fun z => h.wRightBottom ((inside_swap _ _ _).mp z)
  eRightTop := fun z => h.wRightTop ((inside_swap _ _ _).mp z)
  wLeftBottom := fun z => h.eLeftBottom ((inside_swap _ _ _).mp z)
  wLeftTop := fun z => h.eLeftTop ((inside_swap _ _ _).mp z)
  wRightBottom := fun z => h.eRightBottom ((inside_swap _ _ _).mp z)
  wRightTop := fun z => h.eRightTop ((inside_swap _ _ _).mp z)
  apartE := fun x y z => h.apartW y x
    ⟨(inside_swap _ _ _).mp z.1,(inside_swap _ _ _).mp z.2⟩
  apartW := fun x y z => h.apartE y x
    ⟨(inside_swap _ _ _).mp z.1,(inside_swap _ _ _).mp z.2⟩

private theorem reframe {N E W : OpenSquare} (h : Data N E W) (Q : OpenSquare)
    (side : Q.side=N.side) (inside : ∀ x y, Q.Inside x y ↔ N.Inside x y) : Data Q E W where
  side := by simpa only [side] using h.side
  sameE := side.trans h.sameE
  sameW := side.trans h.sameW
  origin := (inside _ _).mpr h.origin
  halfX := (inside _ _).mpr h.halfX
  halfY := (inside _ _).mpr h.halfY
  markerN := (inside _ _).mpr h.markerN
  markerE := h.markerE
  ordinaryE1 := h.ordinaryE1
  ordinaryE2 := h.ordinaryE2
  markerW := h.markerW
  ordinaryW1 := h.ordinaryW1
  ordinaryW2 := h.ordinaryW2
  eLeftBottom := h.eLeftBottom
  eLeftTop := h.eLeftTop
  eRightBottom := h.eRightBottom
  eRightTop := h.eRightTop
  wLeftBottom := h.wLeftBottom
  wLeftTop := h.wLeftTop
  wRightBottom := h.wRightBottom
  wRightTop := h.wRightTop
  apartE := fun x y z => h.apartE x y ⟨(inside _ _).mp z.1,z.2⟩
  apartW := fun x y z => h.apartW x y ⟨(inside _ _).mp z.1,z.2⟩

private theorem negative (N E W : OpenSquare) (h : Data N E W)
    (dn : Normal N.c (-N.s)) : False := by
  let C := opposite N
  obtain ⟨B,bp,bcanon,bside,binside,_⟩ := ClosedFrames.canonical_frame (opposite E)
  have bi : ∀ x y, B.Inside x y ↔ E.Inside (-x) (-y) :=
    fun x y => (binside _ _).trans (inside_opposite _ _ _)
  have ci : ∀ x y, C.Inside x y ↔ N.Inside (-x) (-y) := inside_opposite N
  have missing : ¬ C.Inside (7/20) (-7/20) := by
    norm_num [ci]
    exact fun z => h.apartW _ _ ⟨z,h.markerW⟩
  have first := C1092MMMMFirstPair.result C B h.side (h.sameE.trans bside.symm) dn bp bcanon
    (by norm_num [ci]; exact h.origin)
    (by norm_num [ci]; exact h.halfY)
    (by norm_num [ci]; exact h.markerN) missing
    (by norm_num [bi]; exact h.markerE)
    (by norm_num [bi]; exact h.ordinaryE1)
    (by norm_num [bi]; exact h.ordinaryE2)
    (by norm_num [bi]; exact h.eLeftTop)
    (by norm_num [bi]; exact h.eLeftBottom)
    (by norm_num [bi]; exact h.eRightTop)
    (by norm_num [bi]; exact h.eRightBottom)
    (fun x y z => h.apartE _ _ ⟨(ci _ _).mp z.1,(bi _ _).mp z.2⟩)
  let D := opposite (swap N)
  obtain ⟨A,ap,acanon,aside,ainside,_⟩ := ClosedFrames.canonical_frame (opposite (swap W))
  have ai : ∀ x y, A.Inside x y ↔ W.Inside (-y) (-x) :=
    fun x y => (ainside _ _).trans ((inside_opposite _ _ _).trans (inside_swap _ _ _))
  have di : ∀ x y, D.Inside x y ↔ N.Inside (-y) (-x) :=
    fun x y => (inside_opposite _ _ _).trans (inside_swap _ _ _)
  have missingG : ¬ D.Inside (7/20) (-7/20) := by
    norm_num [di]
    exact fun z => h.apartE _ _ ⟨z,h.markerE⟩
  have missingM : ¬ D.Inside (-7/20) (7/20) := by
    norm_num [di]
    exact fun z => h.apartW _ _ ⟨z,h.markerW⟩
  have second := C1092MMMMSecondPair.result D A h.side (h.sameW.trans aside.symm) dn
    first.centralSine first.centralCosine ap acanon
    (by norm_num [di]; exact h.origin)
    (by norm_num [di]; exact h.halfX)
    (by norm_num [di]; exact h.halfY)
    (by norm_num [di]; exact h.markerN) missingG missingM
    (by norm_num [ai]; exact h.markerW)
    (by norm_num [ai]; exact h.ordinaryW1)
    (by norm_num [ai]; exact h.ordinaryW2)
    (by norm_num [ai]; exact h.wLeftTop)
    (by norm_num [ai]; exact h.wLeftBottom)
    (by norm_num [ai]; exact h.wRightTop)
    (by norm_num [ai]; exact h.wRightBottom)
    (fun x y z => h.apartW _ _ ⟨(di _ _).mp z.1,(ai _ _).mp z.2⟩)
  have bn : Normal B.c B.s := ⟨first.positive.le,
    by simpa only [abs_of_pos first.positive] using bcanon,B.unit_normal⟩
  have an : Normal A.c A.s := ⟨second.positive.le,
    by simpa only [abs_of_pos second.positive] using acanon,A.unit_normal⟩
  have uLow : N.loU < 0 := by linarith only [h.origin.1]
  have vLow : N.loV < 0 := by linarith only [h.origin.2.2.1]
  have east : N.side*(1+B.c*(-N.s)+B.s*N.c) ≤ B.c+B.s+
      (B.c*N.c-B.s*(-N.s))*N.loV-(B.c*(-N.s)+B.s*N.c)*N.loU := by
    have support := first.support
    dsimp [C,opposite] at support
    nlinarith only [support]
  have west : N.side*(1+A.s*N.c-A.c*(-N.s)) ≤ A.c+A.s+
      (A.c*N.c+A.s*(-N.s))*N.loU-(A.s*N.c-A.c*(-N.s))*N.loV := by
    have support := second.support
    dsimp [D,opposite,swap] at support
    nlinarith only [support]
  exact C1092MMMMCancellation.impossible dn bn an h.side first.centralSine first.centralCosine
    first.sine second.sine first.cosine second.cosine uLow vLow east west

theorem impossible (N E W : OpenSquare) (h : Data N E W) : False := by
  obtain ⟨Q,cp,canon,side,inside,_⟩ := ClosedFrames.canonical_frame N
  have data := reframe h Q side inside
  by_cases sign : Q.s ≤ 0
  · have dn : Normal Q.c (-Q.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_nonpos sign] using canon,
      by nlinarith only [Q.unit_normal]⟩
    exact negative Q E W data dn
  · have positive : 0 < Q.s := lt_of_not_ge sign
    have dn : Normal (swap Q).c (-(swap Q).s) := ⟨positive.le,
      by simpa only [swap,neg_neg,abs_of_pos positive] using canon,
      by dsimp [swap]; nlinarith only [Q.unit_normal]⟩
    exact negative (swap Q) (swap W) (swap E) data.swapped dn

#print axioms impossible
end N12Compact.C1092MMMMEnding
