import Compact.Completion.C1092.WholeSupports

/-! The two longitudinal sources of the final MMMP ending. Both orders
of every actual face-normal axis are considered. Strict markers and the
strict origin remove the transverse orders without an angle mesh. -/
namespace N12Compact.C1092MMMPEndingAxes
open S12 S12Pilot ABTransverse C1092WholeSupports
set_option Elab.async false

noncomputable def clockwise (q : OpenSquare) : OpenSquare where
  c := q.c
  s := q.s
  loU := -q.loV-q.side
  loV := q.loU
  side := q.side
  unit_normal := q.unit_normal
  side_pos := q.side_pos

theorem inside_clockwise (q : OpenSquare) (x y : ℝ) :
    (clockwise q).Inside x y ↔ q.Inside y (-x) := by
  dsimp [clockwise,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [a,b,c,d]

theorem upper_nn (q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*q.c+ny*q.s=d) (dv : -nx*q.s+ny*q.c=e)
    (dn : 0≤d) (en : 0≤e) :
    upper q nx ny=d*(q.loU+q.side)+e*(q.loV+q.side) := by
  rw [(formulas q nx ny).2,du,dv,max_eq_left dn,max_eq_left en]
  ring

theorem alternatives (W N : OpenSquare) (same : W.side=N.side)
    (wp : 0<W.c) (wn : 0≤W.s) (wo : W.s≤W.c)
    (np : 0<N.c) (nn : 0≤N.s) (no : N.s≤N.c)
    (origin : W.Inside 0 0) (wm : W.Inside (-7/20) (7/20))
    (nm : N.Inside (7/20) (7/20))
    (apart : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y)) :
    W.loU+W.side≤lower N W.c W.s ∨ upper W N.c N.s≤N.loU := by
  have axes := CongruentSAT.faceSeparation_of_disjoint W N same apart
  change pairRadius W N≤|W.c*(centerX N-centerX W)+W.s*(centerY N-centerY W)| ∨
    pairRadius W N≤|-W.s*(centerX N-centerX W)+W.c*(centerY N-centerY W)| ∨
    pairRadius N W≤|N.c*(centerX N-centerX W)+N.s*(centerY N-centerY W)| ∨
    pairRadius N W≤|-N.s*(centerX N-centerX W)+N.c*(centerY N-centerY W)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius W nx ny+supportRadius N nx ny=R)
      (axis : R≤|nx*(centerX N-centerX W)+ny*(centerY N-centerY W)|) :=
    separated W N nx ny (by rwa [identity])
  rcases axes with wu | wv | nu | nv
  · have pair := separateAxis W.c W.s _ (parallel_radius W N) wu
    have first := strict_bounds W _ _ W.c W.s W.unit_normal wm
    have last := strict_bounds N _ _ W.c W.s W.unit_normal nm
    rcases pair with forward | reverse
    · exact Or.inl (by simpa only [(ownU W).2] using forward)
    · exfalso; nlinarith only [reverse,first.1,last.2,wp]
  · have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have pair := separateAxis (-W.s) W.c _ (transverse_radius W N) wv
    have first := strict_bounds W _ _ (-W.s) W.c unit wm
    have last := strict_bounds N _ _ (-W.s) W.c unit nm
    have zero := strict_bounds W 0 0 (-W.s) W.c unit origin
    rcases pair with forward | reverse <;> exfalso
    · nlinarith only [forward,first.2,last.1,wn]
    · nlinarith only [reverse,zero.1,last.2,wo]
  · have identity : supportRadius W N.c N.s+supportRadius N N.c N.s=pairRadius N W := by
      rw [add_comm]; exact parallel_radius N W
    have pair := separateAxis N.c N.s _ identity nu
    have first := strict_bounds W _ _ N.c N.s N.unit_normal wm
    have last := strict_bounds N _ _ N.c N.s N.unit_normal nm
    rcases pair with forward | reverse
    · exact Or.inr (by simpa only [(ownU N).1] using forward)
    · exfalso; nlinarith only [reverse,first.1,last.2,np]
  · have unit : (-N.s)^2+N.c^2=1 := by nlinarith only [N.unit_normal]
    have identity : supportRadius W (-N.s) N.c+supportRadius N (-N.s) N.c=pairRadius N W := by
      rw [add_comm]; exact transverse_radius N W
    have pair := separateAxis (-N.s) N.c _ identity nv
    have first := strict_bounds W _ _ (-N.s) N.c unit wm
    have last := strict_bounds N _ _ (-N.s) N.c unit nm
    have zero := strict_bounds W 0 0 (-N.s) N.c unit origin
    rcases pair with forward | reverse <;> exfalso
    · nlinarith only [forward,first.2,last.1,nn]
    · nlinarith only [reverse,zero.1,last.2,no]

#print axioms alternatives
end N12Compact.C1092MMMPEndingAxes
