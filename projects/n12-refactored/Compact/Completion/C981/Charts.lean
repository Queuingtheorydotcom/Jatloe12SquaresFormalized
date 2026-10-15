import S12.WallGeometry
import S12.Container

/-! Exact rigid coordinate charts used only with the same actual square.
Their strict interiors, side lengths and genuine coordinate walls are
transported by direct four-band equivalences. -/
namespace N12Compact.C981CompletionCharts

open S12 S12Pilot
set_option Elab.async false

noncomputable def corner (q : OpenSquare) : OpenSquare where
  c := q.s
  s := -q.c
  loU := q.loU-q.c-3*q.s
  loV := q.loV+q.s-3*q.c
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

noncomputable def top (q : OpenSquare) : OpenSquare where
  c := -q.c
  s := q.s
  loU := q.loU-2*q.c-3*q.s
  loV := -q.loV-q.side-2*q.s+3*q.c
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

noncomputable def shiftedTop (q : OpenSquare) : OpenSquare where
  c := q.c
  s := q.s
  loU := q.loU-2*q.c-3*q.s
  loV := q.loV+2*q.s-3*q.c
  side := q.side
  unit_normal := q.unit_normal
  side_pos := q.side_pos

@[simp] theorem corner_side (q : OpenSquare) : (corner q).side=q.side := rfl
@[simp] theorem top_side (q : OpenSquare) : (top q).side=q.side := rfl
@[simp] theorem shiftedTop_side (q : OpenSquare) : (shiftedTop q).side=q.side := rfl

theorem inside_corner (q : OpenSquare) (x y : ℝ) :
    (corner q).Inside x y ↔ q.Inside (1-y) (3+x) := by
  dsimp [corner,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [a,b,c,d]

theorem inside_top (q : OpenSquare) (x y : ℝ) :
    (top q).Inside x y ↔ q.Inside (2-x) (3+y) := by
  dsimp [top,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [a,b,c,d]

theorem inside_shiftedTop (q : OpenSquare) (x y : ℝ) :
    (shiftedTop q).Inside x y ↔ q.Inside (2+x) (3+y) := by
  dsimp [shiftedTop,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [a,b,c,d]

theorem corner_wall (q : OpenSquare) (box : InsideContainer q) :
    ∀ x y, (corner q).Inside x y → y ≤ 1 := by
  intro x y point
  have bound := (box _ _ ((inside_corner _ _ _).mp point)).1
  linarith only [bound]

theorem top_wall (q : OpenSquare) (box : InsideContainer q) :
    ∀ x y, (top q).Inside x y → y ≤ 1 := by
  intro x y point
  have bound := (box _ _ ((inside_top _ _ _).mp point)).2.2.2
  linarith only [bound]

theorem shiftedTop_wall (q : OpenSquare) (box : InsideContainer q) :
    ∀ x y, (shiftedTop q).Inside x y → y ≤ 1 := by
  intro x y point
  have bound := (box _ _ ((inside_shiftedTop _ _ _).mp point)).2.2.2
  linarith only [bound]

end N12Compact.C981CompletionCharts
