import Compact.Completion.C1092.MPPMInwardFinalPredecessor
import Compact.Completion.C1092.MPPMInwardFinalSuccessor
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! The physical joins in CENTERED-INWARD-OIOI §§6--8. The right bar
has one actual owner R; the paired corner and bottom owner remain K/B.
The first comparison proves C's halfpoint, rather than assuming it.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
open Completion.OtherCases
set_option Elab.async false

structure BottomCorner (B K : OpenSquare) : Prop where
  side : 1<B.side
  same : B.side=K.side
  bottomWall : ∀ x y,B.Inside x y → -2≤y
  cornerWalls : ∀ x y,K.Inside x y → -2≤x ∧ -2≤y
  marker : B.Inside 0 (-543/500)
  inner : B.Inside (-2/5) (-1)
  cornerMarker : K.Inside (-1) (-543/500)
  cornerPoint : K.Inside (-1) (-1)
  apart : ∀ x y,¬(K.Inside x y ∧ B.Inside x y)

theorem bottom_origin (C B K : OpenSquare) (h : BottomCorner B K)
    (halfpoint : C.Inside (-1) (-1/2))
    (apart : ∀ x y,¬(C.Inside x y ∧ K.Inside x y)) : B.Inside 0 (-1) := by
  let B' := B.translated (-2) (-2)
  let K' := K.translated (-2) (-2)
  have bi (x y : ℝ) : B'.Inside x y ↔ B.Inside (-2+x) (-2+y) :=
    inside_translated_iff B (-2) (-2) x y
  have ki (x y : ℝ) : K'.Inside x y ↔ K.Inside (-2+x) (-2+y) :=
    inside_translated_iff K (-2) (-2) x y
  have origin := WallProfile.boundary_origin B' K' (457/500) (8/5)
    h.side h.same
    (fun x y own => by have low := h.bottomWall _ _ ((bi x y).mp own); linarith only [low])
    (fun x y own => by
      have low := h.cornerWalls _ _ ((ki x y).mp own)
      constructor <;> linarith only [low.1,low.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [bi]; norm_num; exact h.marker)
    (by rw [bi]; norm_num; exact h.inner)
    (by rw [ki]; norm_num; exact h.cornerMarker)
    (by rw [ki]; norm_num; exact h.cornerPoint)
    (fun own => apart _ _ ⟨halfpoint,by
      have actual := (ki 1 (3/2)).mp own
      norm_num at actual
      exact actual⟩)
    (fun x y own => h.apart _ _ ⟨(ki x y).mp own.1,(bi x y).mp own.2⟩)
  have actual := (bi 2 1).mp origin
  norm_num at actual
  exact actual

/-- The first actual C/E comparison forces the outer halfpoint. -/
theorem centered_halfpoint (C W E : OpenSquare) (h : CenteredPredecessor C W)
    (same : C.side=E.side) (e : NegativeSuccessor E)
    (inner : C.Inside 0 (-13/50))
    (far : ¬E.Inside 1 (-36/85))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.Inside (-1) (-1/2) := by
  have sharp := centered_predecessor C W h
  have cap := successor_far E (by simpa only [←same] using h.side) e far
  have cb := normal_bounds h.central
  have cp : 0<C.c := by linarith only [cb.1]
  have height : 0≤C.c/11+C.s/2 := by
    linarith only [h.center.2.2.2,sharp.1]
  have order := relative_order h.central e.normal
    (show half C.c (-C.s)<half E.c (-E.s) by linarith only [sharp.2.2.2,cap.2])
  have endpoint : Normal (95727000/103958161) (40541839/103958161) := by norm_num [Normal]
  have endpointHalf : half (95727000/103958161) (40541839/103958161)=2869/14131 := by
    norm_num [half]
  have cross := half_cross endpoint e.normal (by simpa only [endpointHalf] using cap.2.le)
  have margins := centered_half_margins h.central e.normal sharp.2.1 sharp.2.2.1
    sharp.2.2.2.le height cross
  have lowU : C.loU< -C.c-C.s/2 := by
    apply lt_of_not_ge
    intro no
    have lowerA : C.side-C.c-C.s/2≤C.loU+C.side := by linarith only [no]
    exact successor_impossible C E (1/2) (C.c/11+C.s/2) h.side same
      h.central e h.marker inner lowerA sharp.1.le cap.1
      (by nlinarith only [order]) margins.1 margins.2 apart
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [lowU]
  · linarith only [h.center.2.1,h.central.2.1,cp]
  · linarith only [sharp.1,h.side,cb.2.1,sharp.2.2.1]
  · linarith only [h.center.2.2.2,h.centralNegative,cp]

/-- Full centered local ending, with actual foreign-owner producers
kept literal. In particular neither outer auxiliary is assigned to C. -/
theorem centered_impossible (C W E R B K : OpenSquare)
    (h : CenteredPredecessor C W) (same : C.side=E.side)
    (e : NegativeSuccessor E) (inner : C.Inside 0 (-13/50))
    (lowerA : C.side-C.c-(13/50)*C.s≤C.loU+C.side)
    (rightBar : ∀ y : ℝ,-36/85≤y → y≤0 → R.Inside 1 y)
    (bottom : BottomCorner B K)
    (apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y))
    (apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y))
    (apartCK : ∀ x y,¬(C.Inside x y ∧ K.Inside x y))
    (apartEB : ∀ x y,¬(E.Inside x y ∧ B.Inside x y)) : False := by
  have far : ¬E.Inside 1 (-36/85) := fun own =>
    apartER _ _ ⟨own,rightBar _ le_rfl (by norm_num)⟩
  have halfpoint := centered_halfpoint C W E h same e inner far apartCE
  have origin := bottom_origin C B K bottom halfpoint apartCK
  have omitted : ¬E.Inside 0 (-1) := fun own => apartEB _ _ ⟨own,origin⟩
  have side : 1<E.side := by simpa only [←same] using h.side
  have cap := successor_far E side e far
  have angle := successor_bottom E side e cap.1 omitted
  have sharp := centered_predecessor C W h
  have endpoint : Normal (4165/4813) (2412/4813) := by norm_num [Normal]
  have endpointHalf : half (4165/4813) (2412/4813)=(18:ℝ)/67 := by norm_num [half]
  have cross := half_cross endpoint e.normal (by simpa only [endpointHalf] using angle.2.le)
  have margins := centered_final_margins h.central e.normal sharp.2.1 sharp.2.2.1
    sharp.2.2.2.le (show 0≤C.c/11+C.s/2 by linarith only [h.center.2.2.2,sharp.1]) cross
  have order := relative_order h.central e.normal
    (show half C.c (-C.s)<half E.c (-E.s) by linarith only [sharp.2.2.2,angle.2])
  exact successor_impossible C E (13/50) (C.c/11+C.s/2) h.side same h.central e
    h.marker inner lowerA sharp.1.le cap.1 (by nlinarith only [order]) margins.1 margins.2 apartCE

#print axioms bottom_origin
#print axioms centered_halfpoint
#print axioms centered_impossible
end N12Compact.C1092MPPMInwardFinal
