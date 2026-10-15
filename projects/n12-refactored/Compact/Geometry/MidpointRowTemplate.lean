import Compact.Geometry.MidpointSection
import Compact.Geometry.FourSquareLowerBarrier

/-! A complete four-owner contradiction from a strict unit vertical span.
The two wall squares use actual missing lower auxiliary points. No missing
corner barrier, pose cover, angle partition or side upper cap is assumed. -/
namespace N12Compact.MidpointRowTemplate

open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

structure Premises (A B L R : OpenSquare) (topX : ℝ) : Prop where
  aSide : 1 < A.side
  bSide : 1 < B.side
  lSide : 1 < L.side
  rSide : 1 < R.side
  bBox : InsideContainer B
  lBox : InsideContainer L
  rBox : InsideContainer R
  aP : ClosedInside A 2 (113/50)
  aQ : ClosedInside A (113/50) 2
  aT : ClosedInside A (47/20) (47/20)
  aF : ¬ A.Inside (33/20) (33/20)
  aG : ¬ A.Inside (47/20) (33/20)
  bMarker : ClosedInside B (33/20) (47/20)
  bLow : B.Inside (87/50) 2
  bHigh : B.Inside topX 3
  lP : ClosedInside L (457/500) 2
  lQ : ClosedInside L 1 (12/5)
  lMissingLow : ¬ L.Inside 1 (87/50)
  rP : ClosedInside R (1543/500) 2
  rQ : ClosedInside R 3 (12/5)
  rMissingLow : ¬ R.Inside 3 (87/50)
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)
  br : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)

private theorem close {q : OpenSquare} {x y : ℝ} (hp : q.Inside x y) :
    ClosedInside q x y := ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

theorem impossible (A B L R : OpenSquare) (topX : ℝ)
    (h : Premises A B L R topX) : False := by
  have highR : R.Inside 3 (5/2) := FourSquareLowerBarrier.right_point R A
    h.rSide h.rBox h.rP h.rQ h.rMissingLow h.aQ
    (fun x y hp => h.ar x y ⟨hp.2,hp.1⟩)
  have leftReflected : (pullX L).Inside 3 (5/2) := by
    apply FourSquareLowerBarrier.right_point (pullX L) (pullX B)
      h.lSide (container_pullX L h.lBox)
    · apply (ClosedFrames.closed_pullX L _ _).mpr
      norm_num
      exact h.lP
    · apply (ClosedFrames.closed_pullX L _ _).mpr
      norm_num
      exact h.lQ
    · intro hp
      have original := (inside_pullX L _ _).mp hp
      apply h.lMissingLow
      norm_num at original
      exact original
    · apply (ClosedFrames.closed_pullX B _ _).mpr
      norm_num
      exact close h.bLow
    · intro x y hp
      exact h.bl _ _ ⟨(inside_pullX B _ _).mp hp.2,(inside_pullX L _ _).mp hp.1⟩
  have highL : L.Inside 1 (5/2) := by
    have original := (inside_pullX L _ _).mp leftReflected
    norm_num at original
    exact original
  have foreignB := ClosedPointExclusion.outside_of_closed A B _ _ h.ab h.bMarker
  have foreignR := ClosedPointExclusion.outside_of_closed A R _ _ h.ar h.rQ
  have foreignHigh : ¬ A.Inside 3 (5/2) := fun hp => h.ar _ _ ⟨hp,highR⟩
  obtain ⟨a,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame A
  have highA : A.Inside 2 (5/2) := (hi _ _).mp
    (FourSquareANarrow.point_of_higher_R a (by simpa only [hside] using h.aSide) hc hs
      ((hcl _ _).mpr h.aP) ((hcl _ _).mpr h.aQ) ((hcl _ _).mpr h.aT)
      (fun hp => h.aF ((hi _ _).mp hp)) (fun hp => h.aG ((hi _ _).mp hp))
      (fun hp => foreignB ((hi _ _).mp hp)) (fun hp => foreignR ((hi _ _).mp hp))
      (fun hp => foreignHigh ((hi _ _).mp hp)))
  have hsection : MidpointSection.UnitSection B (5/2) :=
    MidpointSection.of_unit_span B (87/50) topX (5/2) h.bSide
      (by norm_num; exact h.bLow) (by norm_num; exact h.bHigh)
  obtain ⟨j,hj⟩ := MidpointSection.grid_hit B (5/2) h.bBox hsection
  have cases : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
  rcases cases with he | he | he
  · apply h.bl 1 (5/2)
    exact ⟨by convert hj using 1 <;> norm_num [he],highL⟩
  · apply h.ab 2 (5/2)
    exact ⟨highA,by convert hj using 1 <;> norm_num [he]⟩
  · apply h.br 3 (5/2)
    exact ⟨by convert hj using 1 <;> norm_num [he],highR⟩

#print axioms impossible
end N12Compact.MidpointRowTemplate
