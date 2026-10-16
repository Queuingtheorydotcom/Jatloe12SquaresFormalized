import Compact.Geometry.ABTransverse

/-! The three exhaustive support orders shared by both MMMM pair arguments.
Both orders on each of the four actual face axes are considered. -/
namespace N12Compact.C1092MMMMPairAxes
open S12 S12Pilot ABTransverse C977ChainBridge ThreeSquare
set_option Elab.async false

theorem alternatives (C B : OpenSquare) (side : 1 < C.side)
    (same : C.side=B.side) (cp : 0 < C.c) (cc : C.s ≤ C.c)
    (bp : 0 < B.c) (bc : B.s ≤ B.c) (sum : C.c-C.s ≤ 10/7)
    (origin : C.Inside 0 0) (central : C.Inside (-7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (ordinary : B.Inside (-1) (2/5))
    (cap : C.loU+C.side ≤ (7/20)*(C.c-C.s))
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) :
    B.loU+B.side ≤ lower C B.c B.s ∨
      C.loV+C.side ≤ lower B (-C.s) C.c ∨
      upper C (-B.s) B.c ≤ B.loV := by
  have axes := CongruentSAT.faceSeparation_of_disjoint C B same apart
  change pairRadius C B ≤ |C.c*(centerX B-centerX C)+C.s*(centerY B-centerY C)| ∨
    pairRadius C B ≤ |-C.s*(centerX B-centerX C)+C.c*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |B.c*(centerX B-centerX C)+B.s*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |-B.s*(centerX B-centerX C)+B.c*(centerY B-centerY C)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius C nx ny+supportRadius B nx ny=R)
      (sep : R ≤ |nx*(centerX B-centerX C)+ny*(centerY B-centerY C)|) :=
    separated C B nx ny (by rwa [identity])
  rcases axes with cu | cv | bu | bv
  · have sep := separateAxis C.c C.s _ (parallel_radius C B) cu
    have zero := strict_bounds C 0 0 C.c C.s C.unit_normal origin
    have point := strict_bounds B _ _ C.c C.s C.unit_normal marker
    rcases sep with forward | reverse
    · exfalso; nlinarith only [forward,zero.2,point.1,cc]
    · rw [(ownU C).1] at reverse
      exfalso; nlinarith only [reverse,point.2,cap,side,sum]
  · have sep := separateAxis (-C.s) C.c _ (transverse_radius C B) cv
    have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    have first := strict_bounds C _ _ (-C.s) C.c unit central
    have last := strict_bounds B _ _ (-C.s) C.c unit marker
    rcases sep with forward | reverse
    · right; left; simpa only [(ownV C).2] using forward
    · exfalso; nlinarith only [reverse,first.1,last.2,cp]
  · have identity : supportRadius C B.c B.s+supportRadius B B.c B.s=pairRadius B C := by
      rw [add_comm]; exact parallel_radius B C
    have sep := separateAxis B.c B.s _ identity bu
    have zero := strict_bounds C 0 0 B.c B.s B.unit_normal origin
    have point := strict_bounds B _ _ B.c B.s B.unit_normal ordinary
    rcases sep with forward | reverse
    · exfalso; nlinarith only [forward,zero.2,point.1,bc,bp]
    · left; simpa only [(ownU B).2] using reverse
  · have identity : supportRadius C (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B C := by
      rw [add_comm]; exact transverse_radius B C
    have sep := separateAxis (-B.s) B.c _ identity bv
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have first := strict_bounds C _ _ (-B.s) B.c unit central
    have last := strict_bounds B _ _ (-B.s) B.c unit marker
    rcases sep with forward | reverse
    · right; right; simpa only [(ownV B).1] using forward
    · exfalso; nlinarith only [reverse,first.1,last.2,bp]

#print axioms alternatives
end N12Compact.C1092MMMMPairAxes
