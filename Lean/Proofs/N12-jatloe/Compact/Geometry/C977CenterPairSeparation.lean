import Compact.Geometry.ABTransverse

/-! In the center-owned branch, an inner auxiliary point on the adjacent
central square removes both transverse directions. These are full-square
SAT reductions for signed canonical frames; no orientation sign is fixed. -/
namespace N12Compact.C977CenterPairSeparation

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge

/-- The actual southwest and southeast central squares can separate only
eastward, on one of their own longitudinal axes. The southeast inner point
is retained explicitly because it is conditional in the original family. -/
theorem right_alternatives (A B : OpenSquare)
    (ac : 0<A.c) (an : |A.s|≤A.c)
    (bc : 0<B.c) (bn : |B.s|≤B.c) (same : A.side=B.side)
    (aCenter : A.Inside 2 2) (aLow : A.Inside 2 (3/2))
    (aRight : A.Inside 2 (87/50))
    (bMarker : B.Inside (47/20) (33/20))
    (bRight : B.Inside 3 (87/50)) (bInner : B.Inside (113/50) 2)
    (apart : ∀ x y, ¬(A.Inside x y ∧ B.Inside x y)) :
    A.loU+A.side≤lower B A.c A.s ∨ upper A B.c B.s≤B.loU := by
  have forward (c s : ℝ) (positive : 0<c) (unit : c^2+s^2=1)
      (sep : upper A c s≤lower B c s ∨ upper B c s≤lower A c s) :
      upper A c s≤lower B c s := by
    rcases sep with yes | no
    · exact yes
    · have ap := strict_bounds A _ _ c s unit aRight
      have bp := strict_bounds B _ _ c s unit bRight
      exfalso
      nlinarith only [no,ap.1,bp.2,positive]
  have transverse (c s : ℝ) (positive : 0<c) (canonical : |s|≤c)
      (unit : c^2+s^2=1)
      (sep : upper A (-s) c≤lower B (-s) c ∨
        upper B (-s) c≤lower A (-s) c) : False := by
    have bounds := abs_le.mp canonical
    have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
    rcases sep with forward | reverse
    · have ap := strict_bounds A _ _ (-s) c normal aCenter
      have bp := strict_bounds B _ _ (-s) c normal bMarker
      nlinarith only [forward,ap.2,bp.1,bounds.1]
    · have ap := strict_bounds A _ _ (-s) c normal aLow
      have bp := strict_bounds B _ _ (-s) c normal bInner
      nlinarith only [reverse,ap.1,bp.2,bounds.2,positive]
  have axes := CongruentSAT.faceSeparation_of_disjoint A B same apart
  change pairRadius A B≤|A.c*(centerX B-centerX A)+A.s*(centerY B-centerY A)| ∨
    pairRadius A B≤|-A.s*(centerX B-centerX A)+A.c*(centerY B-centerY A)| ∨
    pairRadius B A≤|B.c*(centerX B-centerX A)+B.s*(centerY B-centerY A)| ∨
    pairRadius B A≤|-B.s*(centerX B-centerX A)+B.c*(centerY B-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius B nx ny=R)
      (sep : R≤|nx*(centerX B-centerX A)+ny*(centerY B-centerY A)|) :=
    separated A B nx ny (by rwa [identity])
  rcases axes with au | av | bu | bv
  · left
    have h := forward A.c A.s ac A.unit_normal
      (separateAxis _ _ _ (parallel_radius A B) au)
    simpa only [(ownU A).2] using h
  · exact False.elim (transverse A.c A.s ac an A.unit_normal
      (separateAxis _ _ _ (transverse_radius A B) av))
  · right
    have identity : supportRadius A B.c B.s+supportRadius B B.c B.s=pairRadius B A := by
      rw [add_comm]; exact parallel_radius B A
    have h := forward B.c B.s bc B.unit_normal (separateAxis _ _ _ identity bu)
    simpa only [(ownU B).1] using h
  · have identity : supportRadius A (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B A := by
      rw [add_comm]; exact transverse_radius B A
    exact False.elim (transverse B.c B.s bc bn B.unit_normal
      (separateAxis _ _ _ identity bv))

/-- The transposed central pair can separate only northward. Its inner
point is again explicit, rather than assumed uniformly from a saved row. -/
theorem top_alternatives (A C : OpenSquare)
    (ac : 0<A.c) (an : |A.s|≤A.c)
    (cc : 0<C.c) (cn : |C.s|≤C.c) (same : A.side=C.side)
    (aCenter : A.Inside 2 2) (aLeft : A.Inside (3/2) 2)
    (aTop : A.Inside (87/50) 2)
    (cMarker : C.Inside (33/20) (47/20))
    (cTop : C.Inside (87/50) 3) (cInner : C.Inside 2 (113/50))
    (apart : ∀ x y, ¬(A.Inside x y ∧ C.Inside x y)) :
    A.loV+A.side≤lower C (-A.s) A.c ∨ upper A (-C.s) C.c≤C.loV := by
  have forward (c s : ℝ) (positive : 0<c) (unit : c^2+s^2=1)
      (sep : upper A (-s) c≤lower C (-s) c ∨
        upper C (-s) c≤lower A (-s) c) :
      upper A (-s) c≤lower C (-s) c := by
    rcases sep with yes | no
    · exact yes
    · have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
      have ap := strict_bounds A _ _ (-s) c normal aTop
      have cp := strict_bounds C _ _ (-s) c normal cTop
      exfalso
      nlinarith only [no,ap.1,cp.2,positive]
  have longitudinal (c s : ℝ) (positive : 0<c) (canonical : |s|≤c)
      (unit : c^2+s^2=1)
      (sep : upper A c s≤lower C c s ∨ upper C c s≤lower A c s) : False := by
    have bounds := abs_le.mp canonical
    rcases sep with forward | reverse
    · have ap := strict_bounds A _ _ c s unit aCenter
      have cp := strict_bounds C _ _ c s unit cMarker
      nlinarith only [forward,ap.2,cp.1,bounds.2]
    · have ap := strict_bounds A _ _ c s unit aLeft
      have cp := strict_bounds C _ _ c s unit cInner
      nlinarith only [reverse,ap.1,cp.2,bounds.1,positive]
  have axes := CongruentSAT.faceSeparation_of_disjoint A C same apart
  change pairRadius A C≤|A.c*(centerX C-centerX A)+A.s*(centerY C-centerY A)| ∨
    pairRadius A C≤|-A.s*(centerX C-centerX A)+A.c*(centerY C-centerY A)| ∨
    pairRadius C A≤|C.c*(centerX C-centerX A)+C.s*(centerY C-centerY A)| ∨
    pairRadius C A≤|-C.s*(centerX C-centerX A)+C.c*(centerY C-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius C nx ny=R)
      (sep : R≤|nx*(centerX C-centerX A)+ny*(centerY C-centerY A)|) :=
    separated A C nx ny (by rwa [identity])
  rcases axes with au | av | cu | cv
  · exact False.elim (longitudinal A.c A.s ac an A.unit_normal
      (separateAxis _ _ _ (parallel_radius A C) au))
  · left
    have h := forward A.c A.s ac A.unit_normal
      (separateAxis _ _ _ (transverse_radius A C) av)
    simpa only [(ownV A).2] using h
  · have identity : supportRadius A C.c C.s+supportRadius C C.c C.s=pairRadius C A := by
      rw [add_comm]; exact parallel_radius C A
    exact False.elim (longitudinal C.c C.s cc cn C.unit_normal
      (separateAxis _ _ _ identity cu))
  · right
    have identity : supportRadius A (-C.s) C.c+supportRadius C (-C.s) C.c=pairRadius C A := by
      rw [add_comm]; exact transverse_radius C A
    have h := forward C.c C.s cc C.unit_normal (separateAxis _ _ _ identity cv)
    simpa only [(ownV C).1] using h

#print axioms right_alternatives
#print axioms top_alternatives
end N12Compact.C977CenterPairSeparation
