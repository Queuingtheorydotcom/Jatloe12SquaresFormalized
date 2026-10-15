import Compact.Geometry.ABTransverse

/-! Directed support selectors for the original bottom boundary chain.
All bounds follow from genuine strict marker/seed points. The conclusions
retain the full supports of both squares, including their common side;
no independent center box or proposed core cutoff replaces a neighbor.
Source only, uncompiled. -/
namespace N12Compact.C696BottomChainSelectors

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

private theorem four_axes (P Q : OpenSquare) (same : P.side=Q.side)
    (apart : ∀ x y, ¬(P.Inside x y ∧ Q.Inside x y)) :
    (upper P P.c P.s≤lower Q P.c P.s ∨ upper Q P.c P.s≤lower P P.c P.s) ∨
    (upper P (-P.s) P.c≤lower Q (-P.s) P.c ∨
      upper Q (-P.s) P.c≤lower P (-P.s) P.c) ∨
    (upper P Q.c Q.s≤lower Q Q.c Q.s ∨ upper Q Q.c Q.s≤lower P Q.c Q.s) ∨
    (upper P (-Q.s) Q.c≤lower Q (-Q.s) Q.c ∨
      upper Q (-Q.s) Q.c≤lower P (-Q.s) Q.c) := by
  have axes := CongruentSAT.faceSeparation_of_disjoint P Q same apart
  change pairRadius P Q≤|P.c*(centerX Q-centerX P)+P.s*(centerY Q-centerY P)| ∨
    pairRadius P Q≤|-P.s*(centerX Q-centerX P)+P.c*(centerY Q-centerY P)| ∨
    pairRadius Q P≤|Q.c*(centerX Q-centerX P)+Q.s*(centerY Q-centerY P)| ∨
    pairRadius Q P≤|-Q.s*(centerX Q-centerX P)+Q.c*(centerY Q-centerY P)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius P nx ny+supportRadius Q nx ny=R)
      (sep : R≤|nx*(centerX Q-centerX P)+ny*(centerY Q-centerY P)|) :=
    separated P Q nx ny (by rwa [identity])
  rcases axes with pu | pv | qu | qv
  · exact Or.inl (separateAxis _ _ _ (parallel_radius P Q) pu)
  · exact Or.inr (Or.inl (separateAxis _ _ _ (transverse_radius P Q) pv))
  · have identity : supportRadius P Q.c Q.s+supportRadius Q Q.c Q.s=pairRadius Q P := by
      rw [add_comm]
      exact parallel_radius Q P
    exact Or.inr (Or.inr (Or.inl (separateAxis _ _ _ identity qu)))
  · have identity : supportRadius P (-Q.s) Q.c+supportRadius Q (-Q.s) Q.c=pairRadius Q P := by
      rw [add_comm]
      exact transverse_radius Q P
    exact Or.inr (Or.inr (Or.inr (separateAxis _ _ _ identity qv)))

def SingletonStep (O D : OpenSquare) (c s : ℝ) : Prop :=
  upper O c s≤lower D c s ∨
    ((43/130)*c < -s ∧ upper O (-s) c≤lower D (-s) c)

/-- A bottom singleton followed by the rightward bottom wall has only
its forward U separator, except at a necessarily steep negative tilt. -/
theorem singleton_wall (O D : OpenSquare)
    (oc : 0<O.c) (dc : 0<D.c)
    (os : O.s≤O.c) (ds : D.s≤D.c)
    (same : O.side=D.side)
    (oMarker : O.Inside 1 (457/500))
    (oMiddle : O.Inside (87/50) 1)
    (oFar : O.Inside (187/100) (19/25))
    (dMarker : D.Inside 2 (457/500))
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) :
    SingletonStep O D O.c O.s ∨ SingletonStep O D D.c D.s := by
  have fromU (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper O c s≤lower D c s ∨ upper D c s≤lower O c s) :
      SingletonStep O D c s := by
    left
    rcases sep with forward | backward
    · exact forward
    · have om := strict_bounds O _ _ c s unit oMarker
      have dm := strict_bounds D _ _ c s unit dMarker
      exfalso
      nlinarith only [backward,om.1,dm.2,hc]
  have fromV (c s : ℝ) (hc : 0<c) (hs : s≤c) (unit : c^2+s^2=1)
      (sep : upper O (-s) c≤lower D (-s) c ∨
        upper D (-s) c≤lower O (-s) c) : SingletonStep O D c s := by
    have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
    have om := strict_bounds O _ _ (-s) c vunit oMiddle
    have ofar := strict_bounds O _ _ (-s) c vunit oFar
    have dm := strict_bounds D _ _ (-s) c vunit dMarker
    rcases sep with forward | backward
    · right
      refine ⟨?_,forward⟩
      nlinarith only [forward,om.2,dm.1]
    · exfalso
      nlinarith only [backward,ofar.1,dm.2,hc,hs]
  rcases four_axes O D same apart with ou | ov | du | dv
  · exact Or.inl (fromU O.c O.s oc O.unit_normal ou)
  · exact Or.inl (fromV O.c O.s oc os O.unit_normal ov)
  · exact Or.inr (fromU D.c D.s dc D.unit_normal du)
  · exact Or.inr (fromV D.c D.s dc ds D.unit_normal dv)

def CornerStep (D E : OpenSquare) (c s : ℝ) : Prop :=
  upper D c s≤lower E c s ∨
    ((43/543)*c<s ∧ upper E (-s) c≤lower D (-s) c) ∨
    ((43/220)*c < -s ∧ upper D (-s) c≤lower E (-s) c)

/-- The next actual pair retains three possible directed axes per frame.
Both transverse directions require a strict tilt, with different exact
thresholds supplied by the wall reach and the paired corner markers. -/
theorem wall_corner (D E : OpenSquare) (dc : 0<D.c) (ec : 0<E.c)
    (same : D.side=E.side)
    (dMarker : D.Inside 2 (457/500))
    (dReach : D.Inside (64/25) 1)
    (eBottom : E.Inside 3 (457/500))
    (eRight : E.Inside (1543/500) 1)
    (apart : ∀ x y, ¬(D.Inside x y ∧ E.Inside x y)) :
    CornerStep D E D.c D.s ∨ CornerStep D E E.c E.s := by
  have fromU (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper D c s≤lower E c s ∨ upper E c s≤lower D c s) :
      CornerStep D E c s := by
    left
    rcases sep with forward | backward
    · exact forward
    · have dm := strict_bounds D _ _ c s unit dMarker
      have eb := strict_bounds E _ _ c s unit eBottom
      exfalso
      nlinarith only [backward,dm.1,eb.2,hc]
  have fromV (c s : ℝ) (unit : c^2+s^2=1)
      (sep : upper D (-s) c≤lower E (-s) c ∨
        upper E (-s) c≤lower D (-s) c) : CornerStep D E c s := by
    have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
    have dm := strict_bounds D _ _ (-s) c vunit dMarker
    have dr := strict_bounds D _ _ (-s) c vunit dReach
    have eb := strict_bounds E _ _ (-s) c vunit eBottom
    have er := strict_bounds E _ _ (-s) c vunit eRight
    rcases sep with forward | backward
    · right; right
      refine ⟨?_,forward⟩
      nlinarith only [forward,dr.2,eb.1]
    · right; left
      refine ⟨?_,backward⟩
      nlinarith only [backward,er.2,dm.1]
  rcases four_axes D E same apart with du | dv | eu | ev
  · exact Or.inl (fromU D.c D.s dc D.unit_normal du)
  · exact Or.inl (fromV D.c D.s D.unit_normal dv)
  · exact Or.inr (fromU E.c E.s ec E.unit_normal eu)
  · exact Or.inr (fromV E.c E.s E.unit_normal ev)

def CornerTurn (E R : OpenSquare) (c s : ℝ) : Prop :=
  upper E (-s) c≤lower R (-s) c ∨
    ((43/220)*c<s ∧ upper E c s≤lower R c s) ∨
    ((43/543)*c < -s ∧ upper R c s≤lower E c s)

/-- The same paired corner passes the full support obligation to the
right wall. This is the geometric turn of the boundary chain; the corner
is not replaced by its single inward point. -/
theorem corner_wall (E R : OpenSquare) (ec : 0<E.c) (rc : 0<R.c)
    (same : E.side=R.side)
    (eBottom : E.Inside 3 (457/500))
    (eRight : E.Inside (1543/500) 1)
    (rMarker : R.Inside (1543/500) 2)
    (rReach : R.Inside 3 (36/25))
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) :
    CornerTurn E R E.c E.s ∨ CornerTurn E R R.c R.s := by
  have fromU (c s : ℝ) (unit : c^2+s^2=1)
      (sep : upper E c s≤lower R c s ∨ upper R c s≤lower E c s) :
      CornerTurn E R c s := by
    have eb := strict_bounds E _ _ c s unit eBottom
    have er := strict_bounds E _ _ c s unit eRight
    have rm := strict_bounds R _ _ c s unit rMarker
    have rr := strict_bounds R _ _ c s unit rReach
    rcases sep with forward | backward
    · right; left
      refine ⟨?_,forward⟩
      nlinarith only [forward,er.2,rr.1]
    · right; right
      refine ⟨?_,backward⟩
      nlinarith only [backward,rm.2,eb.1]
  have fromV (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper E (-s) c≤lower R (-s) c ∨
        upper R (-s) c≤lower E (-s) c) : CornerTurn E R c s := by
    left
    rcases sep with forward | backward
    · exact forward
    · have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
      have er := strict_bounds E _ _ (-s) c vunit eRight
      have rm := strict_bounds R _ _ (-s) c vunit rMarker
      exfalso
      nlinarith only [backward,er.1,rm.2,hc]
  rcases four_axes E R same apart with eu | ev | ru | rv
  · exact Or.inl (fromU E.c E.s E.unit_normal eu)
  · exact Or.inl (fromV E.c E.s ec E.unit_normal ev)
  · exact Or.inr (fromU R.c R.s R.unit_normal ru)
  · exact Or.inr (fromV R.c R.s rc R.unit_normal rv)

def WallSingletonStep (R N : OpenSquare) (c s : ℝ) : Prop :=
  upper R (-s) c≤lower N (-s) c ∨
    ((43/130)*c<s ∧ upper R c s≤lower N c s)

/-- At the far end of the chain, the right wall passes its full support
to the opposite corner's right singleton. All reverse directions vanish;
the longitudinal exception must have a steep positive tilt. -/
theorem wall_singleton (R N : OpenSquare)
    (rc : 0<R.c) (nc : 0<N.c)
    (rs : -R.c≤R.s) (ns : -N.c≤N.s)
    (same : R.side=N.side)
    (rMarker : R.Inside (1543/500) 2)
    (nMarker : N.Inside (1543/500) 3)
    (nMiddle : N.Inside 3 (113/50))
    (nFar : N.Inside (81/25) (213/100))
    (apart : ∀ x y, ¬(R.Inside x y ∧ N.Inside x y)) :
    WallSingletonStep R N R.c R.s ∨ WallSingletonStep R N N.c N.s := by
  have fromU (c s : ℝ) (hc : 0<c) (hs : -c≤s) (unit : c^2+s^2=1)
      (sep : upper R c s≤lower N c s ∨ upper N c s≤lower R c s) :
      WallSingletonStep R N c s := by
    have rm := strict_bounds R _ _ c s unit rMarker
    have nm := strict_bounds N _ _ c s unit nMiddle
    have nf := strict_bounds N _ _ c s unit nFar
    rcases sep with forward | backward
    · right
      refine ⟨?_,forward⟩
      nlinarith only [forward,rm.2,nm.1]
    · exfalso
      nlinarith only [backward,rm.1,nf.2,hc,hs]
  have fromV (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper R (-s) c≤lower N (-s) c ∨
        upper N (-s) c≤lower R (-s) c) : WallSingletonStep R N c s := by
    left
    rcases sep with forward | backward
    · exact forward
    · have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
      have rm := strict_bounds R _ _ (-s) c vunit rMarker
      have nm := strict_bounds N _ _ (-s) c vunit nMarker
      exfalso
      nlinarith only [backward,rm.1,nm.2,hc]
  rcases four_axes R N same apart with ru | rv | nu | nv
  · exact Or.inl (fromU R.c R.s rc rs R.unit_normal ru)
  · exact Or.inl (fromV R.c R.s rc R.unit_normal rv)
  · exact Or.inr (fromU N.c N.s nc ns N.unit_normal nu)
  · exact Or.inr (fromV N.c N.s nc N.unit_normal nv)

def BottomBarrier (D : OpenSquare) : Prop :=
  (0≤D.s → D.loV+D.side≤(3/2)*D.c-2*D.s) ∧
  (D.s≤0 → 2*D.c+(3/2)*D.s≤D.loU ∨
    D.loV+D.side≤(3/2)*D.c-2*D.s)

/-- The actual southwest central crosspoint controls the bottom wall's
inward face. The negative-frame alternative retains its possible U face. -/
theorem central_bottom (D : OpenSquare) (dc : 0<D.c) (canonical : |D.s|≤D.c)
    (marker : D.Inside 2 (457/500)) (reach : D.Inside (64/25) 1)
    (missing : ¬D.Inside 2 (3/2)) : BottomBarrier D := by
  have m := marker
  have r := reach
  dsimp [OpenSquare.Inside,InBands] at m r
  constructor
  · intro sign
    by_contra no
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    have slope := (abs_le.mp canonical).2
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [m.1,m.2.2.1,r.2.1,dc,sign,slope,no]
  · intro sign
    by_contra no
    have lower : D.loU<2*D.c+(3/2)*D.s := by
      by_contra failure
      exact no (Or.inl (le_of_not_gt failure))
    have upper : (3/2)*D.c-2*D.s<D.loV+D.side := by
      by_contra failure
      exact no (Or.inr (le_of_not_gt failure))
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    refine ⟨lower,?_,?_,upper⟩ <;>
      nlinarith only [r.2.1,m.2.2.1,dc,sign]

def RightBarrier (R : OpenSquare) : Prop :=
  (R.s≤0 → (5/2)*R.c+2*R.s≤R.loU) ∧
  (0≤R.s → (5/2)*R.c+2*R.s≤R.loU ∨
    R.loV+R.side≤2*R.c-(5/2)*R.s)

/-- The actual northeast central crosspoint controls the right wall's
inward face. This is the other end of the same retained boundary chain. -/
theorem central_right (R : OpenSquare) (rc : 0<R.c) (canonical : |R.s|≤R.c)
    (marker : R.Inside (1543/500) 2) (reach : R.Inside 3 (36/25))
    (missing : ¬R.Inside (5/2) 2) : RightBarrier R := by
  have m := marker
  have r := reach
  dsimp [OpenSquare.Inside,InBands] at m r
  constructor
  · intro sign
    by_contra no
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    have slope := (abs_le.mp canonical).1
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [m.2.1,m.2.2.2,r.2.2.1,rc,sign,slope,no]
  · intro sign
    by_contra no
    have lower : R.loU<(5/2)*R.c+2*R.s := by
      by_contra failure
      exact no (Or.inl (le_of_not_gt failure))
    have upper : 2*R.c-(5/2)*R.s<R.loV+R.side := by
      by_contra failure
      exact no (Or.inr (le_of_not_gt failure))
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    refine ⟨lower,?_,?_,upper⟩ <;>
      nlinarith only [m.2.1,r.2.2.1,rc,sign]

#print axioms singleton_wall
#print axioms wall_corner
#print axioms corner_wall
#print axioms wall_singleton
#print axioms central_bottom
#print axioms central_right
end N12Compact.C696BottomChainSelectors
