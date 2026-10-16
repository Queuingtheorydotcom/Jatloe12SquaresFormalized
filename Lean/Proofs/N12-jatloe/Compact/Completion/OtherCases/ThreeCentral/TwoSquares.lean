import Compact.Completion.OtherCases.ThreeCentral.SteepSupport
import Compact.Geometry.ClosedFrames

/-! A square with an inward auxiliary pair cannot be disjoint from the actual
square containing the other three central markers, when its two outward
points are excluded. Every normal and both canonical signs are included.
The proof compares the complete physical squares, without angle cells. -/
namespace N12Compact.Completion.OtherCases.ThreeCentral
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C977CornerCubic
set_option Elab.async false

private theorem radius_even (q : OpenSquare) (x y : ℝ) :
    supportRadius q (-x) (-y) = supportRadius q x y := by
  unfold supportRadius
  rw [show (-x)*q.c+(-y)*q.s = -(x*q.c+y*q.s) by ring,
    show -(-x)*q.s+(-y)*q.c = -(-x*q.s+y*q.c) by ring,
    abs_neg,abs_neg]

private theorem upper_neg (q : OpenSquare) (x y : ℝ) :
    upper q (-x) (-y) = -lower q x y := by
  unfold upper lower
  rw [radius_even]
  ring

private theorem lower_neg (q : OpenSquare) (x y : ℝ) :
    lower q (-x) (-y) = -upper q x y := by
  unfold upper lower
  rw [radius_even]
  ring

/-- Three strict projection comparisons put every possible separator from
A toward H in the open positive quadrant. Reversed axes are covered by
applying the same assertion to the negated normal. -/
private theorem separator_cone (A H : OpenSquare) (x y : ℝ)
    (unit : x^2+y^2=1)
    (d : A.Inside 2 (87/50)) (q : A.Inside (87/50) 2)
    (hSE : H.Inside (47/20) (33/20))
    (hNW : H.Inside (33/20) (47/20))
    (separate : upper A x y ≤ lower H x y) : 0 < x ∧ 0 < y := by
  have ad := strict_bounds A _ _ x y unit d
  have aq := strict_bounds A _ _ x y unit q
  have se := strict_bounds H _ _ x y unit hSE
  have nw := strict_bounds H _ _ x y unit hNW
  have first : (35/100)*x < (61/100)*y := by
    nlinarith only [ad.2,nw.1,separate]
  have second : (35/100)*y < (61/100)*x := by
    nlinarith only [aq.2,se.1,separate]
  constructor <;> linarith only [first,second]

private theorem positive_impossible (A H : OpenSquare)
    (normal : Normal A.c A.s) (side : 1 < A.side) (same : A.side = H.side)
    (southwest : A.Inside (33/20) (33/20))
    (d : A.Inside 2 (87/50)) (q : A.Inside (87/50) 2)
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5))
    (hSE : H.Inside (47/20) (33/20))
    (hNE : H.Inside (47/20) (47/20))
    (hNW : H.Inside (33/20) (47/20))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) : False := by
  have no_forward (x y : ℝ) (unit : x^2+y^2=1) :
      ¬ upper A x y ≤ lower H x y := by
    intro separate
    obtain ⟨xp,yp⟩ := separator_cone A H x y unit d q hSE hNW separate
    by_cases shallow : y ≤ x
    · have support := C868CentralSupport.positive_support A x y
        ⟨yp.le,shallow,unit⟩ normal side southwest d q missingBottom missingLeft
      have foreign := (strict_bounds H _ _ x y unit hNW).1
      nlinarith only [support,foreign,separate]
    · have support := steep_support A x y normal xp (le_of_not_ge shallow)
        side southwest d q missingBottom missingLeft
      have foreign := (strict_bounds H _ _ x y unit hSE).1
      nlinarith only [support,foreign,separate]
  have no_axis (x y : ℝ) (unit : x^2+y^2=1) :
      ¬ (upper A x y ≤ lower H x y ∨ upper H x y ≤ lower A x y) := by
    rintro (separate | separate)
    · exact no_forward x y unit separate
    · have flipped : upper A (-x) (-y) ≤ lower H (-x) (-y) := by
        rw [upper_neg,lower_neg]
        linarith only [separate]
      exact no_forward (-x) (-y) (by nlinarith only [unit]) flipped
  have axes := CongruentSAT.faceSeparation_of_disjoint A H same apart
  change pairRadius A H ≤ |A.c*(centerX H-centerX A)+A.s*(centerY H-centerY A)| ∨
    pairRadius A H ≤ |-A.s*(centerX H-centerX A)+A.c*(centerY H-centerY A)| ∨
    pairRadius H A ≤ |H.c*(centerX H-centerX A)+H.s*(centerY H-centerY A)| ∨
    pairRadius H A ≤ |-H.s*(centerX H-centerX A)+H.c*(centerY H-centerY A)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius A x y+supportRadius H x y = R)
      (separate : R ≤ |x*(centerX H-centerX A)+y*(centerY H-centerY A)|) :=
    separated A H x y (by rwa [identity])
  rcases axes with au | av | hu | hv
  · exact no_axis A.c A.s A.unit_normal
      (separateAxis _ _ _ (parallel_radius A H) au)
  · exact no_axis (-A.s) A.c (by nlinarith only [A.unit_normal])
      (separateAxis _ _ _ (transverse_radius A H) av)
  · have identity : supportRadius A H.c H.s+supportRadius H H.c H.s = pairRadius H A := by
      rw [add_comm]
      exact parallel_radius H A
    exact no_axis H.c H.s H.unit_normal (separateAxis _ _ _ identity hu)
  · have identity : supportRadius A (-H.s) H.c+supportRadius H (-H.s) H.c = pairRadius H A := by
      rw [add_comm]
      exact transverse_radius H A
    exact no_axis (-H.s) H.c (by nlinarith only [H.unit_normal])
      (separateAxis _ _ _ identity hv)

/-- Unrestricted geometric obstruction shared by C705 and reflected C716.
The two outward exclusions may have different foreign owners. No wall or
side upper bound is used by this local theorem. -/
theorem impossible (A H : OpenSquare) (side : 1 < A.side) (same : A.side = H.side)
    (southwest : A.Inside (33/20) (33/20))
    (d : A.Inside 2 (87/50)) (q : A.Inside (87/50) 2)
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5))
    (hSE : H.Inside (47/20) (33/20))
    (hNE : H.Inside (47/20) (47/20))
    (hNW : H.Inside (33/20) (47/20))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) : False := by
  obtain ⟨a,cp,canonical,shape,equivalent,_⟩ := ClosedFrames.canonical_frame A
  have aSide : 1 < a.side := by simpa only [shape] using side
  have aSame : a.side = H.side := shape.trans same
  have aSW := (equivalent _ _).mpr southwest
  have aD := (equivalent _ _).mpr d
  have aQ := (equivalent _ _).mpr q
  have aBottom : ¬ a.Inside (8/5) 1 := fun h => missingBottom ((equivalent _ _).mp h)
  have aLeft : ¬ a.Inside 1 (8/5) := fun h => missingLeft ((equivalent _ _).mp h)
  have aApart : ∀ x y, ¬ (a.Inside x y ∧ H.Inside x y) := by
    intro x y h
    exact apart x y ⟨(equivalent _ _).mp h.1,h.2⟩
  by_cases sign : 0 ≤ a.s
  · exact positive_impossible a H
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,a.unit_normal⟩
      aSide aSame aSW aD aQ aBottom aLeft hSE hNE hNW aApart
  · let b := turnFrame (turnFrame (turnFrame (pullSwap a)))
    let J := pullSwap H
    have bEquivalent (x y : ℝ) : b.Inside x y ↔ a.Inside y x := by
      simp only [b,turnFrame_inside,inside_pullSwap]
    have bNormal : Normal b.c b.s := by
      refine ⟨?_,?_,b.unit_normal⟩
      · dsimp [b,turnFrame,pullSwap]
        linarith only [sign]
      · have order : -a.s ≤ a.c := by
          simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical
        simpa only [b,turnFrame,pullSwap,neg_neg] using order
    apply positive_impossible b J bNormal
      (by simpa [b,pullSwap] using aSide) (by simpa [b,J,pullSwap] using aSame)
      ((bEquivalent _ _).mpr aSW) ((bEquivalent _ _).mpr aQ)
      ((bEquivalent _ _).mpr aD)
      (fun h => aLeft ((bEquivalent _ _).mp h))
      (fun h => aBottom ((bEquivalent _ _).mp h))
    · exact (inside_pullSwap H _ _).mpr hNW
    · exact (inside_pullSwap H _ _).mpr hNE
    · exact (inside_pullSwap H _ _).mpr hSE
    · intro x y h
      exact aApart y x ⟨(bEquivalent _ _).mp h.1,(inside_pullSwap H x y).mp h.2⟩

end N12Compact.Completion.OtherCases.ThreeCentral
