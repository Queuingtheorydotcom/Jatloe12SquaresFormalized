import Compact.Geometry.C977CenterPairSeparation
import Compact.Geometry.CentralCenterCaps
import Compact.Geometry.C977NegativeCorner

/-! A center-owning square's genuine marker cap removes its transverse
incoming axis. The neighboring transverse mode remains explicit and is
necessarily steep; no conditional inner auxiliary point is assumed. -/
namespace N12Compact.CentralCenterPairIncoming

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977NegativeCorner C977ChainBridge
set_option Elab.async false

/-- The southeast marker lies strictly within A's V strip. Its exclusion
from A is therefore on U, even though the neighboring square has an
independent signed frame. -/
theorem southeast_transverse (A : OpenSquare) (canonical : |A.s|≤A.c)
    (side : 1<A.side) (center : A.Inside 2 2)
    (cap : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s) :
    A.loV<(33/20)*A.c-(47/20)*A.s ∧
      (33/20)*A.c-(47/20)*A.s<A.loV+A.side := by
  have signs := abs_le.mp canonical
  have short : (7/10)*(A.c+A.s)<1 := by
    have squared : (A.c+A.s)^2≤2 := by
      nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s)]
    nlinarith only [squared]
  constructor
  · linarith only [cap,side,short]
  · nlinarith only [center.2.2.2,signs.1]

/-- Complete four-axis SAT reduction with only original marker, wall,
center and crosspoint data. The final mode is a genuine surviving axis. -/
theorem right_alternatives (A B : OpenSquare)
    (ac : 0<A.c) (an : |A.s|≤A.c)
    (bc : 0<B.c) (bn : |B.s|≤B.c)
    (same : A.side=B.side) (side : 1<A.side)
    (aCenter : A.Inside 2 2) (aLow : A.Inside 2 (3/2))
    (aRight : A.Inside 2 (87/50))
    (aCap : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (bMarker : B.Inside (47/20) (33/20)) (bRight : B.Inside 3 (87/50))
    (apart : ∀ x y, ¬(A.Inside x y ∧ B.Inside x y)) :
    A.loU+A.side≤lower B A.c A.s ∨
      upper A B.c B.s≤B.loU ∨
      (3*B.c<7*B.s ∧ B.loV+B.side≤lower A (-B.s) B.c) := by
  have band := southeast_transverse A an side aCenter aCap
  have forward (c s : ℝ) (positive : 0<c) (unit : c^2+s^2=1)
      (sep : upper A c s≤lower B c s ∨ upper B c s≤lower A c s) :
      upper A c s≤lower B c s := by
    rcases sep with yes | no
    · exact yes
    · have ap := strict_bounds A _ _ c s unit aRight
      have bp := strict_bounds B _ _ c s unit bRight
      exfalso
      nlinarith only [no,ap.1,bp.2,positive]
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
  · have normal : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    have bp := strict_bounds B _ _ (-A.s) A.c normal bMarker
    rcases separateAxis _ _ _ (transverse_radius A B) av with below | above
    · rw [(ownV A).2] at below
      exfalso
      nlinarith only [below,band.2,bp.1]
    · rw [(ownV A).1] at above
      exfalso
      nlinarith only [above,band.1,bp.2]
  · right; left
    have identity : supportRadius A B.c B.s+supportRadius B B.c B.s=pairRadius B A := by
      rw [add_comm]; exact parallel_radius B A
    have h := forward B.c B.s bc B.unit_normal (separateAxis _ _ _ identity bu)
    simpa only [(ownU B).1] using h
  · have identity : supportRadius A (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B A := by
      rw [add_comm]; exact transverse_radius B A
    have normal : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have bp := strict_bounds B _ _ (-B.s) B.c normal bMarker
    rcases separateAxis _ _ _ identity bv with below | above
    · have ap := strict_bounds A _ _ (-B.s) B.c normal aCenter
      have signs := abs_le.mp bn
      exfalso
      nlinarith only [below,ap.2,bp.1,signs.1]
    · right; right
      have ap := strict_bounds A _ _ (-B.s) B.c normal aLow
      refine ⟨by nlinarith only [above,ap.1,bp.2],?_⟩
      simpa only [(ownV B).2] using above

private noncomputable def swapFrame (A : OpenSquare) : OpenSquare where
  c := A.c
  s := -A.s
  loU := A.loV
  loV := A.loU
  side := A.side
  unit_normal := by nlinarith only [A.unit_normal]
  side_pos := A.side_pos

private theorem inside_swapFrame (A : OpenSquare) (x y : ℝ) :
    (swapFrame A).Inside x y↔A.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

private theorem upper_swapFrame (A : OpenSquare) (x y : ℝ) :
    upper (swapFrame A) x y=upper A y x := by
  rw [upper_in_bands,upper_in_bands]
  dsimp only [swapFrame]
  rw [show x*A.c+y*(-A.s)= -y*A.s+x*A.c by ring,
    show -x*(-A.s)+y*A.c=y*A.c+x*A.s by ring]
  ring

private theorem lower_swapFrame (A : OpenSquare) (x y : ℝ) :
    lower (swapFrame A) x y=lower A y x := by
  rw [lower_in_bands,lower_in_bands]
  dsimp only [swapFrame]
  rw [show x*A.c+y*(-A.s)= -y*A.s+x*A.c by ring,
    show -x*(-A.s)+y*A.c=y*A.c+x*A.s by ring]
  ring

theorem top_alternatives (A C : OpenSquare)
    (ac : 0<A.c) (an : |A.s|≤A.c)
    (cc : 0<C.c) (cn : |C.s|≤C.c)
    (same : A.side=C.side) (side : 1<A.side)
    (aCenter : A.Inside 2 2) (aLeft : A.Inside (3/2) 2)
    (aTop : A.Inside (87/50) 2)
    (aCap : A.loU+A.side≤(47/20)*A.c+(33/20)*A.s)
    (cMarker : C.Inside (33/20) (47/20)) (cTop : C.Inside (87/50) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ C.Inside x y)) :
    A.loV+A.side≤lower C (-A.s) A.c ∨
      upper A (-C.s) C.c≤C.loV ∨
      (7*C.s< -3*C.c ∧ C.loU+C.side≤lower A C.c C.s) := by
  have aCanonical : |(swapFrame A).s|≤(swapFrame A).c := by
    simpa only [swapFrame,abs_neg] using an
  have cCanonical : |(swapFrame C).s|≤(swapFrame C).c := by
    simpa only [swapFrame,abs_neg] using cn
  have cap : (swapFrame A).loV+(swapFrame A).side≤
      (47/20)*(swapFrame A).c-(33/20)*(swapFrame A).s := by
    dsimp only [swapFrame]
    linarith only [aCap]
  have result := right_alternatives (swapFrame A) (swapFrame C)
    ac aCanonical cc cCanonical same side
    ((inside_swapFrame A _ _).mpr aCenter) ((inside_swapFrame A _ _).mpr aLeft)
    ((inside_swapFrame A _ _).mpr aTop) cap
    ((inside_swapFrame C _ _).mpr cMarker) ((inside_swapFrame C _ _).mpr cTop)
    (fun x y h => apart y x ⟨(inside_swapFrame A _ _).mp h.1,
      (inside_swapFrame C _ _).mp h.2⟩)
  rcases result with first | second | third
  · left
    change A.loV+A.side≤lower (swapFrame C) A.c (-A.s) at first
    simpa only [lower_swapFrame] using first
  · right; left
    change upper (swapFrame A) C.c (-C.s)≤C.loV at second
    simpa only [upper_swapFrame] using second
  · right; right
    rcases third with ⟨slope,bound⟩
    refine ⟨?_,?_⟩
    · change 3*C.c<7*(-C.s) at slope
      linarith only [slope]
    · change C.loU+C.side≤lower (swapFrame A) (-(-C.s)) C.c at bound
      simpa only [neg_neg,lower_swapFrame] using bound

#print axioms southeast_transverse
#print axioms right_alternatives
#print axioms top_alternatives
end N12Compact.CentralCenterPairIncoming
