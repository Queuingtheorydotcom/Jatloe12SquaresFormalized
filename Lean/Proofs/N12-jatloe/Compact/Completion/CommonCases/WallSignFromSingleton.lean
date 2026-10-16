import Compact.Geometry.WallSignChord
import Compact.Completion.CommonCases.OriginalOwners

/-! Common reduction found while comparing the thirteen remaining case
handoffs with the new C1089--C1092 proofs. A genuine foreign singleton
point fixes the wall center sign; the same physical wall then supplies
its near chord. No far auxiliary, canonical angle, finite component list
or family symmetry is a premise. All ownership is strict and the center
split includes equality. Source only, uncompiled. -/
namespace N12Compact.CommonCases.WallSignFromSingleton
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- The reflected chord would contain the actual foreign singleton
point if the center were at or below two. The omitted central point in
this reflected application is the original southwest marker. -/
theorem left_center (W : OpenSquare) (side : 1<W.side)
    (wall : ∀ x y,W.Inside x y → 0≤x)
    (marker : W.Inside (457/500) 2)
    (southwest : ¬W.Inside (33/20) (33/20))
    (singleton : ¬W.Inside 1 (87/50)) : 2<centerY W := by
  apply lt_of_not_ge
  intro low
  have reflectedSign : 2≤centerY (pullY W) := by
    rw [center_pullY_y]
    linarith only [low]
  have point := WallSignChord.chord (pullY W) side
    (fun x y own => wall x (4-y) ((inside_pullY W x y).mp own))
    (by norm_num only [inside_pullY]; exact marker)
    (by norm_num only [inside_pullY]; exact southwest)
    reflectedSign (113/50) (by norm_num) (by norm_num)
  norm_num only [inside_pullY] at point
  exact singleton point

/-- The upper chord needs a genuine northwest omission in addition to
the southwest omission used to determine the center sign. In particular
this second conclusion is not available for merged left mask6144. -/
theorem left_chord (W : OpenSquare) (side : 1<W.side)
    (wall : ∀ x y,W.Inside x y → 0≤x)
    (marker : W.Inside (457/500) 2)
    (southwest : ¬W.Inside (33/20) (33/20))
    (northwest : ¬W.Inside (33/20) (47/20))
    (singleton : ¬W.Inside 1 (87/50)) :
    2<centerY W ∧ ∀ y : ℝ,111/50≤y → y≤239/100 → W.Inside 1 y := by
  have high := left_center W side wall marker southwest singleton
  exact ⟨high,fun y low upper =>
    WallSignChord.chord W side wall marker northwest high.le y low upper⟩

/-- Transpose the entire local left-center argument, including its real
wall and foreign point. The conclusion is about the original bottom
square's center, not its frame angle. -/
theorem bottom_center (W : OpenSquare) (side : 1<W.side)
    (wall : ∀ x y,W.Inside x y → 0≤y)
    (marker : W.Inside 2 (457/500))
    (southwest : ¬W.Inside (33/20) (33/20))
    (singleton : ¬W.Inside (87/50) 1) : 2<centerX W := by
  have high := left_center (pullSwap W) side
    (fun x y own => wall y x ((inside_pullSwap W x y).mp own))
    ((inside_pullSwap W _ _).mpr marker)
    (fun own => southwest ((inside_pullSwap W _ _).mp own))
    (fun own => singleton ((inside_pullSwap W _ _).mp own))
  simpa only [center_pullSwap_y] using high

/-- The near bottom point and its whole strict chord follow without F6.
Both central omissions come from this same actual bottom square. -/
theorem bottom_chord (W : OpenSquare) (side : 1<W.side)
    (wall : ∀ x y,W.Inside x y → 0≤y)
    (marker : W.Inside 2 (457/500))
    (southwest : ¬W.Inside (33/20) (33/20))
    (southeast : ¬W.Inside (47/20) (33/20))
    (singleton : ¬W.Inside (87/50) 1) :
    2<centerX W ∧ ∀ x : ℝ,111/50≤x → x≤239/100 → W.Inside x 1 := by
  have high := bottom_center W side wall marker southwest singleton
  refine ⟨high,?_⟩
  intro x low upper
  have point := WallSignChord.chord (pullSwap W) side
    (fun u v own => wall v u ((inside_pullSwap W u v).mp own))
    ((inside_pullSwap W _ _).mpr marker)
    (fun own => southeast ((inside_pullSwap W _ _).mp own))
    (by simpa only [center_pullSwap_y] using high.le) x low upper
  exact (inside_pullSwap W _ _).mp point

theorem bottom_near (W : OpenSquare) (side : 1<W.side)
    (wall : ∀ x y,W.Inside x y → 0≤y)
    (marker : W.Inside 2 (457/500))
    (southwest : ¬W.Inside (33/20) (33/20))
    (southeast : ¬W.Inside (47/20) (33/20))
    (singleton : ¬W.Inside (87/50) 1) : W.Inside (113/50) 1 :=
  (bottom_chord W side wall marker southwest southeast singleton).2 _
    (by norm_num) (by norm_num)

/-- Family-independent actual-owner adapter. The marker membership and
omissions are checked against this owner's exact mask; the low point is
strict in the distinct actual singleton1. This covers8192 and8196 without
identifying their different marker sets. -/
theorem original_bottom (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (member : mask∈family)
    (one : 1∈family) (different : mask≠1)
    (marker : ((2,457/500) : ℚ×ℚ)∈seedPoints (maskSupport mask))
    (southwest : (8 : Marker)∉maskSupport mask)
    (southeast : (9 : Marker)∉maskSupport mask) :
    2<centerX (OriginalOwners.owner p mask) ∧
      ∀ x : ℝ,111/50≤x → x≤239/100 → (OriginalOwners.owner p mask).Inside x 1 := by
  have mark := OriginalOwners.seed family p hf mask member (2,457/500) marker
  have foreign := OriginalOwners.seed family p hf 1 one (87/50,1) (by decide +kernel)
  have sw := OriginalOwners.missing_marker family p hf mask member 8 southwest
  have se := OriginalOwners.missing_marker family p hf mask member 9 southeast
  norm_num [S12.marker] at mark foreign sw se
  exact bottom_chord _ (OriginalOwners.side p mask)
    (fun x y own => (OriginalOwners.box p mask x y own).2.2.1) mark sw se
    (fun own => OriginalOwners.apart family p hf mask 1 member one different _ _ ⟨own,foreign⟩)

/-- The actual left-center adapter deliberately needs no northwest
omission. It therefore retains the correct6144 hypothesis for C976. -/
theorem original_left_center (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (member : mask∈family)
    (two : 2∈family) (different : mask≠2)
    (marker : ((457/500,2) : ℚ×ℚ)∈seedPoints (maskSupport mask))
    (southwest : (8 : Marker)∉maskSupport mask) :
    2<centerY (OriginalOwners.owner p mask) := by
  have mark := OriginalOwners.seed family p hf mask member (457/500,2) marker
  have foreign := OriginalOwners.seed family p hf 2 two (1,87/50) (by decide +kernel)
  have sw := OriginalOwners.missing_marker family p hf mask member 8 southwest
  norm_num [S12.marker] at mark foreign sw
  exact left_center _ (OriginalOwners.side p mask)
    (fun x y own => (OriginalOwners.box p mask x y own).1) mark sw
    (fun own => OriginalOwners.apart family p hf mask 2 member two different _ _ ⟨own,foreign⟩)

end
#print axioms left_center
#print axioms bottom_chord
#print axioms original_bottom
#print axioms original_left_center
end N12Compact.CommonCases.WallSignFromSingleton
