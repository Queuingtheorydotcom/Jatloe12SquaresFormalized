import Compact.Geometry.ThreeSquareOriginal
import Compact.Geometry.LongSection

/-! The complete original-square terminal at the archive's radius interface.
The finite case-entry enclosures and their coverage are the remaining inputs;
no long-section, SAT, or point-transfer theorem is assumed here. -/
namespace N12Compact.ThreeSquare
open S12 S12Pilot FourSquareAnchors LongSectionGeometry

private theorem radius_entrance (q : OpenSquare) (ha : 1 < q.side)
    (normal : NearHorizontal q.c q.s) (box : InsideContainer q)
    (radius : centerY q - 35 / 72 ≤ sectionRadius q) :
    (1 / 2 ≤ centerY q ∧ centerY q ≤ 1) ∧
      |(35 / 72 : ℝ) - centerY q| ≤ sectionRadius q := by
  have hc := cosine_bounds q.c q.s normal q.unit_normal
  have bound : centerY q - 35 / 72 ≤
      (q.c + |q.s| - 2 * q.c * |q.s|) / 2 := by
    simpa only [sectionRadius, abs_mul, abs_of_pos hc.1, mul_assoc] using radius
  have height := height_band q.side q.c q.s (centerY q) ha hc.1.le q.unit_normal
    (bottom_wall q hc.1.le box) bound
  constructor
  · exact ⟨height.1.le, by linarith [height.2]⟩
  · rw [abs_of_neg (by linarith [height.1] : (35 / 72 : ℝ) - centerY q < 0)]
    linarith only [radius]

/-- The three-square forced-point deduction with all long sections and
separating axes derived from the original geometry. This is the archived
three-square statement under the already required packing normalization.
No ordering of angles or target long-section construction is needed. -/
theorem forced_point_of_radius (A E D : OpenSquare)
    (sameAE : A.side = E.side) (sameAD : A.side = D.side)
    (ha : 1 < A.side) (cap : A.side ≤ 1001 / 1000)
    (normalA : NearHorizontal A.c A.s) (normalE : NearHorizontal E.c E.s)
    (normalD : NearHorizontal D.c D.s)
    (xA : 1 ≤ centerX A ∧ centerX A ≤ 3 / 2)
    (xE : 2 ≤ centerX E ∧ centerX E ≤ 5 / 2)
    (xD : 3 ≤ centerX D ∧ centerX D ≤ 7 / 2)
    (boxA : InsideContainer A) (boxE : InsideContainer E) (boxD : InsideContainer D)
    (point : ClosedInside E 2 1)
    (radiusA : centerY A - 35 / 72 ≤ sectionRadius A)
    (radiusE : centerY E - 35 / 72 ≤ sectionRadius E)
    (radiusD : centerY D - 35 / 72 ≤ sectionRadius D)
    (apartAE : ∀ x y, ¬ (A.Inside x y ∧ E.Inside x y))
    (apartED : ∀ x y, ¬ (E.Inside x y ∧ D.Inside x y)) : A.Inside 1 1 := by
  have he : 1 < E.side := by simpa only [← sameAE] using ha
  have hd : 1 < D.side := by simpa only [← sameAD] using ha
  have entranceA := radius_entrance A ha normalA boxA radiusA
  have entranceE := radius_entrance E he normalE boxE radiusE
  have entranceD := radius_entrance D hd normalD boxD radiusD
  exact forced_point_compact A E D sameAE sameAD ha cap normalA normalE xA xE
    (by linarith [xE.2, xD.1]) entranceA.1 entranceE.1 boxA boxD point
    (horizontal_long_section E (35 / 72) he entranceE.2)
    (horizontal_long_section D (35 / 72) hd entranceD.2) apartAE apartED

#print axioms forced_point_of_radius
end N12Compact.ThreeSquare
