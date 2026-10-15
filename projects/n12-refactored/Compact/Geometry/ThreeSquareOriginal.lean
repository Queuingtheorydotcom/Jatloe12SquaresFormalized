import Compact.Geometry.ThreeSquareForcedPoint
import Compact.Geometry.ThreeSquareSupport
import Compact.Geometry.BorderEndpoint
import Compact.Bridge.CongruentSAT

/-!
Terminal three-square theorem in the original OpenSquare model. All missing
legacy SquareAxes/LongChordGeometry imports have been removed. Equal sides
and the upper side bound are the original normalized-packing premises.

The negative scalar cancellation is extracted from the existing C709
PointTransfer.negative_transfer_scalar, with its mathematical hypotheses
unchanged. The positive branch uses the compact endpoint calculation and
actual long sections. Entry enclosure/radius proofs remain separate.
-/
namespace N12Compact.ThreeSquare
open S12 S12Pilot S12Completion.C977 C977ChainBridge
open FourSquareAnchors SectionCapacity
noncomputable section

private theorem pair_radius_gt_one (q r : OpenSquare)
    (same : q.side = r.side) (ha : 1 < q.side) : 1 < pairRadius q r := by
  have unit := normal_pair_unit q r
  have hdot := abs_nonneg (normalDot q r)
  have hcross := abs_nonneg (normalCross q r)
  have lower : 1 ≤ |normalDot q r| + |normalCross q r| := by
    nlinarith [sq_abs (normalDot q r), sq_abs (normalCross q r), mul_nonneg hdot hcross]
  have scaled := mul_le_mul_of_nonneg_left lower (half_pos q.side_pos).le
  dsimp [pairRadius]
  rw [← same]
  nlinarith only [scaled, ha]

private theorem forward_separation (q r : OpenSquare)
    (same : q.side = r.side) (ha : 1 < q.side)
    (apart : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y))
    (vq : |-q.s * (centerX r - centerX q) + q.c * (centerY r - centerY q)| < 1)
    (vr : |-r.s * (centerX r - centerX q) + r.c * (centerY r - centerY q)| < 1)
    (bq : -1 < q.c * (centerX r - centerX q) + q.s * (centerY r - centerY q))
    (br : -1 < r.c * (centerX r - centerX q) + r.s * (centerY r - centerY q)) :
    pairRadius q r ≤ q.c * (centerX r - centerX q) + q.s * (centerY r - centerY q) ∨
    pairRadius r q ≤ r.c * (centerX r - centerX q) + r.s * (centerY r - centerY q) := by
  have hq := pair_radius_gt_one q r same ha
  have hr := pair_radius_gt_one r q same.symm (by simpa only [← same] using ha)
  have sat := CongruentSAT.faceSeparation_of_disjoint q r same apart
  change pairRadius q r ≤ |q.c * (centerX r - centerX q) + q.s * (centerY r - centerY q)| ∨
    pairRadius q r ≤ |-q.s * (centerX r - centerX q) + q.c * (centerY r - centerY q)| ∨
    pairRadius r q ≤ |r.c * (centerX r - centerX q) + r.s * (centerY r - centerY q)| ∨
    pairRadius r q ≤ |-r.s * (centerX r - centerX q) + r.c * (centerY r - centerY q)| at sat
  rcases sat with sep | sep | sep | sep
  · left
    by_cases h : 0 ≤ q.c * (centerX r - centerX q) + q.s * (centerY r - centerY q)
    · simpa only [abs_of_nonneg h] using sep
    · rw [abs_of_neg (lt_of_not_ge h)] at sep
      linarith only [sep, hq, bq]
  · linarith only [sep, hq, vq]
  · right
    by_cases h : 0 ≤ r.c * (centerX r - centerX q) + r.s * (centerY r - centerY q)
    · simpa only [abs_of_nonneg h] using sep
    · rw [abs_of_neg (lt_of_not_ge h)] at sep
      linarith only [sep, hr, br]
  · linarith only [sep, hr, vr]

/-- C709's negative transfer cancellation, retaining weak wall/support
inequalities and strict side excess. -/
private theorem negative_scalar (a c s k y : ℝ)
    (ha : 1 < a) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ 0)
    (hunit : c ^ 2 + s ^ 2 = 1) (hk1 : k ≤ 1)
    (wall : a * (c - s) / 2 ≤ y) (cap : y ≤ 3 / 2)
    (gap : a * (1 + (s * k + c * |k|) / 2) ≤ c + k * (1 - y)) : False := by
  have hcs : 1 ≤ c - s := by
    nlinarith [mul_nonneg hc0 (show 0 ≤ -s by linarith)]
  by_cases hk : 0 ≤ k
  · rw [abs_of_nonneg hk] at gap
    have w := mul_le_mul_of_nonneg_left wall hk
    have hp := mul_nonneg hc0 hk
    have factor := mul_nonneg (show 0 ≤ 1 - c by linarith) (show 0 ≤ 1 - k by linarith)
    have margin := mul_pos (show 0 < a - 1 by linarith) (show 0 < 1 + c * k by nlinarith)
    nlinarith only [gap, w, factor, margin]
  · have hk0 : k < 0 := lt_of_not_ge hk
    rw [abs_of_neg hk0] at gap
    have upper := mul_le_mul_of_nonneg_left cap (show 0 ≤ -k by linarith)
    have factor := mul_nonneg (show 0 ≤ c - s - 1 by linarith) (show 0 ≤ -k by linarith)
    have hkprod := mul_nonneg (show 0 ≤ c - s by linarith) (show 0 ≤ -k by linarith)
    have margin := mul_pos (show 0 < a - 1 by linarith)
      (show 0 < 1 - (c - s) * k / 2 by nlinarith)
    nlinarith only [gap, upper, factor, margin, hc1]

private theorem negative_corner (A E : OpenSquare)
    (same : A.side = E.side) (ha : 1 < A.side)
    (normalA : NearHorizontal A.c A.s) (normalE : NearHorizontal E.c E.s)
    (hs : A.s ≤ 0)
    (xA : 1 ≤ centerX A ∧ centerX A ≤ 3 / 2)
    (xE : 2 ≤ centerX E ∧ centerX E ≤ 5 / 2)
    (yA : 1 / 2 ≤ centerY A ∧ centerY A ≤ 1)
    (yE : 1 / 2 ≤ centerY E ∧ centerY E ≤ 1)
    (box : InsideContainer A) (point : ClosedInside E 2 1)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ E.Inside x y)) : A.Inside 1 1 := by
  have hc := cosine_bounds A.c A.s normalA A.unit_normal
  have hC := cosine_bounds E.c E.s normalE E.unit_normal
  have bands := corner_nonpositive A.side A.c A.s (centerX A) (centerY A)
    ha hc.1.le hc.2 hs (by linarith [(abs_le.mp normalA.2).1]) xA yA
  by_contra missing
  have left : A.c * (1 - centerX A) + A.s * (1 - centerY A) ≤ -A.side / 2 := by
    by_contra hn
    apply missing
    apply (inside_centered_iff A 1 1).mpr
    dsimp [InBands]
    exact ⟨lt_of_not_ge hn, by linarith [bands.1], bands.2.1, by linarith [bands.2.2]⟩
  have dx : 1 / 2 ≤ centerX E - centerX A ∧ centerX E - centerX A ≤ 3 / 2 := by
    constructor <;> linarith [xA.1, xA.2, xE.1, xE.2]
  have dy : |centerY E - centerY A| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [yA.1, yA.2, yE.1, yE.2]
  have pA := projection_bounds A.c A.s _ _ normalA A.unit_normal dx dy
  have pE := projection_bounds E.c E.s _ _ normalE E.unit_normal dx dy
  rcases forward_separation A E same ha apart pA.1 pE.1 pA.2 pE.2 with sep | sep
  · have support := closed_support E 2 1 A.c A.s point
    have rad : supportRadius E A.c A.s =
        E.side / 2 * (|normalDot A E| + |normalCross A E|) := by
      dsimp [supportRadius, normalDot, normalCross]
      rw [show -A.c * E.s + A.s * E.c = -(A.c * E.s - A.s * E.c) by ring, abs_neg]
    rw [rad] at support
    have lower := (abs_le.mp support).1
    dsimp [pairRadius] at sep
    nlinarith only [sep, lower, left, ha, hc.2]
  · have pointLower := (abs_le.mp (closed_coordinates E 2 1 point).1).1
    have support : A.side / 2 * (|normalDot E A| + |normalCross E A|) ≤
        E.c * (2 - centerX A) + E.s * (1 - centerY A) := by
      dsimp [pairRadius] at sep
      nlinarith only [sep, pointLower]
    let k := (A.c * E.s - A.s * E.c) / E.c
    have coefficient : E.c * k = A.c * E.s - A.s * E.c := by
      dsimp [k]
      field_simp [ne_of_gt hC.1] <;> ring
    have relative := relative_bounds A.c A.s E.c E.s k normalA normalE
      A.unit_normal E.unit_normal coefficient
    have cross : |normalCross E A| = E.c * |k| := by
      have he : normalCross E A = -(E.c * k) := by
        dsimp [normalCross]
        nlinarith only [coefficient]
      rw [he, abs_neg, abs_mul, abs_of_pos hC.1]
    have dot : normalDot E A = A.c * E.c + A.s * E.s := by dsimp [normalDot]; ring
    rw [dot, abs_of_nonneg relative.1, cross] at support
    have support' := mul_le_mul_of_nonneg_left support hc.1.le
    have left' := mul_le_mul_of_nonneg_left left hC.1.le
    have identity : A.c * (A.c * E.c + A.s * E.s) = E.c * (1 + A.s * k) := by
      calc
        _ = E.c * (A.c ^ 2 + A.s ^ 2) + A.s * (A.c * E.s - A.s * E.c) := by ring
        _ = E.c * (1 + A.s * k) := by rw [A.unit_normal, ← coefficient]; ring
    have gap : A.side * (1 + (A.s * k + A.c * |k|) / 2) ≤
        A.c + k * (1 - centerY A) := by
      apply (mul_le_mul_left hC.1).mp
      calc
        E.c * (A.side * (1 + (A.s * k + A.c * |k|) / 2)) =
            A.side / 2 * (E.c * (1 + A.s * k) + A.c * E.c * |k| + E.c) := by ring
        _ = A.side / 2 *
            (A.c * (A.c * E.c + A.s * E.s) + A.c * E.c * |k| + E.c) := by rw [← identity]
        _ = A.c * (A.side / 2 * (A.c * E.c + A.s * E.s + E.c * |k|)) +
            E.c * (A.side / 2) := by ring
        _ ≤ A.c * (E.c * (2 - centerX A) + E.s * (1 - centerY A)) -
            E.c * (A.c * (1 - centerX A) + A.s * (1 - centerY A)) := by
          linarith only [support', left']
        _ = E.c * A.c + (A.c * E.s - A.s * E.c) * (1 - centerY A) := by ring
        _ = E.c * (A.c + k * (1 - centerY A)) := by rw [← coefficient]; ring
    have wall := bottom_wall A hc.1.le box
    rw [abs_of_nonpos hs] at wall
    exact negative_scalar A.side A.c A.s k (centerY A) ha hc.1.le hc.2 hs
      A.unit_normal relative.2 (by simpa only [sub_eq_add_neg] using wall)
      (by linarith [yA.2]) gap

/-- Two actual long follower sections force the original target square to
own `(1,1)`. All premises are supplied by the original normalized packing
and the intended continuous case-entry bounds. No target chord is required.
-/
theorem forced_point_compact (A E D : OpenSquare)
    (sameAE : A.side = E.side) (sameAD : A.side = D.side)
    (ha : 1 < A.side) (cap : A.side ≤ 1001 / 1000)
    (normalA : NearHorizontal A.c A.s) (normalE : NearHorizontal E.c E.s)
    (xA : 1 ≤ centerX A ∧ centerX A ≤ 3 / 2)
    (xE : 2 ≤ centerX E ∧ centerX E ≤ 5 / 2)
    (orderED : centerX E ≤ centerX D)
    (yA : 1 / 2 ≤ centerY A ∧ centerY A ≤ 1)
    (yE : 1 / 2 ≤ centerY E ∧ centerY E ≤ 1)
    (boxA : InsideContainer A) (boxD : InsideContainer D)
    (point : ClosedInside E 2 1)
    (sectionE : LongSection E (35 / 72)) (sectionD : LongSection D (35 / 72))
    (apartAE : ∀ x y, ¬ (A.Inside x y ∧ E.Inside x y))
    (apartED : ∀ x y, ¬ (E.Inside x y ∧ D.Inside x y)) : A.Inside 1 1 := by
  by_cases hs : 0 < A.s
  · have hc := cosine_bounds A.c A.s normalA A.unit_normal
    have band := endpoint_band A.c A.s normalA A.unit_normal
    have hlo : (A.c + A.s - 1) / A.c < (35 / 72 : ℝ) := by
      apply (div_lt_iff₀ hc.1).mpr
      linarith [normalA.1, (abs_le.mp normalA.2).2, hc.2]
    have hhi : (35 / 72 : ℝ) ≤ A.c / (1 + A.c) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + A.c)).mpr
      exact band.2.2
    have wall := bottom_wall A hc.1.le boxA
    rw [abs_of_pos hs] at wall
    have bands := corner_nonnegative A.side A.c A.s (centerX A) (centerY A)
      ha hc.1.le hc.2 hs.le (abs_le.mp normalA.2).2 xA yA
    by_contra missing
    have face : A.side / 2 ≤ A.s * (centerX A - 1) + A.c * (1 - centerY A) := by
      by_contra hn
      apply missing
      apply (inside_centered_iff A 1 1).mpr
      dsimp [InBands]
      exact ⟨bands.1, by linarith [bands.2.1], bands.2.2, by linarith⟩
    let l := centerX A + (A.s * (centerY A - 35 / 72) - A.side / 2) / A.c
    let ru := l + A.side / A.c
    let rv := centerX A + (A.c * (35 / 72 - centerY A) + A.side / 2) / A.s
    have bounds := BorderEndpoint.positive_endpoints A.side A.c A.s (centerX A) (centerY A)
      1 (35 / 72) ha hc.1 hs band.1 (by nlinarith [A.unit_normal]) hlo hhi
      (by norm_num) (by linarith [xA.2]) face wall
    change 35 / 72 < centerY A ∧ 1 < l ∧ l < centerX A ∧ centerX A < 1 + A.side ∧
      1 + A.side < ru ∧ 1 + A.side < rv at bounds
    have segmentA : ∀ x, centerX A < x → x < 1 + A.side → A.Inside x (35 / 72) := by
      intro x hx0 hx1
      have hb := BorderEndpoint.inside_bands_of_endpoints A.side A.c A.s (centerX A)
        (centerY A) (35 / 72) x (by linarith) hc.1 hs bounds.1 hx0.le
        (by change l < x; linarith [bounds.2.2.1])
        (by change x < ru; linarith [bounds.2.2.2.2.1])
        (by change x < rv; linarith [bounds.2.2.2.2.2])
      apply (inside_centered_iff A x (35 / 72)).mpr
      dsimp [InBands]
      exact ⟨hb.1, by linarith [hb.2.1], hb.2.2.1, by linarith [hb.2.2.2]⟩
    obtain ⟨lE, uE, longE, insideE⟩ := sectionE
    obtain ⟨lD, uD, longD, insideD⟩ := sectionD
    have crossE := section_crosses_center E (35 / 72) lE uE
      (by simpa only [← sameAE] using cap) longE insideE
    have crossD := section_crosses_center D (35 / 72) lD uD
      (by simpa only [← sameAD] using cap) longD insideD
    have beforeE := ordered_sections A E (35 / 72) (centerX A) (1 + A.side) lE uE
      bounds.2.2.2.1 (by linarith) segmentA insideE
      (by linarith [xA.2, xE.1, crossE.2]) apartAE
    have beforeD := ordered_sections E D (35 / 72) lE uE lD uD
      (by linarith) (by linarith) insideE insideD
      (by linarith [crossE.1, crossD.2, orderED]) apartED
    have last := section_right_wall D (35 / 72) lD uD (by linarith) insideD boxD
    linarith only [ha, beforeE, beforeD, longE, longD, last]
  · exact negative_corner A E sameAE ha normalA normalE (le_of_not_gt hs)
      xA xE yA yE boxA point apartAE

end
end N12Compact.ThreeSquare
