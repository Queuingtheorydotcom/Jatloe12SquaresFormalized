import Compact.Completion.C1092.MPPMAllNonpositiveCore
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointEnvelope

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING sections 4--5 scalar bounds.
Finite circle differences replace the two monotonicity arguments. The
quarter-slope contradiction is compared with the exact rational unit
point (40/41,9/41), so no radical endpoint is required. -/
namespace N12Compact.C1092MPPMAllNonpositive
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

theorem sine_small {c s : ℝ} (cn : Normal c s) : s<71/100 := by
  have cb := normal_bounds cn
  have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [cb.1,cn.1])
  apply lt_of_not_ge
  intro high
  have square := mul_nonneg (show 0≤s-71/100 by linarith only [high])
    (show 0≤s+71/100 by linarith only [cn.1])
  nlinarith only [product,square,cn.2.2]

structure MissingBounds (b r : ℝ) : Prop where
  cosine : b<369/500
  sineLow : 27/40<r
  sineHigh : r<71/100
  sum : 141/100<b+r
  difference : b-r<31/500

theorem missing_bounds {b r : ℝ} (bn : Normal b r) (large : 252/373≤r) :
    MissingBounds b r := by
  have bb := normal_bounds bn
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := cosine_order bn endpoint large
  have sum := CommonCases.UnitCircleChord.increasing (A:=(1:ℝ)) (B:=1)
    (show 0<b by linarith only [bb.1]) (by norm_num : (0:ℝ)≤275/373)
    bn.2.2 endpoint.2.2 bn.1 endpoint.1 large (by norm_num) (by norm_num)
    (by linarith only [bn.2.1])
  exact ⟨by linarith only [cosine],by linarith only [large],sine_small bn,
    by linarith only [sum],by linarith only [cosine,large]⟩

def predecessorF (b r : ℝ) : ℝ := 1+b*r-b-r
def predecessorG (b r : ℝ) : ℝ := b^2-b+r

theorem predecessor_coefficients {b r : ℝ} (bn : Normal b r)
    (large : 252/373≤r) : predecessorF b r<43/500 ∧ 12/25<predecessorG b r := by
  have bb := normal_bounds bn
  have mb := missing_bounds bn large
  have sumUpper : b+r≤99/70 := by
    apply le_of_not_gt
    intro high
    have product := mul_pos (show 0<b+r-99/70 by linarith only [high])
      (show 0<b+r+99/70 by linarith only [bb.1,bn.1])
    nlinarith only [product,bn.2.2,sq_nonneg (b-r)]
  have fProduct := mul_nonneg (sub_nonneg.mpr sumUpper)
    (show 0≤99/70+(b+r)-2 by linarith only [mb.sum])
  have fBound : predecessorF b r<43/500 := by
    dsimp only [predecessorF]
    nlinarith only [fProduct,bn.2.2]
  have difference := sub_nonneg.mpr bn.2.1
  have factor : 0≤1-(b+r)/2 := by linarith only [bb.2.2.2.2.2]
  have first := mul_nonneg (show 0≤31/500-(b-r) by linarith only [mb.difference]) factor
  have cap : (b-r)*(1-(b+r)/2)≤(31/500)*(59/200) := by
    nlinarith only [first,mb.sum]
  have gBound : 12/25<predecessorG b r := by
    dsimp only [predecessorG]
    nlinarith only [cap,bn.2.2]
  exact ⟨fBound,gBound⟩

/-- Once the predecessor's support is known, the remaining source
angle lies strictly in the rational cone s/c<43/110<2/5. -/
theorem preliminary_angle {c s H : ℝ} (cn : Normal c s)
    (anchor : -(13/50)*s<H) (cap : H<(43/500)*c-(12/25)*s) :
    110*s<43*c ∧ 23/25<c ∧ s<19/50 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have cone : 110*s<43*c := by linarith only [anchor,cap]
  have coarse : 5*s<2*c := by linarith only [cone,cp]
  have product := mul_pos (show 0<2*c-5*s by linarith only [coarse])
    (show 0<2*c+5*s by linarith only [cp,cn.1])
  have close : 23/25<c := by
    apply lt_of_not_ge
    intro low
    have square := mul_nonneg (show 0≤23/25-c by linarith only [low])
      (show 0≤23/25+c by linarith only [cp])
    nlinarith only [product,cn.2.2,square]
  have small : s<19/50 := by
    apply lt_of_not_ge
    intro high
    have square := mul_nonneg (show 0≤s-19/50 by linarith only [high])
      (show 0≤s+19/50 by linarith only [cn.1])
    nlinarith only [product,cn.2.2,square]
  exact ⟨cone,close,small⟩

def heightGap (c s : ℝ) : ℝ := c+s-1-(13/25)*c*s-(43/500)*c^2

/-- The circle-scaled gap is increasing on the entire coarse source
interval. Its finite difference has a positive coefficient; no derivative
or angular endpoint inference is used. -/
theorem heightGap_order {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (closeC : 23/25<c) (closeD : 23/25<d)
    (smallS : s<19/50) (smallT : t<19/50) (order : s≤t) :
    heightGap c s≤heightGap d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  let B := 1-(13/25)*s-(43/500)*(c+d)
  let A := (c+d)*(1-(13/25)*d)-(s+t)*B
  have first := mul_nonneg (show 0≤c+d by linarith only [closeC,closeD])
    (show 0≤1-(13/25)*d-12/25 by linarith only [db.2.1])
  have last := mul_nonneg (add_nonneg cn.1 dn.1)
    (show 0≤1-B by dsimp only [B]; linarith only [cn.1,closeC,closeD])
  have An : 0≤A := by
    dsimp only [A] at *
    nlinarith only [first,last,closeC,closeD,smallS,smallT]
  have identity : (c+d)*(heightGap d t-heightGap c s)=(t-s)*A := by
    dsimp only [heightGap,A,B]
    linear_combination (1-(13/25)*s-(43/500)*(c+d))*dn.2.2-
      (1-(13/25)*s-(43/500)*(c+d))*cn.2.2
  have weighted : 0≤(c+d)*(heightGap d t-heightGap c s) := by
    rw [identity]
    exact mul_nonneg (sub_nonneg.mpr order) An
  have positive : 0<c+d := by linarith only [closeC,closeD]
  have result := nonneg_of_mul_nonneg_right weighted positive
  linarith only [result]

/-- The exact rational unit point (40/41,9/41) lies before slope 1/4
and has gap 16/8405. It therefore supplies a strict reserve throughout
the hypothetical quarter-slope interval. -/
theorem heightGap_positive {c s : ℝ} (cn : Normal c s)
    (close : 23/25<c) (small : s<19/50) (slope : c≤4*s) :
    0<heightGap c s := by
  have base : Normal (40/41:ℝ) (9/41) := by norm_num [Normal]
  have order : (9/41:ℝ)≤s := sine_order cn base
    (by nlinarith only [slope,cn.1])
  have increasing := heightGap_order base cn (by norm_num) close (by norm_num) small order
  have exactBase : heightGap (40/41) (9/41)=16/8405 := by norm_num [heightGap]
  rw [exactBase] at increasing
  linarith only [increasing]

end
#print axioms predecessor_coefficients
#print axioms preliminary_angle
#print axioms heightGap_positive
end N12Compact.C1092MPPMAllNonpositive
