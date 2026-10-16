import Compact.Geometry.C977NegativeCorner

/-! A positive canonical central square that misses (2,2) can only lie
above its actual bottom singleton on one of their transverse axes. Both
signs of the bottom frame are allowed. The two strict central crosspoints
are original geometric deductions, retained explicitly in this interface. -/
namespace N12Compact.PositiveCentralTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977NegativeCorner

theorem central_margin {C S : ℝ} (h : Normal C S) :
    (13/100)*C+(31/25)*S < 1 := by
  have b := normal_bounds h
  linarith only [h.2.1,b.2.2.2.2.2]

private theorem product_margin {C S : ℝ} (h : Normal C S) :
    9/10 ≤ (C+S)*(1-S/2) := by
  have b := normal_bounds h
  have product := mul_nonneg
    (show 0≤C+S-1 by linarith only [b.2.2.2.2.1])
    (show 0≤3/2-(C+S) by linarith only [b.2.2.2.2.2])
  have sum : (4/5)*C*S ≤ C+S-1 := by nlinarith only [product,h.2.2]
  have orderSquare := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
  have squareOrder := mul_nonneg (sub_nonneg.mpr h.2.1)
    (show 0≤C+S by linarith only [b.1,h.1])
  have half : S^2≤1/2 := by nlinarith only [squareOrder,h.2.2]
  nlinarith only [sum,orderSquare,half]

theorem smaller_angle {c s C S : ℝ} (hc : 0<c) (h : Normal C S)
    (order : 0≤c*S-s*C) :
    c*(2-S^2/2-C)+s*(2+C*S/2-S) < (187/100)*c+(19/25)*s := by
  have b := normal_bounds h
  have hC : 0<C := by linarith only [b.1]
  have cs := mul_nonneg (le_trans h.1 h.2.1) h.1
  have coefficient : 0≤31/25-S+C*S/2 := by
    nlinarith only [b.2.2.2.1,cs]
  have positive := mul_pos hc (sub_pos.mpr (central_margin h))
  have nonnegative := mul_nonneg order coefficient
  have identity :
      C*((187/100)*c+(19/25)*s-
        (c*(2-S^2/2-C)+s*(2+C*S/2-S))) =
      c*(1-(13/100)*C-(31/25)*S)+(c*S-s*C)*(31/25-S+C*S/2) := by
    linear_combination c*h.2.2
  have scaled : 0<C*((187/100)*c+(19/25)*s-
      (c*(2-S^2/2-C)+s*(2+C*S/2-S))) := by
    linarith only [identity,positive,nonnegative]
  have gap := pos_of_mul_pos_right scaled hC.le
  linarith only [gap]

theorem larger_angle {c s C S : ℝ} (hc : 0<c) (hs : s≤c) (h : Normal C S) :
    c*(2+C*S/2-C)+s*(3/2+S^2/2-S) < (187/100)*c+(19/25)*s := by
  have margin := product_margin h
  have negative : S-S^2/2-37/50≤0 := by nlinarith only [sq_nonneg (S-1)]
  have replacement := mul_nonneg (sub_nonneg.mpr hs) (neg_nonneg.mpr negative)
  have positive := mul_pos hc (show 0<(3/100:ℝ) by norm_num)
  have weighted := mul_nonneg hc.le
    (show 0≤(C+S)*(1-S/2)-9/10 by linarith only [margin])
  nlinarith only [replacement,positive,weighted]

/-- Actual full-square disjointness reduces to exactly two forward
transverse supports. Equality of supporting faces remains permitted. -/
theorem alternatives (O A : OpenSquare)
    (oc : 0<O.c) (canonicalO : |O.s|≤O.c) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side)
    (oN : O.Inside (28/25) 1) (oF : O.Inside (187/100) (19/25))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aLeft : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (apart : ∀ x y, ¬ (O.Inside x y ∧ A.Inside x y)) :
    O.loV+O.side ≤ lower A (-O.s) O.c ∨
      upper O (-A.s) A.c ≤ A.loV := by
  have ab := normal_bounds an
  have ac : 0<A.c := by linarith only [ab.1]
  have os := abs_le.mp canonicalO
  let K := O.c*A.c+O.s*A.s
  let H := -O.c*A.s+O.s*A.c
  have kp : 0≤K := by
    have first := mul_nonneg oc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (show 0≤O.c+O.s by linarith only [os.1])
    dsimp [K]
    nlinarith only [first,second]
  have leftPoint := aLeft
  have lowPoint := aLow
  dsimp [OpenSquare.Inside,InBands] at leftPoint lowPoint
  have ownLong : ¬ (upper O O.c O.s≤lower A O.c O.s ∨
      upper A O.c O.s≤lower O O.c O.s) := by
    have far := strict_bounds O _ _ O.c O.s O.unit_normal oF
    have near := strict_bounds O _ _ O.c O.s O.unit_normal oN
    have central := strict_bounds A _ _ O.c O.s O.unit_normal aD
    rintro (sep | sep)
    · by_cases order : H≤0
      · have form : lower A O.c O.s=K*A.loU+H*(A.loV+A.side) := by
          rw [lower_in_bands]
          change K*(A.loU+A.side/2)+H*(A.loV+A.side/2)-
            A.side/2*(|K|+|H|)=K*A.loU+H*(A.loV+A.side)
          rw [abs_of_nonneg kp,abs_of_nonpos order]
          ring
        have up := mul_nonneg kp (sub_nonneg.mpr cap)
        have vp := mul_nonneg (neg_nonneg.mpr order)
          (sub_nonneg.mpr leftPoint.2.2.2.le)
        have width := mul_nonneg kp (sub_nonneg.mpr side.le)
        have scalar := smaller_angle oc an
          (show 0≤O.c*A.s-O.s*A.c by dsimp [H] at order; linarith only [order])
        have identity :
            K*(2*(A.c+A.s)-1)+H*(-A.s*(3/2)+A.c*2) =
            O.c*(2-A.s^2/2-A.c)+O.s*(2+A.c*A.s/2-A.s) := by
          dsimp [K,H]
          linear_combination 2*O.c*an.2.2+2*O.s*an.2.2
        clear_value K H
        nlinarith only [sep,form,up,vp,width,scalar,identity,far.2]
      · have orderPos : 0≤H := le_of_lt (lt_of_not_ge order)
        have form : lower A O.c O.s=K*A.loU+H*A.loV := by
          rw [lower_in_bands]
          change K*(A.loU+A.side/2)+H*(A.loV+A.side/2)-
            A.side/2*(|K|+|H|)=K*A.loU+H*A.loV
          rw [abs_of_nonneg kp,abs_of_nonneg orderPos]
          ring
        have up := mul_nonneg kp (sub_nonneg.mpr cap)
        have vp := mul_nonneg orderPos (sub_nonneg.mpr lowPoint.2.2.1.le)
        have width := mul_nonneg kp (sub_nonneg.mpr side.le)
        have scalar := larger_angle oc os.2 an
        have identity :
            K*(2*(A.c+A.s)-1)+H*(-A.s*2+A.c*(3/2)) =
            O.c*(2+A.c*A.s/2-A.c)+O.s*(3/2+A.s^2/2-A.s) := by
          dsimp [K,H]
          linear_combination 2*O.c*an.2.2+(3/2)*O.s*an.2.2
        clear_value K H
        nlinarith only [sep,form,up,vp,width,scalar,identity,far.2]
    · nlinarith only [sep,central.2,near.1,oc,os.1]
  have centralLong : ¬ (upper O A.c A.s≤lower A A.c A.s ∨
      upper A A.c A.s≤lower O A.c A.s) := by
    have far := strict_bounds O _ _ A.c A.s A.unit_normal oF
    have near := strict_bounds O _ _ A.c A.s A.unit_normal oN
    have central := strict_bounds A _ _ A.c A.s A.unit_normal aD
    rintro (sep | sep)
    · rw [(ownU A).1] at sep
      have margin := central_margin an
      nlinarith only [sep,far.2,cap,side,margin]
    · nlinarith only [sep,central.2,near.1,ac,an.1]
  have reverse (c s : ℝ) (hc : 0<c) (hs : s≤c) (hn : c^2+s^2=1) :
      ¬ upper A (-s) c≤lower O (-s) c := by
    have unit : (-s)^2+c^2=1 := by nlinarith only [hn]
    have central := strict_bounds A _ _ (-s) c unit aP
    have near := strict_bounds O _ _ (-s) c unit oN
    intro sep
    nlinarith only [sep,central.2,near.1,hc,hs]
  have axes := CongruentSAT.faceSeparation_of_disjoint O A same apart
  change pairRadius O A ≤ |O.c*(centerX A-centerX O)+O.s*(centerY A-centerY O)| ∨
    pairRadius O A ≤ |-O.s*(centerX A-centerX O)+O.c*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |A.c*(centerX A-centerX O)+A.s*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |-A.s*(centerX A-centerX O)+A.c*(centerY A-centerY O)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius O nx ny+supportRadius A nx ny=R)
      (sep : R≤|nx*(centerX A-centerX O)+ny*(centerY A-centerY O)|) :=
    separated O A nx ny (by rwa [identity])
  rcases axes with ou | ov | au | av
  · exact False.elim (ownLong (separateAxis _ _ _ (parallel_radius O A) ou))
  · have sep := separateAxis _ _ _ (transverse_radius O A) ov
    rcases sep with sep | sep
    · left; simpa only [(ownV O).2] using sep
    · exact False.elim (reverse O.c O.s oc os.2 O.unit_normal sep)
  · have identity : supportRadius O A.c A.s+supportRadius A A.c A.s=pairRadius A O := by
      rw [add_comm]; exact parallel_radius A O
    exact False.elim (centralLong (separateAxis _ _ _ identity au))
  · have identity : supportRadius O (-A.s) A.c+supportRadius A (-A.s) A.c=pairRadius A O := by
      rw [add_comm]; exact transverse_radius A O
    have sep := separateAxis _ _ _ identity av
    rcases sep with sep | sep
    · right; simpa only [(ownV A).1] using sep
    · exact False.elim (reverse A.c A.s ac an.2.1 A.unit_normal sep)

end N12Compact.PositiveCentralTransverse
