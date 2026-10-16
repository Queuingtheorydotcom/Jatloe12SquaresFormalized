import Compact.Geometry.CentralSteeperIncoming

/-! The actual bottom wall occupies both 2.4 and 2.6 on the row y=1.
Those two points rule out the reversed positive incoming-axis escape.
The proof retains the neighboring square's complete lower support and
uses the horizontal and parallel directions as endpoints of one cone. -/
namespace N12Compact.CentralSteeperBottomReach

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem lower_v_impossible (B : OpenSquare) {C S x : ℝ}
    (an : Normal C S) (bn : Normal B.c B.s)
    (side : 1≤B.side) (order : S*B.c≤C*B.s)
    (cap : B.loU+B.side≤3*B.c+2*B.s)
    (incoming : 2*(C+S)<lower B C S)
    (horizontal : 1-B.c-B.s+B.c*B.s+(x-3)*B.s^2≤0) :
    ¬B.c-x*B.s≤B.loV := by
  intro floor
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0<C := by linarith only [ab.1]
  have bp : 0<B.c := by linarith only [bb.1]
  let K := C*B.c+S*B.s
  let H := S*B.c-C*B.s
  let X := 1-B.c-B.s+B.c*B.s+(x-3)*B.s^2
  let Y := B.c-B.c^2-B.s+(3-x)*B.c*B.s
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg cp.le bp.le) (mul_nonneg an.1 bn.1)
  have hn : H≤0 := by dsimp [H]; linarith only [order]
  have xp : X≤0 := horizontal
  have endpoint : B.c*X+B.s*Y=B.c-1 := by
    dsimp [X,Y]
    linear_combination -bn.2.2
  have cone : C*X+S*Y≤0 := by
    by_cases sign : Y≤0
    · have first := mul_nonneg cp.le (neg_nonneg.mpr xp)
      have last := mul_nonneg an.1 (neg_nonneg.mpr sign)
      nlinarith only [first,last]
    · have positive : 0≤Y := le_of_lt (lt_of_not_ge sign)
      have first := mul_nonneg cp.le (sub_nonneg.mpr bb.2.1)
      have last := mul_nonneg (sub_nonneg.mpr order) positive
      have identity : B.c*(C*X+S*Y)=
          C*(B.c*X+B.s*Y)-(C*B.s-S*B.c)*Y := by ring
      have scaledEndpoint := congrArg (fun z : ℝ => C*z) endpoint
      have scaled : B.c*(C*X+S*Y)≤0 := by
        nlinarith only [identity,scaledEndpoint,first,last]
      exact nonpos_of_mul_nonpos_right scaled bp
  have formula : lower B C S=K*B.loU+H*(B.loV+B.side) := by
    rw [lower_in_bands]
    have u : C*B.c+S*B.s=K := rfl
    have v : -C*B.s+S*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos hn]
    ring
  have first := mul_nonneg kp (sub_nonneg.mpr cap)
  have last := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr floor)
  have width := mul_nonneg (show 0≤K-H by linarith only [kp,hn])
    (sub_nonneg.mpr side)
  have identity : K*(3*B.c+2*B.s-1)+H*(B.c-x*B.s+1)-2*(C+S)=
      C*X+S*Y := by
    dsimp [K,H,X,Y]
    linear_combination (3*C+2*S)*bn.2.2
  nlinarith only [formula,first,last,width,identity,cone,incoming]

private theorem missing_lower_faces (B : OpenSquare) {x : ℝ}
    (bn : Normal B.c B.s) (low : 12/5≤x) (high : x≤13/5)
    (wall : B.Inside 3 (87/50)) (missing : ¬B.Inside x 1) :
    x*B.c+B.s≤B.loU ∨ B.c-x*B.s≤B.loV := by
  have bounds := normal_bounds bn
  have cp : 0<B.c := by linarith only [bounds.1]
  have upperU : x*B.c+B.s<B.loU+B.side := by
    have product := mul_nonneg cp.le (show 0≤3-x by linarith only [high])
    nlinarith only [product,wall.2.1,bn.1]
  have upperV : B.c-x*B.s<B.loV+B.side := by
    have product := mul_nonneg bn.1 (show 0≤x-12/5 by linarith only [low])
    nlinarith only [product,wall.2.2.2,bn.2.1,cp]
  by_cases face : x*B.c+B.s≤B.loU
  · exact Or.inl face
  · right
    apply le_of_not_gt
    intro lower
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [face,upperU,lower,upperV]

/-- This is the complete positive neighboring-central escape. The only
foreign points are the two strict points of the same actual bottom wall.
No bottom-singleton or next-wall sign is needed. -/
theorem impossible (B : OpenSquare) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c B.s)
    (side : 1<B.side) (order : S*B.c≤C*B.s)
    (cap : B.loU+B.side≤3*B.c+2*B.s)
    (incoming : 2*(C+S)<lower B C S)
    (wall : B.Inside 3 (87/50))
    (missingLow : ¬B.Inside (12/5) 1)
    (missingHigh : ¬B.Inside (13/5) 1) : False := by
  have b := normal_bounds bn
  have firstHorizontal : 1-B.c-B.s+B.c*B.s+((12/5)-3)*B.s^2≤0 := by
    have product := mul_nonneg (sub_nonneg.mpr b.2.1)
      (show 0≤(3/5)*B.c+B.s-2/5 by linarith only [b.1,bn.1])
    have identity : 1-B.c-B.s+B.c*B.s+((12/5)-3)*B.s^2=
        (1-B.c)*(2/5-(3/5)*B.c-B.s) := by
      linear_combination -(3/5)*bn.2.2
    nlinarith only [identity,product]
  have lowerU : (12/5)*B.c+B.s≤B.loU := by
    rcases missing_lower_faces B bn (by norm_num) (by norm_num) wall missingLow with h | h
    · exact h
    · exact False.elim (lower_v_impossible B an bn side.le order cap incoming firstHorizontal h)
  have steep : 2/5<B.s := by
    linarith only [lowerU,cap,side,b.2.1]
  have lastHorizontal : 1-B.c-B.s+B.c*B.s+((13/5)-3)*B.s^2≤0 := by
    have product := mul_nonneg (sub_nonneg.mpr b.2.1)
      (show 0≤(2/5)*B.c+B.s-3/5 by linarith only [b.1,steep])
    have identity : 1-B.c-B.s+B.c*B.s+((13/5)-3)*B.s^2=
        (1-B.c)*(3/5-(2/5)*B.c-B.s) := by
      linear_combination -(2/5)*bn.2.2
    nlinarith only [identity,product]
  rcases missing_lower_faces B bn (by norm_num) (by norm_num) wall missingHigh with high | high
  · have square : (B.c+B.s)^2≤2 := by
      nlinarith only [bn.2.2,sq_nonneg (B.c-B.s)]
    have short : (2/5)*B.c+B.s<1 := by
      have ordered : (2/5)*B.c+B.s≤(7/10)*(B.c+B.s) := by
        linarith only [bn.2.1]
      nlinarith only [ordered,square]
    linarith only [high,cap,side,short]
  · exact lower_v_impossible B an bn side.le order cap incoming lastHorizontal high

private theorem negative_lower_v_impossible (B : OpenSquare) {C S x : ℝ}
    (an : Normal C (-S)) (bn : Normal B.c B.s) (xBound : x≤13/5)
    (side : 1≤B.side) (cap : B.loU+B.side≤3*B.c+2*B.s)
    (incoming : 2*C+(3/2)*S<lower B C S)
    (horizontal : 1-B.c-B.s+B.c*B.s+(x-3)*B.s^2≤0) :
    ¬B.c-x*B.s≤B.loV := by
  intro floor
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤C := by linarith only [ab.1]
  have bp : 0≤B.c := by linarith only [bb.1]
  have sign : S≤0 := by linarith only [an.1]
  let K := C*B.c+S*B.s
  let H := S*B.c-C*B.s
  let X := 1-B.c-B.s+B.c*B.s+(x-3)*B.s^2
  let Y := B.c-B.c^2-B.s+(3-x)*B.c*B.s
  have kp : 0≤K := by
    have first := mul_nonneg bp (show 0≤C+S by linarith only [an.2.1])
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hn : H≤0 := by
    have first := mul_nonneg (neg_nonneg.mpr sign) bp
    have last := mul_nonneg cp bn.1
    dsimp [H]; nlinarith only [first,last]
  have xp : X≤0 := horizontal
  have cross : B.c*B.s≤1/2 := by
    nlinarith only [bn.2.2,sq_nonneg (B.c-B.s)]
  have defect : (1-B.c)^2≤9/100 := by
    have product := mul_nonneg
      (show 0≤3/10-(1-B.c) by linarith only [bb.1])
      (show 0≤3/10+(1-B.c) by linarith only [bb.2.1])
    nlinarith only [product]
  have first := mul_nonneg (mul_nonneg bp bn.1) (sub_nonneg.mpr xBound)
  have last := mul_nonneg (sq_nonneg B.s) (sub_nonneg.mpr xBound)
  have diagonal : X-Y-1/2≤0 := by
    dsimp [X,Y]
    nlinarith only [defect,cross,first,last,sq_nonneg B.s]
  have firstWeight := mul_nonneg (show 0≤C+S by linarith only [an.2.1])
    (neg_nonneg.mpr xp)
  have lastWeight := mul_nonneg an.1 (neg_nonneg.mpr diagonal)
  have cone : C*X+S*(Y+1/2)≤0 := by
    nlinarith only [firstWeight,lastWeight]
  have formula : lower B C S=K*B.loU+H*(B.loV+B.side) := by
    rw [lower_in_bands]
    have u : C*B.c+S*B.s=K := rfl
    have v : -C*B.s+S*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos hn]
    ring
  have capWeight := mul_nonneg kp (sub_nonneg.mpr cap)
  have floorWeight := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr floor)
  have width := mul_nonneg (show 0≤K-H by linarith only [kp,hn])
    (sub_nonneg.mpr side)
  have identity : K*(3*B.c+2*B.s-1)+H*(B.c-x*B.s+1)-
      (2*C+(3/2)*S)=C*X+S*(Y+1/2) := by
    dsimp [K,H,X,Y]
    linear_combination (3*C+2*S)*bn.2.2
  nlinarith only [formula,capWeight,floorWeight,width,identity,cone,incoming]

/-- The same two original wall points close the negative central test
direction. The strict incoming value is the actual crosspoint (2,1.5),
so no reflection of the missing-singleton root is required. -/
theorem negative_impossible (B : OpenSquare) {C S : ℝ}
    (an : Normal C (-S)) (bn : Normal B.c B.s)
    (side : 1<B.side) (cap : B.loU+B.side≤3*B.c+2*B.s)
    (incoming : 2*C+(3/2)*S<lower B C S)
    (wall : B.Inside 3 (87/50))
    (missingLow : ¬B.Inside (12/5) 1)
    (missingHigh : ¬B.Inside (13/5) 1) : False := by
  have b := normal_bounds bn
  have firstHorizontal : 1-B.c-B.s+B.c*B.s+((12/5)-3)*B.s^2≤0 := by
    have product := mul_nonneg (sub_nonneg.mpr b.2.1)
      (show 0≤(3/5)*B.c+B.s-2/5 by linarith only [b.1,bn.1])
    have identity : 1-B.c-B.s+B.c*B.s+((12/5)-3)*B.s^2=
        (1-B.c)*(2/5-(3/5)*B.c-B.s) := by
      linear_combination -(3/5)*bn.2.2
    nlinarith only [identity,product]
  have lowerU : (12/5)*B.c+B.s≤B.loU := by
    rcases missing_lower_faces B bn (by norm_num) (by norm_num) wall missingLow with h | h
    · exact h
    · exact False.elim (negative_lower_v_impossible B an bn (by norm_num)
        side.le cap incoming firstHorizontal h)
  have steep : 2/5<B.s := by linarith only [lowerU,cap,side,b.2.1]
  have lastHorizontal : 1-B.c-B.s+B.c*B.s+((13/5)-3)*B.s^2≤0 := by
    have product := mul_nonneg (sub_nonneg.mpr b.2.1)
      (show 0≤(2/5)*B.c+B.s-3/5 by linarith only [b.1,steep])
    have identity : 1-B.c-B.s+B.c*B.s+((13/5)-3)*B.s^2=
        (1-B.c)*(3/5-(2/5)*B.c-B.s) := by
      linear_combination -(2/5)*bn.2.2
    nlinarith only [identity,product]
  rcases missing_lower_faces B bn (by norm_num) (by norm_num) wall missingHigh with high | high
  · have square : (B.c+B.s)^2≤2 := by
      nlinarith only [bn.2.2,sq_nonneg (B.c-B.s)]
    have short : (2/5)*B.c+B.s<1 := by
      have ordered : (2/5)*B.c+B.s≤(7/10)*(B.c+B.s) := by linarith only [bn.2.1]
      nlinarith only [ordered,square]
    linarith only [high,cap,side,short]
  · exact negative_lower_v_impossible B an bn (by norm_num)
      side.le cap incoming lastHorizontal high

end N12Compact.CentralSteeperBottomReach
