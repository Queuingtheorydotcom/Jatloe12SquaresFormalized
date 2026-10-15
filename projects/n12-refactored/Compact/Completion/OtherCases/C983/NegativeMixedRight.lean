import Compact.Completion.OtherCases.C983.NegativeRightOwned

/-! The mixed branch with the southeast/right separator on the right
transverse axis and the northeast/right separator on the northeast parallel
axis. The two right bands are eliminated against the actual wall. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeMixedRight
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

private def residual (a b d r v : ℝ) : ℝ :=
  a*(1-r)+r*v+(a+b-2)*(a*d+b*r)+a*max (a*r-b*d) 0

private theorem scalar_bounds (a b d r : ℝ) (ap : 0<a) (bn : 0≤b)
    (dp : 0<d) (rp : 0<r) (ru : a^2+b^2=1) (nu : d^2+r^2=1) :
    0<a*d+b*r ∧ a*d+b*r≤1 ∧ a≤1 ∧ b≤1 ∧ d≤1 ∧
      1≤a+b ∧ a+b<2 := by
  have Apos : 0<a*d+b*r := by positivity
  have rotated : (a*d+b*r)^2+(a*r-b*d)^2=1 := by
    linear_combination (a^2+b^2)*nu+ru
  have Au : a*d+b*r≤1 := by nlinarith only [rotated,sq_nonneg (a*r-b*d),Apos]
  have au : a≤1 := by nlinarith only [ru,sq_nonneg b,ap]
  have bu : b≤1 := by nlinarith only [ru,sq_nonneg a,bn]
  have du : d≤1 := by nlinarith only [nu,sq_nonneg r,dp]
  have prod := mul_nonneg ap.le bn
  have sumlo : 1≤a+b := by nlinarith only [ru,prod,ap,bn]
  have sumhi : a+b<2 := by nlinarith only [ru,sq_nonneg (a-b)]
  exact ⟨Apos,Au,au,bu,du,sumlo,sumhi⟩

/-- The universal southeast support closes every right direction up to
`b=4/5`; the fixed vertex support closes the remaining directions. -/
private theorem scalar_universal (a b d r v : ℝ) (ap : 0<a) (bn : 0≤b)
    (dp : 0<d) (rp : 0<r) (ru : a^2+b^2=1) (nu : d^2+r^2=1)
    (rSmall : r<3/4) (projection : d+r/7<1)
    (floor : 1-(1-b)/a≤v) (vertex : b-a/7≤v) :
    0≤residual a b d r v := by
  let A := a*d+b*r
  let B := a*r-b*d
  let C := 2-a-b
  let q := (1-b)/a
  have data := scalar_bounds a b d r ap bn dp rp ru nu
  have Apos : 0<A := data.1
  have Au : A≤1 := data.2.1
  have au : a≤1 := data.2.2.1
  have bu : b≤1 := data.2.2.2.1
  have Cp : 0<C := by dsimp only [C]; linarith only [data.2.2.2.2.2.2]
  have Cu : C≤1 := by dsimp only [C]; linarith only [data.2.2.2.2.2.1]
  have aq : a*q=1-b := by dsimp only [q]; field_simp [ne_of_gt ap]
  by_cases steep : 4/5≤b
  · have aSmall : a≤3/5 := by
      have square := mul_nonneg (sub_nonneg.mpr steep)
        (show 0≤b+4/5 by linarith only [bn])
      apply le_of_not_gt
      intro bad
      have other := mul_pos (sub_pos.mpr bad)
        (show 0<a+3/5 by linarith only [ap])
      nlinarith only [ru,square,other]
    have beta := mul_nonneg Cp.le (sub_nonneg.mpr projection.le)
    have delta := mul_nonneg (sub_nonneg.mpr Cu)
      (show 0≤1-(4/3)*r by linarith only [rSmall])
    have first := mul_nonneg ap.le (show 0≤C*(1-d-r/7)+(1-C)*(1-(4/3)*r) by
      linarith only [beta,delta])
    have last := mul_nonneg
      (mul_nonneg rp.le (sub_nonneg.mpr bu))
      (show 0≤25+4*b-46*a by linarith only [steep,aSmall])
    have support := mul_nonneg rp.le (sub_nonneg.mpr vertex)
    have axis := mul_nonneg ap.le (le_max_right B 0)
    have identity : a*(1-r)+r*(b-a/7)+(a+b-2)*A=
        a*(C*(1-d-r/7)+(1-C)*(1-(4/3)*r))+
        (r/21)*(1-b)*(25+4*b-46*a) := by
      dsimp only [A,C]
      linear_combination (25/21)*r*ru
    dsimp only [residual]
    dsimp only [A,B] at identity axis
    nlinarith only [identity,first,last,support,axis]
  · have bSmall : b≤4/5 := le_of_not_ge steep
    have aligned : 0≤2*a-2+b*(2-a-q) := by
      have margin := mul_nonneg (sub_nonneg.mpr bu) (sq_nonneg (1-a))
      have identity : a*(2*a-2+b*(2-a-q))=(1-b)*(1-a)^2 := by
        linear_combination ru-b*aq
      nlinarith only [margin,identity,ap]
    have support := mul_nonneg rp.le (sub_nonneg.mpr floor)
    by_cases Bpos : 0≤B
    · have bBefore : b≤r := by
        have identity : r*A-d*B=b := by
          dsimp only [A,B]
          linear_combination b*nu
        have first := mul_nonneg rp.le (sub_nonneg.mpr Au)
        have last := mul_nonneg dp.le Bpos
        nlinarith only [identity,first,last]
      have gNonneg : 0≤2-a-q := by
        have first := mul_nonneg bn (sub_nonneg.mpr bu)
        have last := mul_nonneg ap.le (sub_nonneg.mpr au)
        have identity : a*(2-a-q)=b-(1-a)^2 := by
          linear_combination -aq
        nlinarith only [identity,first,last,ru,ap]
      have first := mul_nonneg (show 0≤2-a by linarith only [au])
        (sub_nonneg.mpr Au)
      have last := mul_nonneg (sub_nonneg.mpr bBefore) gNonneg
      have identity : residual a b d r v=
          a+(a-2)*A+r*(1+v-a) := by
        dsimp only [residual]
        rw [max_eq_left Bpos]
        dsimp only [A,B]
        linear_combination r*ru
      dsimp only [q] at aligned last
      nlinarith only [identity,aligned,first,last,support]
    · have Bnonpos : B≤0 := le_of_not_ge Bpos
      have rBefore : r≤b := by
        have identity : b*A+a*B=r := by
          dsimp only [A,B]
          linear_combination r*ru
        have first := mul_nonneg bn (sub_nonneg.mpr Au)
        have last := mul_nonneg ap.le (neg_nonneg.mpr Bnonpos)
        nlinarith only [identity,first,last]
      have Aweight := mul_nonneg Cp.le (sub_nonneg.mpr Au)
      have identity : residual a b d r v=a+r*(v-a)-C*A := by
        dsimp only [residual]
        rw [max_eq_right Bnonpos]
        dsimp only [A,C]
        ring
      by_cases sign : 1-q≤a
      · have angle := mul_nonneg (sub_nonneg.mpr rBefore)
          (show 0≤a-(1-q) by linarith only [sign])
        dsimp only [q] at aligned angle
        dsimp only [C] at Aweight identity
        nlinarith only [identity,aligned,Aweight,angle,support]
      · have aWall : 2≤2*a+b := by
          have product := mul_nonneg bn (show 0≤4-5*b by linarith only [bSmall])
          apply le_of_not_gt
          intro bad
          have square := mul_pos (sub_pos.mpr bad)
            (show 0<2-b+2*a by linarith only [ap,bu])
          nlinarith only [product,square,ru]
        have angle := mul_nonneg rp.le (show 0≤1-q-a by linarith only [sign])
        dsimp only [q] at angle
        dsimp only [C] at Aweight identity
        nlinarith only [identity,Aweight,angle,support,aWall]

private theorem scalar_shallow (a b d r v : ℝ) (ap : 0<a) (bn : 0≤b)
    (dp : 0<d) (rp : 0<r) (ru : a^2+b^2=1) (nu : d^2+r^2=1)
    (rLarge : 29/100<r) (shallow : b≤9/41)
    (floor : 1+(4/5)*b-a≤v) : 0≤residual a b d r v := by
  let A := a*d+b*r
  let B := a*r-b*d
  have data := scalar_bounds a b d r ap bn dp rp ru nu
  have Au : A≤1 := data.2.1
  have au : a≤1 := data.2.2.1
  have du : d≤1 := data.2.2.2.2.1
  have aLarge : 40/41≤a := by
    have square := mul_nonneg (sub_nonneg.mpr shallow)
      (show 0≤9/41+b by linarith only [bn])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<40/41+a by linarith only [ap])
    nlinarith only [ru,square,other]
  have Bpos : 0≤B := by
    have first := mul_nonneg ap.le (sub_nonneg.mpr rLarge.le)
    have last := mul_nonneg bn (sub_nonneg.mpr du)
    dsimp only [B]
    nlinarith only [first,last,aLarge,shallow]
  have gNonneg : 0≤2+(4/5)*b-2*a := by linarith only [au,bn]
  have first := mul_nonneg (show 0≤2-a by linarith only [au])
    (sub_nonneg.mpr Au)
  have last := mul_nonneg (sub_nonneg.mpr rLarge.le) gNonneg
  have support := mul_nonneg rp.le (sub_nonneg.mpr floor)
  have deficit : 1-a≤(14/25)*b^2 := by
    have product := mul_nonneg (sub_nonneg.mpr au)
      (show 0≤(14/25)*(1+a)-1 by linarith only [aLarge])
    nlinarith only [product,ru]
  have quadratic := mul_nonneg bn
    (show 0≤29/125-(497/625)*b by linarith only [shallow])
  have lower : 0≤2*a-2+(29/100)*(2+(4/5)*b-2*a) := by
    nlinarith only [deficit,quadratic]
  have identity : residual a b d r v=a+(a-2)*A+r*(1+v-a) := by
    dsimp only [residual]
    rw [max_eq_left Bpos]
    dsimp only [A,B]
    linear_combination r*ru
  nlinarith only [identity,lower,first,last,support]

private theorem wall_residual (E N R : OpenSquare)
    (input : RightTripleData.Input E N R)
    (north : upper N N.c N.s≤lower R N.c N.s) :
    residual R.c (-R.s) N.c (-N.s) R.loV<0 := by
  let a := R.c
  let b := -R.s
  let d := N.c
  let r := -N.s
  let A := a*d+b*r
  let B := a*r-b*d
  let J := max B 0
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have dp : 0<d := input.northeastFaces.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [input.northeastFaces.sine_neg]
  have ru : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have Apos : 0<A := by dsimp only [A]; positivity
  have Jnonneg : 0≤J := le_max_right B 0
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have sideR : 1<R.side := by simpa only [←input.sameER] using input.southeastFaces.sideLarge
  have nLow : 1-r<N.loU+N.side := by
    dsimp only [r]
    linarith only [input.northeastFaces.lowerU,sideN]
  have formula : lower R d (-r)=A*R.loU-B*R.loV-J*R.side := by
    rw [C981CompletionSupportForms.lower_in_bands]
    have first : d*R.c+(-r)*R.s=A := by dsimp only [A,a,b]; ring
    have last : -d*R.s+(-r)*R.c= -B := by dsimp only [B,a,b]; ring
    rw [first,last,abs_of_nonneg Apos.le]
    dsimp only [J]
    by_cases sign : 0≤B
    · rw [abs_of_nonpos (neg_nonpos.mpr sign),max_eq_left sign]
      ring
    · have opposite : B≤0 := le_of_not_ge sign
      rw [abs_of_nonneg (neg_nonneg.mpr opposite),max_eq_right opposite]
      ring
  rw [(ownU N).2] at north
  have nFace : N.loU+N.side≤A*R.loU-B*R.loV-J*R.side := by
    have normalized : N.loU+N.side≤lower R d (-r) := by
      simpa only [d,r,neg_neg] using north
    rwa [formula] at normalized
  have wall : a*(R.loU+R.side)+b*(R.loV+R.side)≤2 := by
    dsimp only [a,b]
    nlinarith only [input.rightFaces.realWall]
  have first := mul_pos ap (sub_pos.mpr nLow)
  have next := mul_nonneg ap.le (sub_nonneg.mpr nFace)
  have last := mul_nonneg Apos.le (sub_nonneg.mpr wall)
  have coeff : 0≤(a+b)*A+a*J := by positivity
  have length := mul_nonneg coeff (sub_nonneg.mpr sideR.le)
  have identity : A*(a*(R.loU+R.side)+b*(R.loV+R.side))-
      a*(A*R.loU-B*R.loV-J*R.side)=
      r*R.loV+((a+b)*A+a*J)*R.side := by
    dsimp only [A,B]
    linear_combination r*R.loV*ru
  change a*(1-r)+r*R.loV+(a+b-2)*A+a*J<0
  nlinarith only [first,next,last,length,identity]

private theorem vertex_floor (E R : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (right : RightTripleData.RightProfile R)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) :
    -R.s-R.c/7<R.loV := by
  let X := E.c*(E.loU+E.side)+t*(E.loV+E.side)
  let Y := -t*(E.loU+E.side)+E.c*(E.loV+E.side)
  have coordinates := NegativeRightSeparation.southeast_vertex_coordinates E t profile
  have yFloor := NegativeCentralOrder.upper_vertex_y_gt E t profile
  have support := (closed_bounds E X Y (-R.s) R.c coordinates.1).2
  have first := mul_nonneg
    (show 0≤ -R.s by linarith only [right.sineNonpositive])
    (sub_nonneg.mpr coordinates.2.1.le)
  have last := mul_pos right.cosinePositive (sub_pos.mpr yFloor)
  rw [(ownV R).1] at south
  dsimp only [X,Y] at support ⊢
  nlinarith only [support,first,last,south]

/-- The right transverse / northeast parallel mixed branch is impossible. -/
theorem impossible (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (north : upper N N.c N.s≤lower R N.c N.s)
    (south : upper E (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  let a := R.c
  let b := -R.s
  let d := N.c
  let r := -N.s
  have ap : 0<a := input.rightFaces.cosinePositive
  have bn : 0≤b := by dsimp only [b]; linarith only [input.rightFaces.sineNonpositive]
  have dp : 0<d := input.northeastFaces.cosine_pos
  have rp : 0<r := by dsimp only [r]; linarith only [input.northeastFaces.sine_neg]
  have ru : a^2+b^2=1 := by simpa only [a,b,neg_sq] using R.unit_normal
  have nu : d^2+r^2=1 := by simpa only [d,r,neg_sq] using N.unit_normal
  have sideN : 1<N.side := by simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have data := TopOnlyQuadrantScalars.profile_bounds N sideN input.northeastFaces
  have rLarge : 29/100<r := NegativeCentralOrder.north_sine_gt N sideN input.northeastFaces
  have projection : d+r/7<1 := NegativeCentralOrder.north_projection_lt N sideN input.northeastFaces
  have vertex := vertex_floor E R (-E.s) input.southeastFaces input.rightFaces south
  have wall := wall_residual E N R input north
  have vBound : upper E b a≤R.loV := by simpa only [(ownV R).1] using south
  rcases input.southeastFaces.bar with first | second
  · by_cases shallow : b≤9/41
    · have floor := NegativeRightOwned.southeast_first_shallow E (-E.s) a b
        input.southeastFaces first ap bn shallow ru
      have result := scalar_shallow a b d r R.loV ap bn dp rp ru nu rLarge shallow
        (le_trans floor.le vBound)
      exact (not_lt_of_ge result) wall
    · have floor := NegativeRightOwned.southeast_first_steep E (-E.s) a b
        input.southeastFaces first ap bn (le_of_not_ge shallow) ru
      have result := scalar_universal a b d r R.loV ap bn dp rp ru nu
        data.2.2.2.1 projection (le_trans floor.le vBound) vertex.le
      exact (not_lt_of_ge result) wall
  · have floor := NegativeRightOwned.southeast_second_floor E (-E.s) a b
      input.southeastFaces second ap bn ru
    have result := scalar_universal a b d r R.loV ap bn dp rp ru nu
      data.2.2.2.1 projection (le_trans floor.le vBound) vertex.le
    exact (not_lt_of_ge result) wall

#print axioms impossible
end N12Compact.Completion.OtherCases.C983.NegativeMixedRight
