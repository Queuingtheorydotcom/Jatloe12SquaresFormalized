import Compact.Completion.OtherCases.C976LeftTop.TopFaces
import Compact.Completion.OtherCases.C976LeftTop.Segment
import Compact.Completion.OtherCases.C976LeftTop.Margins

/-! Sections 5--6 of C976-LEFT-TOP-ANGLE. The one support obtained from
the entire actual excluded segment is joined to both possible physical
separating axes. The real top wall and the common side retain all weak
face contacts. Source translation only; these proofs are uncompiled. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open OrdinaryLeftTop
set_option Elab.async false

theorem left_axis_impossible (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side) (large : (1/3)*N.c≤N.s)
    (face : W.c-(63/50)*W.s≤W.loV)
    (separation : upper N N.c N.s≤lower W N.c N.s) : False := by
  have support := lower_support_strict N W n t w same face
  have segment := upperU_strict N n large
  have ap : 0<Scalars.a0 N.c N.s := by
    dsimp only [Scalars.a0]
    linarith only [n.cosine,n.sine]
  have sepWeight := mul_le_mul_of_nonneg_left separation w.sine.le
  by_cases small : N.s≤N.c/2
  · have margin := Scalars.left_low_margin N.c N.s n.cosine n.sine N.unit_normal
      large small
    have identity : Scalars.a0 N.c N.s+Scalars.b0 N.c N.s*(1-N.c)-39/625-
        Scalars.a0 N.c N.s*((13/50)*N.c+N.s)=
        (37/100)*N.c+(11/100)*N.s-189/625-(169/5000)*N.c^2-
          (39/625)*N.c*N.s := by
      dsimp only [Scalars.a0,Scalars.b0]
      linear_combination -(6/25)*N.unit_normal
    have weighted : Scalars.a0 N.c N.s*((13/50)*N.c+N.s)<
        Scalars.a0 N.c N.s*(N.loU+N.side) := by
      linarith only [segment,identity,margin]
    have upper : (13/50)*N.c+N.s<upper N N.c N.s := by
      rw [(ownU N).2]
      exact (mul_lt_mul_left ap).mp weighted
    have targetBound := target_low N W n w (by linarith only [small])
    have upperWeight := mul_lt_mul_of_pos_left upper w.sine
    linarith only [support,targetBound,upperWeight,sepWeight]
  · have high : N.c/2≤N.s := le_of_lt (lt_of_not_ge small)
    have margin := Scalars.left_high_margin N.c N.s n.cosine n.sine N.unit_normal
      high (angle_upper N n).le
    have identity : Scalars.a0 N.c N.s+Scalars.b0 N.c N.s*(1-N.c)-39/625-
        Scalars.a0 N.c N.s*((4/25)*N.c+(6/5)*N.s)=
        (37/100)*N.c+(11/100)*N.s-219/625+(17/625)*N.c^2-
          (161/2500)*N.c*N.s := by
      dsimp only [Scalars.a0,Scalars.b0]
      linear_combination -(36/125)*N.unit_normal
    have weighted : Scalars.a0 N.c N.s*((4/25)*N.c+(6/5)*N.s)<
        Scalars.a0 N.c N.s*(N.loU+N.side) := by
      linarith only [segment,identity,margin]
    have upper : (4/25)*N.c+(6/5)*N.s<upper N N.c N.s := by
      rw [(ownU N).2]
      exact (mul_lt_mul_left ap).mp weighted
    have targetBound := target_high N W n w (by linarith only [high])
    have upperWeight := mul_lt_mul_of_pos_left upper w.sine
    linarith only [support,targetBound,upperWeight,sepWeight]

theorem top_axis_impossible (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side) (large : (1/3)*N.c≤N.s)
    (face : W.c-(63/50)*W.s≤W.loV)
    (separation : upper N W.c W.s≤lower W W.c W.s) : False := by
  let a0 := Scalars.a0 N.c N.s
  let b0 := Scalars.b0 N.c N.s
  let K := Scalars.k0 W.c W.s
  have ap : 0<a0 := by dsimp only [a0,Scalars.a0]; linarith only [n.cosine,n.sine]
  have coeff := coefficients N W n w
  have relation : beta N W*a0-alpha N W*b0=K := by
    dsimp only [a0,b0,K,Scalars.a0,Scalars.b0,Scalars.k0,
      alpha,beta,ShallowTop.alpha,ShallowTop.gamma]
    linear_combination ((13/100)*W.s-(6/25)*W.c)*N.unit_normal
  have rawSegment := segment_support N n large
  have segment : -(39/625)≤a0*N.loU+b0*N.loV := rawSegment
  have segmentWeight := mul_le_mul_of_nonneg_left segment coeff.1.le
  have relationWeight := congrArg (fun x : ℝ => x*N.loV) relation
  have formula := upper_wall_normal N W n w
  have lowerSupport : N.side*(alpha N W+beta N W)*a0+K*N.loV-
      (39/625)*alpha N W≤a0*upper N W.c W.s := by
    rw [formula]
    nlinarith only [segmentWeight,relationWeight]
  have wall := ShallowTop.top_wall_faces W t w
  rw [(ownU W).1] at separation
  have wallWeight := mul_nonneg ap.le (sub_nonneg.mpr wall)
  have faceWeight := mul_nonneg (mul_nonneg ap.le w.cosine) (sub_nonneg.mpr face)
  have sepWeight := mul_nonneg (mul_nonneg ap.le w.sine.le) (sub_nonneg.mpr separation)
  have physical : W.s*a0*upper N W.c W.s+
      a0*(N.side*(W.c+W.s)+W.c^2-(63/50)*W.c*W.s-2)≤0 := by
    rw [←same] at wallWeight
    nlinarith only [wallWeight,faceWeight,sepWeight]
  have lowerWeight := mul_nonneg w.sine.le (sub_nonneg.mpr lowerSupport)
  have necessary :
      W.s*(N.side*(alpha N W+beta N W)*a0+K*N.loV-(39/625)*alpha N W)+
        a0*(N.side*(W.c+W.s)+W.c^2-(63/50)*W.c*W.s-2)≤0 := by
    nlinarith only [physical,lowerWeight]
  let D := a0*(W.s*(alpha N W+beta N W)+W.c+W.s)
  have dp : 0<D := by
    dsimp only [D]
    exact mul_pos ap (by
      have first := mul_pos w.sine (add_pos coeff.1 coeff.2)
      linarith only [first,w.cosine,w.sine])
  by_cases sign : 0≤K
  · have lowerV := mul_nonneg (mul_nonneg w.sine.le sign) (sub_nonneg.mpr n.lowerV)
    have endpoint : 0<Scalars.Elo N.c N.s W.c W.s :=
      Scalars.lo_positive N.c N.s W.c W.s n.cosine n.sine.le N.unit_normal
        large (angle_upper N n) (width N n) w.cosine w.sine W.unit_normal w.slope sign
    have extra := mul_pos (sub_pos.mpr n.side) dp
    have identity :
        W.s*(N.side*(alpha N W+beta N W)*a0+K*N.loV-(39/625)*alpha N W)+
          a0*(N.side*(W.c+W.s)+W.c^2-(63/50)*W.c*W.s-2)=
        Scalars.Elo N.c N.s W.c W.s+(N.side-1)*D+
          W.s*K*(N.loV-(-(27/100)*N.s-(1/25)*N.c)) := by
      dsimp only [a0,K,D,Scalars.Elo,Scalars.alpha,Scalars.beta,
        alpha,beta,ShallowTop.alpha,ShallowTop.gamma]
      ring
    linarith only [necessary,identity,endpoint,extra,lowerV]
  · have kn : K≤0 := le_of_lt (lt_of_not_ge sign)
    have upperV := mul_nonneg (mul_nonneg w.sine.le (neg_nonneg.mpr kn))
      (sub_nonneg.mpr n.upperV)
    have endpoint : 0<Scalars.Ehi N.c N.s W.c W.s :=
      Scalars.hi_positive N.c N.s W.c W.s n.cosine n.sine.le N.unit_normal
        large (angle_upper N n) (width N n) w.cosine w.sine W.unit_normal w.slope kn
    have dPositive : 0<D-W.s*K := by
      have last := mul_nonpos_of_nonneg_of_nonpos w.sine.le kn
      linarith only [dp,last]
    have extra := mul_pos (sub_pos.mpr n.side) dPositive
    have identity :
        W.s*(N.side*(alpha N W+beta N W)*a0+K*N.loV-(39/625)*alpha N W)+
          a0*(N.side*(W.c+W.s)+W.c^2-(63/50)*W.c*W.s-2)=
        Scalars.Ehi N.c N.s W.c W.s+(N.side-1)*(D-W.s*K)+
          W.s*(-K)*(N.c-(N.loV+N.side)) := by
      dsimp only [a0,K,D,Scalars.Ehi,Scalars.alpha,Scalars.beta,
        alpha,beta,ShallowTop.alpha,ShallowTop.gamma]
      ring
    linarith only [necessary,identity,endpoint,extra,upperV]

end N12Compact.Completion.OtherCases.C976LeftTop
