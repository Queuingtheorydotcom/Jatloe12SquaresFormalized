import Compact.Completion.C1092.MPPMInwardFinalBottomData

/-! Both complete relative-angle orders for the actual nonpositive
bottom square in INWARD-BOTTOM-ANGLE. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal.BottomAngle
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

theorem negative_coefficients (C B : OpenSquare) (cn : Normal C.c (-C.s))
    (bn : Normal B.c (-B.s)) : 0<C.c*B.c+C.s*B.s ∧ C.c*B.c+C.s*B.s≤1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have first := mul_pos (show 0<C.c by linarith only [cb.1])
    (show 0<B.c by linarith only [bb.1])
  have last := mul_nonneg cn.1 bn.1
  have unit := relative_unit cn bn
  constructor
  · nlinarith only [first,last]
  · nlinarith only [unit,sq_nonneg (-C.c*B.s+C.s*B.c),
      sq_nonneg (C.c*B.c+C.s*B.s-1)]

theorem negative_v (C B : OpenSquare) (h : Input C B) (bn : Normal B.c (-B.s))
    (qlow : half C.c (-C.s)≤1-C.c-(2/5)*C.s)
    (sep : B.loV+B.side≤lower C (-B.s) B.c) : False := by
  have faces := central_faces C B h
  have height := negative_wall_height C B h bn
  have coefficients := negative_coefficients C B h.normal bn
  let l := C.c*B.c+C.s*B.s
  let d := -C.c*B.s+C.s*B.c
  by_cases order : d≤0
  · have formula := lower_np C (-B.s) B.c d l
      (by dsimp [d]; ring) (by dsimp [l]; ring) order coefficients.1.le
    have first := mul_nonneg (neg_nonneg.mpr order) (sub_nonneg.mpr faces.lowerU)
    have last := mul_nonneg coefficients.1.le
      (show 0≤-C.side-C.loV by linarith only [faces.upperV])
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<l-d by dsimp [l]; linarith only [coefficients.1,order])
    have margin := negative_before_margin h.normal bn
      (show C.c*(-B.s)≤(-C.s)*B.c by dsimp [d] at order; nlinarith only [order]) qlow
    dsimp [l,d] at formula first strict
    nlinarith only [formula,first,last,strict,margin,sep,height]
  · have positive : 0≤d := (lt_of_not_ge order).le
    have formula := lower_nn C (-B.s) B.c d l
      (by dsimp [d]; ring) (by dsimp [l]; ring) positive coefficients.1.le
    have first := mul_nonneg positive
      (show 0≤-C.c/2-C.loU by linarith only [faces.upperLowU])
    have last := mul_nonneg coefficients.1.le
      (show 0≤-C.side-C.loV by linarith only [faces.upperV])
    have strict := mul_pos (sub_pos.mpr h.side) coefficients.1
    have margin := negative_after_margin h.normal bn
      (show (-C.s)*B.c≤C.c*(-B.s) by dsimp [d] at positive; nlinarith only [positive])
    dsimp [l,d] at formula first
    nlinarith only [formula,first,last,strict,margin,sep,height]

theorem negative_central (C B : OpenSquare) (h : Input C B) (bn : Normal B.c (-B.s))
    (sep : upper B (-C.s) C.c≤C.loV) : False := by
  have faces := central_faces C B h
  have height := negative_wall_height C B h bn
  have coefficients := negative_coefficients C B h.normal bn
  let l := C.c*B.c+C.s*B.s
  let e := -C.s*B.c+C.c*B.s
  have support : -1<upper B (-C.s) C.c := by
    by_cases order : 0≤e
    · have formula := upper_pos_pos B (-C.s) C.c e l
        (by dsimp [e]; ring) (by dsimp [l]; ring) order coefficients.1.le
      have upperU : 0<B.loU+B.side := by
        linarith only [h.bottomMarker.2.1,bn.1]
      have first := mul_nonneg order upperU.le
      have last := mul_pos coefficients.1 (show 0<B.loV+B.side+1 by linarith only [height])
      dsimp [e,l] at formula first
      nlinarith only [formula,first,last,coefficients.2]
    · have en : e≤0 := (lt_of_not_ge order).le
      have formula := upper_np B (-C.s) C.c e l
        (by dsimp [e]; ring) (by dsimp [l]; ring) en coefficients.1.le
      by_cases shallow : -B.s≤(14/25)*B.c
      · have lowerU : B.loU<0 := by linarith only [h.bottomFar.1,shallow]
        have first := mul_nonneg (neg_nonneg.mpr en) (show 0≤-B.loU by linarith only [lowerU])
        have last := mul_pos coefficients.1 (show 0<B.loV+B.side+1 by linarith only [height])
        dsimp [e,l] at formula first
        nlinarith only [formula,first,last,coefficients.2]
      · let P := 1+(43/500)*B.c^2+(14/25)*B.c*B.s
        let Q := (14/25)*B.c^2-(43/500)*B.c*B.s
        have first := mul_nonneg (neg_nonneg.mpr en)
          (show 0≤-(14/25)*B.c-B.s-B.loU by linarith only [h.bottomFar.1])
        have last := mul_pos coefficients.1
          (show 0<B.loV+B.side+(543/500)*B.c by linarith only [h.bottomMarker.2.2.2])
        have identity : e*(-(14/25)*B.c-B.s)+l*(-(543/500)*B.c)= -C.c*P+C.s*Q := by
          dsimp [e,l,P,Q]
          linear_combination -C.c*B.unit_normal
        have norm := negative_central_norm bn (by linarith only [shallow])
        have dot := dot_le_one h.normal norm.le
        change P*C.c+Q*(-C.s)≤1 at dot
        dsimp [e,l] at formula identity first
        nlinarith only [formula,identity,first,last,dot]
  linarith only [support,sep,faces.upperV,h.side]

theorem nonpositive_impossible (C B : OpenSquare) (h : Input C B) (bn : Normal B.c (-B.s))
    (bad : (half C.c (-C.s))^2-2*half C.c (-C.s)+1/5≤0) : False := by
  have arc := bad_arc h.normal bad
  have canonical : |B.s|≤B.c := by
    rw [abs_of_nonpos (show B.s≤0 by linarith only [bn.1])]
    exact bn.2.1
  rcases separators C B h canonical with own|first|last
  · exact negative_central C B h bn own
  · have direction := cone C B h B.c B.s B.unit_normal
      (by simpa only [(ownU B).2] using first)
    linarith only [direction.1,bn.1]
  · exact negative_v C B h bn arc.1 last

#print axioms nonpositive_impossible
end N12Compact.C1092MPPMInwardFinal.BottomAngle
