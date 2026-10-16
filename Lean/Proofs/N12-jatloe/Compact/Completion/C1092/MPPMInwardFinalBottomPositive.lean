import Compact.Completion.C1092.MPPMInwardFinalBottomData

/-! The three genuine support sources for a nonnegative actual bottom
square in INWARD-BOTTOM-ANGLE. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal.BottomAngle
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

theorem positive_coefficients (C B : OpenSquare) (cn : Normal C.c (-C.s))
    (negative : C.s<0) (bn : Normal B.c B.s) :
    0≤C.c*B.c+C.s*B.s ∧ 0< -C.s*B.c+C.c*B.s := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤B.c by linarith only [bb.1])
  have last := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
  have strict := mul_pos (show 0< -C.s by linarith only [negative])
    (show 0<B.c by linarith only [bb.1])
  have remaining := mul_nonneg (show 0≤C.c by linarith only [cb.1]) bn.1
  constructor <;> nlinarith only [first,last,strict,remaining]

theorem positive_central (C B : OpenSquare) (h : Input C B) (bn : Normal B.c B.s)
    (sep : upper B (-C.s) C.c≤C.loV) : False := by
  have faces := central_faces C B h
  have coefficients := positive_coefficients C B h.normal faces.negative bn
  let l := C.c*B.c+C.s*B.s
  let m := -C.s*B.c+C.c*B.s
  let P := 1+(43/500)*B.s^2-(13/50)*B.c*B.s
  let Q := (43/500)*B.c*B.s+(13/50)*B.s^2
  have formula := upper_pos_pos B (-C.s) C.c m l
    (by dsimp [m]) (by dsimp [l]; ring) coefficients.2.le coefficients.1
  have first := mul_pos coefficients.2
    (show 0<B.loU+B.side+(543/500)*B.s by linarith only [h.bottomMarker.2.1])
  have last := mul_nonneg coefficients.1
    (show 0≤B.loV+B.side-(13/50)*B.s+B.c by linarith only [h.bottomNear.2.2.2])
  have identity : m*(-(543/500)*B.s)+l*((13/50)*B.s-B.c)= -C.c*P+C.s*Q := by
    dsimp [m,l,P,Q]
    linear_combination -C.c*B.unit_normal
  have norm := positive_central_norm bn
  have dot := dot_le_one h.normal norm
  change P*C.c+Q*(-C.s)≤1 at dot
  have support : -1<upper B (-C.s) C.c := by
    dsimp [m,l] at formula identity
    nlinarith only [formula,identity,first,last,dot]
  linarith only [support,sep,faces.upperV,h.side]

theorem positive_u (C B : OpenSquare) (h : Input C B) (bn : Normal B.c B.s)
    (sum : 543/500<C.c-C.s) (sep : B.loU+B.side≤lower C B.c B.s) : False := by
  have faces := central_faces C B h
  have coefficients := positive_coefficients C B h.normal faces.negative bn
  let l := C.c*B.c+C.s*B.s
  let m := -C.s*B.c+C.c*B.s
  have formula := lower_nn C B.c B.s l m
    (by dsimp [l]; ring) (by dsimp [m]; ring) coefficients.1 coefficients.2.le
  have first := mul_nonneg coefficients.1
    (show 0≤-C.c/2-C.loU by linarith only [faces.upperLowU])
  have last := mul_nonneg coefficients.2.le
    (show 0≤-C.side-C.loV by linarith only [faces.upperV])
  have strict := mul_pos coefficients.2 (sub_pos.mpr h.side)
  have margin := positive_u_margin h.normal bn (by simpa only [sub_eq_add_neg] using sum)
  dsimp [l,m] at formula
  nlinarith only [formula,first,last,strict,margin,sep,h.bottomMarker.2.1]

theorem positive_v (C B : OpenSquare) (h : Input C B) (bn : Normal B.c B.s)
    (arc : 0≤C.c-C.s-1+C.c*C.s+(2/5)*C.s^2)
    (sep : B.loV+B.side≤lower C (-B.s) B.c) : False := by
  have faces := central_faces C B h
  have coefficients := positive_coefficients C B h.normal faces.negative bn
  let l := C.c*B.c+C.s*B.s
  let m := -C.s*B.c+C.c*B.s
  have formula := lower_np C (-B.s) B.c (-m) l
    (by dsimp [m]; ring) (by dsimp [l]; ring)
    (by linarith only [coefficients.2]) coefficients.1
  have first := mul_nonneg coefficients.2.le (sub_nonneg.mpr faces.lowerU)
  have last := mul_nonneg coefficients.1
    (show 0≤-C.side-C.loV by linarith only [faces.upperV])
  have wall := positive_wall C B h bn
  have bb := normal_bounds bn
  have product := mul_nonneg (show 0≤B.c by linarith only [bb.1])
    (show 0≤B.c+B.s by linarith only [bb.1,bn.1])
  have positive : 0<(1+B.c*(B.c+B.s))/2+m+l := by
    dsimp [m,l]
    nlinarith only [product,coefficients.1,coefficients.2]
  have strict := mul_pos (sub_pos.mpr h.side) positive
  have margin := positive_wall_margin h.normal bn (by nlinarith only [arc])
  dsimp [l,m] at formula strict
  nlinarith only [formula,first,last,wall,strict,margin,sep]

theorem nonnegative_impossible (C B : OpenSquare) (h : Input C B) (bn : Normal B.c B.s)
    (bad : (half C.c (-C.s))^2-2*half C.c (-C.s)+1/5≤0) : False := by
  have arc := bad_arc h.normal bad
  have canonical : |B.s|≤B.c := by rw [abs_of_nonneg bn.1]; exact bn.2.1
  rcases separators C B h canonical with own|first|last
  · exact positive_central C B h bn own
  · exact positive_u C B h bn (by nlinarith only [arc.2.2]) first
  · exact positive_v C B h bn (by nlinarith only [arc.2.1]) last

#print axioms nonnegative_impossible
end N12Compact.C1092MPPMInwardFinal.BottomAngle
