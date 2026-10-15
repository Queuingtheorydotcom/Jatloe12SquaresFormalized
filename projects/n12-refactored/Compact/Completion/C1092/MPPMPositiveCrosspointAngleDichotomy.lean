import Compact.Completion.C1092.MPPMPositiveCrosspointSeeds

/-! `C1092-MPPM-POSITIVE-CROSSPOINT-ANGLE-DICHOTOMY.md`, Theorem 1.
The literal excluded next crosspoint has exactly two possible weak exits.
The three ordinary-forward faces are obtained from their existing point
producer. Even the general upper-u cap A <= 0 is unnecessary here: the
stronger upper-u cap is a conclusion of its exit. The same square supplies
the strict outer halfpoint in the shallow alternative.

This is source translation only; no compiler or replay was run. -/
namespace N12Compact.C1092MPPMPositiveCrosspointAngleDichotomy
open S12 S12Pilot C977CornerCubic C1092MPPMPositiveCrosspointSeeds
set_option Elab.async false

structure Shallow (C : OpenSquare) : Prop where
  upperU : C.loU+C.side≤-C.s/2
  slope : 25*C.s<13*C.c
  ratio : C.s/C.c<13/25
  half : C1092WallProfileScalars.half C.c C.s<1/4
  backward : ¬C.Inside 0 (-13/50)
  outer : C.Inside (-1) (-1/2)

structure Steep (C : OpenSquare) : Prop where
  lowerV : -C.c/2≤C.loV
  half : 1/3<C1092WallProfileScalars.half C.c C.s
  angle : 1+C.c<3*C.s

/-- The reciprocal-free slope bound is strictly below the slope 8/15
at half-angle 1/4. The exact identity includes both interval endpoints. -/
private theorem quarter_lt_of_slope {c s : ℝ} (cn : Normal c s)
    (slope : 25*s<13*c) : C1092WallProfileScalars.half c s<1/4 := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  let q := C1092WallProfileScalars.half c s
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have qn : 0≤q := data.1
  have cosine : (1+q^2)*c=1-q^2 := data.2.2.2.1
  have sine : (1+q^2)*s=2*q := data.2.2.2.2
  have identity : (1+q^2)*(8*c-15*s)=-2*(4*q-1)*(q+4) := by
    linear_combination 8*cosine-15*sine
  have scaled : 0<(1+q^2)*(8*c-15*s) :=
    mul_pos (by positivity) (by linarith only [slope,cp])
  change q<1/4
  apply lt_of_not_ge
  intro low
  have product := mul_nonneg (show 0≤4*q-1 by linarith only [low])
    (show 0≤q+4 by linarith only [qn])
  nlinarith only [identity,scaled,product]

/-- Width greater than one forces the strict half-angle lower bound.
The factor 1-q is positive throughout the canonical sector. -/
private theorem third_lt_of_width {c s : ℝ} (cn : Normal c s)
    (width : 1<s+c/2) : 1/3<C1092WallProfileScalars.half c s := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  let q := C1092WallProfileScalars.half c s
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have cosine : (1+q^2)*c=1-q^2 := data.2.2.2.1
  have sine : (1+q^2)*s=2*q := data.2.2.2.2
  have high : q<1 := by
    change s/(1+c)<1
    apply (div_lt_one (show 0<1+c by linarith only [cp])).mpr
    linarith only [cn.2.1]
  have identity : (1+q^2)*(s+c/2-1)=(1-q)*(3*q-1)/2 := by
    linear_combination sine+(1/2)*cosine
  have scaled : 0<(1+q^2)*(s+c/2-1) :=
    mul_pos (by positivity) (by linarith only [width])
  change 1/3<q
  apply lt_of_not_ge
  intro low
  have product := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤1-q by linarith only [high])
    (show 3*q-1≤0 by linarith only [low])
  nlinarith only [identity,scaled,product]

/-- The local classification uses strict actual ordinary/forward points,
the actual northwest-marker exclusion, and the literal excluded next
crosspoint. No all-positive cycle or ownership reassignment is assumed. -/
theorem classify (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (positive : 0<C.s) (h : ForwardCore C)
    (north : ¬C.Inside (-7/20) (7/20))
    (next : ¬C.Inside 0 (-1/2)) : Shallow C ∨ Steep C := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  by_cases cap : C.loU+C.side≤-C.s/2
  · have slope : 25*C.s<13*C.c := by linarith only [h.forward.2.1,cap]
    have small := quarter_lt_of_slope cn slope
    have points := halfpoint_of_next_crosspoint C side cn positive h north
      (by linarith only [small]) next
    exact Or.inl ⟨cap,slope,(div_lt_iff₀ cp).mpr (by linarith only [slope]),
      small,points.2.1,points.2.2⟩
  · have lowerV : -C.c/2≤C.loV := by
      apply le_of_not_gt
      intro low
      apply next
      have high : -C.s/2<C.loU+C.side := lt_of_not_ge cap
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,h.marker.1,h.marker.2.2.2,cp,cn.1,cn.2.1]
    have faces := forward_profile C side cn h
    have width : 1<C.s+C.c/2 := by linarith only [side,lowerV,faces.upperV]
    have steep := third_lt_of_width cn width
    have angle := (lt_div_iff₀ (show 0<1+C.c by linarith only [cp])).mp
      (show (1/3:ℝ)<C.s/(1+C.c) from steep)
    exact Or.inr ⟨lowerV,steep,by linarith only [angle]⟩

/-- The weak face exits cannot coincide; their continuous angle ranges
are separated by the closed gap from 1/4 to 1/3. -/
theorem exclusive (C : OpenSquare) : ¬(Shallow C ∧ Steep C) := by
  rintro ⟨shallow,steep⟩
  linarith only [shallow.half,steep.half]

theorem exactly_one (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (positive : 0<C.s) (h : ForwardCore C)
    (north : ¬C.Inside (-7/20) (7/20))
    (next : ¬C.Inside 0 (-1/2)) :
    (Shallow C ∨ Steep C) ∧ ¬(Shallow C ∧ Steep C) :=
  ⟨classify C side cn positive h north next,exclusive C⟩

#print axioms classify
#print axioms exclusive
#print axioms exactly_one
end N12Compact.C1092MPPMPositiveCrosspointAngleDichotomy
