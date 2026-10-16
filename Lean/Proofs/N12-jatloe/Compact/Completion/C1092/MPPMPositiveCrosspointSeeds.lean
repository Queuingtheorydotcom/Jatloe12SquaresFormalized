import Compact.Completion.C1092.MPPMMissingPositiveFaces

/-! `C1092-MPPM-POSITIVE-CROSSPOINT-SEEDS.md`, sections 2--3, with the
literal point-to-face proof of `FORWARD-OWNED-POSITIVE-D`, Corollary 2.
The preceding-origin exclusion is a point premise in the forward-owned
local theorem. Its universal original-OOOO producer is not asserted here.
The missing-forward theorem obtains its faces from the completed geometric
producer, rather than receiving a face table as a new hypothesis.

No compiler, numerical search, certificate generation or replay was run. -/
namespace N12Compact.C1092MPPMPositiveCrosspointSeeds
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure ForwardCore (C : OpenSquare) : Prop where
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  ordinaryG : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  corner : ¬C.Inside (-1) (-1)
  previousOrigin : ¬C.Inside (-1) 0
  bottom : ¬C.Inside (-2/5) (-1)

structure ForwardInputs (C : OpenSquare) : Prop where
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  ordinaryG : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  corner : ¬C.Inside (-1) (-1)
  previousOrigin : ¬C.Inside (-1) 0
  bottom : ¬C.Inside (-2/5) (-1)
  farBottom : ¬C.Inside (-14/25) (-1)
  northMarker : ¬C.Inside (-7/20) (7/20)

def ForwardInputs.core {C : OpenSquare} (h : ForwardInputs C) : ForwardCore C :=
  ⟨h.marker,h.ordinaryP,h.ordinaryG,h.forward,h.corner,h.previousOrigin,h.bottom⟩

structure ForwardFaces (C : OpenSquare) : Prop where
  lowerU : -C.c-C.s≤C.loU
  lowerV : (2/5)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤C.s

/-- The three simultaneous ordinary-forward faces use the genuinely
excluded preceding origin. No ownership of that origin by a wall is used. -/
theorem forward_profile (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : ForwardCore C) : ForwardFaces C := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have upperV : C.loV+C.side≤C.s := by
    apply le_of_not_gt
    intro high
    apply h.previousOrigin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinaryP.1,h.ordinaryP.2.2.1,h.forward.2.1,cp,cn.1]
  have lowerU : -C.c-C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    have cornerV : C.s-C.c≤C.loV := by
      apply le_of_not_gt
      intro lowV
      apply h.corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,lowV,h.marker.2.1,h.ordinaryP.2.2.2,cp,cn.1]
    linarith only [cornerV,upperV,side,cb.2.1]
  have lowerV : (2/5)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply h.bottom
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.ordinaryG.1,h.marker.2.1,h.ordinaryP.2.2.2,
        cp,cn.1,cn.2.1]
  exact ⟨lowerU,lowerV,upperV⟩

private theorem half_width {c s : ℝ} (cn : Normal c s)
    (small : C1092WallProfileScalars.half c s≤1/3) : s+c/2≤1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let q := C1092WallProfileScalars.half c s
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have qn : 0≤q := data.1
  have qu : q≤1 := data.2.1
  have cosine : (1+q^2)*c=1-q^2 := data.2.2.2.1
  have sine : (1+q^2)*s=2*q := data.2.2.2.2
  have positive := mul_nonneg (show 0≤1-q by linarith only [qu])
    (show 0≤1-3*q by dsimp [q]; linarith only [small])
  have identity : (1+q^2)*(1-s-c/2)=(1-q)*(1-3*q)/2 := by
    linear_combination -(1/2)*cosine-sine
  have scaled : 0≤(1+q^2)*(1-s-c/2) := by rw [identity]; linarith only [positive]
  have result := nonneg_of_mul_nonneg_right scaled
    (show 0<1+q^2 by nlinarith only [sq_nonneg q])
  linarith only [result]

private theorem half_identity {c s : ℝ} (cn : Normal c s) :
    s*C1092WallProfileScalars.half c s=1-c := by
  have cb := normal_bounds cn
  have den : 1+c≠0 := by linarith only [cb.1]
  dsimp [C1092WallProfileScalars.half]
  field_simp [den]
  nlinarith only [cn.2.2]

/-- The owned-forward crosspoint is strict for every canonical angle.
The two half-angle intervals are exhaustive and retain their shared
endpoint. In the small interval the one literal foreign bottom point
forces the stronger transverse face. -/
theorem crosspoint_of_forward (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : ForwardInputs C) : C.Inside (-1/2) 0 := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have faces := forward_profile C side cn h.core
  have highV : C.s/2<C.loV+C.side := by
    let q := C1092WallProfileScalars.half C.c C.s
    by_cases large : 1/10≤q
    · have product := mul_nonneg cn.1 (sub_nonneg.mpr large)
      have identity := half_identity cn
      change C.s*q=1-C.c at identity
      nlinarith only [faces.lowerV,side,product,identity]
    · have small : q≤1/10 := (lt_of_not_ge large).le
      have relation := (C1092WallProfileScalars.quarter_data C.c C.s
        cp.le cn.1 cn.2.2).2.2.1
      change q*(1+C.c)=C.s at relation
      have product := mul_le_mul_of_nonneg_right small
        (show 0≤1+C.c by linarith only [cp])
      have sine : C.s≤1/5 := by nlinarith only [product,relation,cb.2.1]
      have stronger : (14/25)*C.s-C.c≤C.loV := by
        apply le_of_not_gt
        intro low
        apply h.farBottom
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [low,h.ordinaryG.1,h.marker.2.1,h.ordinaryP.2.2.2,
            cb.1,sine,cp,cn.1]
      linarith only [stronger,side,cb.2.1,cn.1]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.ordinaryG.1,cp,cn.1]
  · linarith only [h.forward.2.1,cp]
  · linarith only [faces.upperV,side,cb.2.2.2.1]
  · linarith only [highV]

/-- The missing-forward seed has the manuscript's stated additional
half-angle ceiling. All faces are produced from literal point data. -/
theorem crosspoint_of_missing (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : C1092MPPMMissingPositiveFaces.Inputs C)
    (small : C1092WallProfileScalars.half C.c C.s≤1/3) :
    C.Inside (-1/2) 0 := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have faces := C1092MPPMMissingPositiveFaces.profile C side cn h
  have width := half_width cn small
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.ordinaryG.1,cp,cn.1]
  · linarith only [faces.lowerU,side,width]
  · linarith only [faces.upperV,side,cb.2.2.2.1]
  · linarith only [faces.lowerV,side,cb.2.1,cn.1]

/-- A foreign next crosspoint forces the same-square upper-u cap, an
exclusion of the backward inner point, and the strict outer halfpoint.
The next crosspoint is a literal exclusion, never inferred by reassigning
an omitted next-forward auxiliary. -/
theorem halfpoint_of_next_crosspoint (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (positive : 0<C.s) (h : ForwardCore C)
    (north : ¬C.Inside (-7/20) (7/20))
    (small : C1092WallProfileScalars.half C.c C.s≤1/3)
    (next : ¬C.Inside 0 (-1/2)) :
    C.loU+C.side≤-C.s/2 ∧ ¬C.Inside 0 (-13/50) ∧ C.Inside (-1) (-1/2) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have faces := forward_profile C side cn h
  have width := half_width cn small
  have cap : C.loU+C.side≤-C.s/2 := by
    apply le_of_not_gt
    intro high
    have lowerV : -C.c/2≤C.loV := by
      apply le_of_not_gt
      intro low
      apply next
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,h.marker.1,h.marker.2.2.2,cp,cn.1,cn.2.1]
    linarith only [lowerV,faces.upperV,side,width]
  have backward : ¬C.Inside 0 (-13/50) := by
    intro own
    linarith only [own.2.1,cap,positive]
  have halfLowV : C.loV<C.s-C.c/2 := by
    apply lt_of_not_ge
    intro low
    have slope : 13*C.s<3*C.c := by linarith only [low,h.marker.2.2.1]
    have northCap : C.loV+C.side≤(7/20)*(C.c+C.s) := by
      apply le_of_not_gt
      intro high
      apply north
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,h.ordinaryP.1,h.forward.2.1,h.marker.2.2.1,
          slope,cp,cn.1]
    linarith only [low,northCap,side,cb.2.1,cn.1]
  refine ⟨cap,backward,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,cb.2.1]
  · linarith only [h.marker.2.1,cp,cn.1]
  · linarith only [halfLowV]
  · linarith only [h.ordinaryG.2.2.2,cp]

#print axioms crosspoint_of_forward
#print axioms crosspoint_of_missing
#print axioms halfpoint_of_next_crosspoint
end N12Compact.C1092MPPMPositiveCrosspointSeeds
