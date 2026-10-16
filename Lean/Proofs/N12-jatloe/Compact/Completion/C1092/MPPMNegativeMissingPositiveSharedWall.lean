import Compact.Completion.C1092.MPPMNegativeMissingPositiveSharedWallScalars
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesBottom
import Compact.Completion.C1092.TwoFifthsSupport

/-! NEGATIVE-MISSING-POSITIVE-SHARED-WALL Theorem 1. This is the
positive retained-forward profile, not the different missing-positive
profile. The actual left square has arbitrary orientation; its literal
marker, origin, and one real wall are the entire boundary input. -/
namespace N12Compact.C1092MPPMNegativeMissingPositiveSharedWall
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowBoundarySupport C1092MPPMCrosspointSupport
open C1092MPPMMissingPositiveBoundaries.Envelopes
set_option Elab.async false
noncomputable section

structure Data (C : OpenSquare) : Prop where
  normal : Normal C.c C.s
  positive : 0<C.s
  halfCap : C.s/(1+C.c)≤3/10
  ordinary : C.Inside (-1) (-13/50)
  crosspoint : C.Inside (-1/2) 0
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤0
  lowerV : (14/25)*C.s-C.c≤C.loV

private theorem northwest (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h r : ℝ) (q : Quarter h r) :
    2*h+r/5-(C.side/2)*(1+h^2+h*r)<upper C (-h) r := by
  let c := C.c
  let s := C.s
  let lam := -c*h+s*r
  let kap := c*r+s*h
  have cp : 0<c := by linarith only [(normal_bounds d.normal).1]
  have sp : 0<s := d.positive
  have hn := q.cosine
  have rn := q.sine
  have sum : 1≤h+r := by
    have product := mul_nonneg hn rn
    nlinarith only [q.unit,product,sq_nonneg (h+r-1),hn,rn]
  have kp : 0<kap := by
    have first := mul_nonneg (sub_nonneg.mpr d.normal.2.1) rn
    have last := mul_nonneg sp.le (sub_nonneg.mpr sum)
    dsimp [kap,c,s]
    nlinarith only [first,last,sp]
  have width : 0<1+h^2+h*r := by nlinarith only [sq_nonneg h,mul_nonneg hn rn]
  by_cases before : lam≤0
  · have formula := upper_np C (-h) r lam kap
      (by dsimp [lam,c,s]; ring) (by dsimp [kap,c,s]; ring) before kp.le
    have first := mul_le_mul_of_nonpos_left d.upperU before
    have last := mul_le_mul_of_nonneg_left d.lowerV kp.le
    have extra := mul_pos (sub_pos.mpr side)
      (show 0<kap-lam+(1+h^2+h*r)/2 by linarith only [kp,before,width])
    have margin := Scalars.northwest_before d.normal d.halfCap q
    have identity : kap-lam+(1+h^2+h*r)/2+kap*((14/25)*s-c)-2*h-r/5=
        leftValue 1 (Scalars.A1 c s) (Scalars.B1 c s) h r := by
      dsimp [kap,lam,leftValue,Scalars.A1,Scalars.B1]
      linear_combination -r*d.normal.2.2
    nlinarith only [formula,first,last,extra,margin,identity]
  · have after : 0≤lam := (lt_of_not_ge before).le
    have formula := C1092TwoFifths.Support.upper_pos_pos C (-h) r lam kap
      (by dsimp [lam,c,s]; ring) (by dsimp [kap,c,s]; ring) after kp.le
    have first := mul_le_mul_of_nonneg_left d.lowerU after
    have last := mul_le_mul_of_nonneg_left d.lowerV kp.le
    have extra := mul_pos (sub_pos.mpr side)
      (show 0<lam+kap+(1+h^2+h*r)/2 by linarith only [after,kp,width])
    have margin := Scalars.northwest_after d.normal d.positive d.halfCap q
      (show 0≤s*r-c*h by dsimp [lam] at after; linarith only [after])
    have identity : lam+kap+(1+h^2+h*r)/2-lam*(c+s)+kap*((14/25)*s-c)-2*h-r/5=
        leftValue 1 (Scalars.A2 c s) (Scalars.B2 c s) h r := by
      dsimp [kap,lam,leftValue,Scalars.A2,Scalars.B2]
      linear_combination (h-r)*d.normal.2.2
    nlinarith only [formula,first,last,extra,margin,identity]

theorem left_order (C L : OpenSquare) (side : 1<C.side) (same : C.side=L.side)
    (d : Data C) (marker : L.Inside (-543/500) 0) (origin : L.Inside (-1) 0)
    (wall : ∀ x y,L.Inside x y→-2≤x)
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) : 1/5<centerY L := by
  classical
  apply lt_of_not_ge
  intro below
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp : 0<C.s := d.positive
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower L nx ny) : nx<0 ∧ 0<ny := by
    have first := (strict_bounds C _ _ nx ny unit d.ordinary).2
    have second := (strict_bounds C _ _ nx ny unit d.crosspoint).2
    have target := (strict_bounds L _ _ nx ny unit origin).1
    have anchor := (strict_bounds L _ _ nx ny unit marker).1
    constructor <;> linarith only [first,second,target,anchor,sep]
  have central : ¬upper C (-C.s) C.c≤lower L (-C.s) C.c := by
    intro sep
    have horizontal := left_center L wall
    have width := (width_bounds L d.normal).2
    rw [←same] at horizontal width
    have horizontalWeight := mul_le_mul_of_nonneg_left horizontal sp.le
    have centerWeight := mul_le_mul_of_nonneg_left below cp.le
    rw [(ownV C).2] at sep
    have margin := Scalars.central_positive d.normal d.halfCap
    have coefficient : 0<3/2+C.s*(C.c+C.s)/2 := by
      have product := mul_nonneg sp.le (show 0≤C.c+C.s by linarith only [cp,sp])
      nlinarith only [product]
    have extra := mul_pos (sub_pos.mpr side) coefficient
    dsimp [lower] at sep
    dsimp [Scalars.F0] at margin
    nlinarith only [sep,horizontalWeight,centerWeight,width,d.lowerV,margin,extra]
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal L nx ny)
      (sep : upper C nx ny≤lower L nx ny) : False := by
    have direction := cone nx ny unit sep
    let h := -nx
    have hn : 0≤h := by dsimp [h]; linarith only [direction.1]
    have face' : FaceNormal L (-h) ny := by simpa only [h,neg_neg] using face
    have physical := left_face L h ny hn direction.2.le wall face'
    rw [←same] at physical
    have centerWeight := mul_le_mul_of_nonneg_left below direction.2.le
    have margin := northwest C side d h ny
      ⟨hn,direction.2.le,by dsimp [h]; nlinarith only [unit]⟩
    have sep' : upper C (-h) ny≤lower L (-h) ny := by simpa only [h,neg_neg] using sep
    nlinarith only [physical,centerWeight,margin,sep']
  obtain ⟨nx,ny,unit,face,sep⟩ := directed_faces C L same apart
  rcases face with own|foreign
  · rcases own with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,cp]
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,sp]
    · exact central sep
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,cp]
  · exact boundary nx ny unit foreign sep

end
#print axioms left_order
end N12Compact.C1092MPPMNegativeMissingPositiveSharedWall
