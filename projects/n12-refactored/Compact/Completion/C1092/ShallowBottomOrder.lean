import Compact.Completion.C1092.ShallowBottomMargin
import Compact.Completion.C1092.ShallowBoundarySupport
import Compact.Completion.C1092.MixedCornerSupports

/-! The complete actual bottom-center envelope in the shallow-positive
wall-order theorem. Every boundary orientation is unrestricted, and every
separating-axis source uses the same central upper face. -/
namespace N12Compact.C1092ShallowWallOrder
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowPositiveScalars C1092ShallowCentralScalars
open C1092ShallowBoundarySupport
set_option Elab.async false

structure Data (C : OpenSquare) (x : ℝ) : Prop where
  positive : 0<x
  shallow : x≤1/4
  cosine : C.c=cosH x
  sine : C.s=sinH x
  normal : Normal C.c C.s
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-C.s/2
  lowerV : (14/25)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤C.s
  marker : C.Inside (-7/20) (-7/20)
  outer : C.Inside (-1) (-13/50)

theorem bottom_order (C B : OpenSquare) (x : ℝ) (side : 1<C.side)
    (same : C.side=B.side) (data : Data C x)
    (marker : B.Inside 0 (-543/500)) (outer : B.Inside (-2/5) (-1))
    (wall : ∀ u v, B.Inside u v → -2≤v)
    (apart : ∀ u v, ¬(C.Inside u v ∧ B.Inside u v)) :
    b C.side C.c C.s (C.loV+C.side)≤centerX B := by
  classical
  apply le_of_not_gt
  intro below
  have cp : 0<C.c := by
    rw [data.cosine]
    exact half_cos_pos x data.positive.le (by linarith only [data.shallow])
  have sp : 0<C.s := by rw [data.sine]; exact half_sin_pos x data.positive
  have shallow : 7/17≤C.c-C.s := by
    simpa only [←data.cosine,←data.sine] using
      (C1092ShallowCentralScalars.bounds x data.positive data.shallow).2.2
  have intrinsic : C.side≤C.c+(11/25)*C.s := by
    linarith only [data.lowerV,data.upperV]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower C nx ny) : 0<ny ∧ nx<(413/500)*ny := by
    have a := (strict_bounds B _ _ nx ny unit marker).2
    have b := (strict_bounds C _ _ nx ny unit data.outer).1
    have c := (strict_bounds B _ _ nx ny unit outer).2
    have d := (strict_bounds C _ _ nx ny unit data.marker).1
    constructor <;> linarith only [a,b,c,d,sep]
  have central : ¬upper B (-C.s) C.c≤lower C (-C.s) C.c := by
    intro sep
    have height := bottom_center B wall
    have width := (width_bounds B data.normal).1
    rw [←same] at height width
    have heightWeight := mul_nonneg cp.le (sub_nonneg.mpr height)
    have widthGap := sub_nonneg.mpr width
    have strict := mul_pos sp (sub_pos.mpr below)
    have coordinate : C.s*b C.side C.c C.s (C.loV+C.side)=
        C.side*(3/2+C.c*(C.c+C.s)/2)-(C.loV+C.side)-2*C.c := by
      dsimp [b]
      field_simp [sp.ne']
    have identity : upper B (-C.s) C.c-C.loV=
        C.s*(b C.side C.c C.s (C.loV+C.side)-centerX B)+
        C.c*(centerY B+2-C.side*width0 B/2)+
        (C.c*(C.side*width0 B/2)+supportRadius B (-C.s) C.c-
          C.side*(1+C.c*(C.c+C.s))/2) := by
      dsimp [upper]
      linear_combination -coordinate
    have heightGap : 0≤C.c*(centerY B+2-C.side*width0 B/2) := by
      convert heightWeight using 1 <;> ring
    have positive : 0<upper B (-C.s) C.c-C.loV := by
      rw [identity]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg strict heightGap) widthGap
    rw [(ownV C).1] at sep
    exact (not_lt_of_ge (sub_nonpos.mpr sep)) positive
  have northeast (nx ny : ℝ) (unit : nx^2+ny^2=1) (east : 0≤nx)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have direction := cone nx ny unit sep
    let lambda := C.c*nx+C.s*ny
    let mu := C.c*ny-C.s*nx
    have lp : 0<lambda := add_pos_of_nonneg_of_pos (mul_nonneg cp.le east)
      (mul_pos sp direction.1)
    have mp : 0<mu := by
      have first := mul_pos (show 0<C.c-C.s by linarith only [shallow]) direction.1
      have last := mul_nonneg sp.le
        (show 0≤ny-nx by linarith only [direction.1,direction.2])
      dsimp [mu]
      nlinarith only [first,last]
    have support := lower_nn C nx ny lambda mu (by dsimp [lambda]; ring)
      (by dsimp [mu]; ring) lp.le mp.le
    have uWeight := mul_le_mul_of_nonneg_left
      (show C.loU≤-C.s/2-C.side by linarith only [data.upperU]) lp.le
    have vWeight := mul_le_mul_of_nonneg_left
      (show C.loV≤C.s-C.side by linarith only [data.upperV]) mp.le
    have extra := mul_pos (sub_pos.mpr side) (add_pos lp mp)
    have bound : lower C nx ny<lambda*(-C.s/2-1)+mu*(C.s-1) := by
      calc
        _ = lambda*C.loU+mu*C.loV := support
        _ ≤ lambda*(-C.s/2-C.side)+mu*(C.s-C.side) := add_le_add uWeight vWeight
        _ < lambda*(-C.s/2-1)+mu*(C.s-1) := by
          apply sub_pos.mp
          convert extra using 1 <;> ring
    have brackets := C1092ShallowCentralScalars.brackets x data.positive data.shallow
      (by simpa only [←data.cosine,←data.sine] using data.normal)
    have f : -C.c+C.s+2/5-C.s^2-(1/2)*C.c*C.s<0 := by
      simpa only [←data.cosine,←data.sine] using brackets.1
    have g : 1-C.c-C.s+C.c*C.s-C.s^2/2<0 := by
      simpa only [←data.cosine,←data.sine] using brackets.2.1
    have first := mul_nonpos_of_nonneg_of_nonpos east f.le
    have last := mul_neg_of_pos_of_neg direction.1 g
    have margin : lambda*(-C.s/2-1)+mu*(C.s-1)-((-2/5)*nx-ny)<0 := by
      have identity : lambda*(-C.s/2-1)+mu*(C.s-1)-((-2/5)*nx-ny)=
          nx*(-C.c+C.s+2/5-C.s^2-(1/2)*C.c*C.s)+
            ny*(1-C.c-C.s+C.c*C.s-C.s^2/2) := by dsimp [lambda,mu]; ring
      rw [identity]
      exact add_neg_of_nonpos_of_neg first last
    have point := (strict_bounds B _ _ nx ny unit outer).2
    have comparison : lambda*(-C.s/2-1)+mu*(C.s-1)<nx*(-2/5)+ny*(-1) := by
      convert sub_neg.mp margin using 1 <;> ring
    exact (not_lt_of_ge sep) ((bound.trans comparison).trans point)
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal B nx ny)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    by_cases east : 0≤nx
    · exact northeast nx ny unit east sep
    · have direction := cone nx ny unit sep
      let h := -nx
      have hn : 0≤h := by dsimp [h]; linarith only [east]
      have unit' : h^2+ny^2=1 := by dsimp [h]; nlinarith only [unit]
      have face' : FaceNormal B (-h) ny := by simpa only [h,neg_neg] using face
      have bottom := bottom_face B h ny hn direction.1.le wall face'
      rw [←same] at bottom
      let delta := C.s*ny-C.c*h
      let kappa := C.s*h+C.c*ny
      have kp : 0<kappa := add_pos_of_nonneg_of_pos (mul_nonneg sp.le hn)
        (mul_pos cp direction.1)
      have lowerFormula : lower C (-h) ny=
          delta*(C.loU+C.side)+kappa*((C.loV+C.side)-C.side)-C.side*max delta 0 := by
        by_cases sign : 0≤delta
        · rw [lower_nn C (-h) ny delta kappa (by dsimp [delta]; ring)
            (by dsimp [kappa]; ring) sign kp.le,max_eq_left sign]
          ring
        · have sign' : delta≤0 := (lt_of_not_ge sign).le
          rw [lower_np C (-h) ny delta kappa (by dsimp [delta]; ring)
            (by dsimp [kappa]; ring) sign' kp.le,max_eq_right sign']
          ring
      have margin := C1092ShallowBottomMargin.margin C.side C.c C.s (C.loU+C.side)
        (C.loV+C.side) h ny x side data.positive data.shallow data.cosine data.sine
        hn direction.1.le unit'
        (by linarith only [data.lowerU]) data.upperU
        (by linarith only [data.lowerV]) data.upperV intrinsic
      have strict := mul_pos (show 0<h by dsimp [h]; linarith only [east])
        (sub_pos.mpr below)
      have positive := add_pos_of_nonneg_of_pos margin.1 strict
      have physical : C1092ShallowBottomMargin.gap C.side C.c C.s (C.loU+C.side)
          (C.loV+C.side) h ny+h*(b C.side C.c C.s (C.loV+C.side)-centerX B)≤
          upper B (-h) ny-lower C (-h) ny := by
        calc
          _ = -h*centerX B-2*ny+(C.side/2)*(1+ny^2+h*ny)-lower C (-h) ny := by
            rw [lowerFormula]
            dsimp [C1092ShallowBottomMargin.gap,delta,kappa]
            ring
          _ ≤ _ := sub_le_sub_right bottom _
      have overlap := positive.trans_le physical
      have sep' : upper B (-h) ny≤lower C (-h) ny := by simpa only [h,neg_neg] using sep
      exact (not_lt_of_ge (sub_nonpos.mpr sep')) overlap
  have flip (nx ny : ℝ) (sep : upper C nx ny≤lower B nx ny) :
      upper B (-nx) (-ny)≤lower C (-nx) (-ny) := by
    rw [(C1092MixedCornerSupports.negative_support B nx ny).2,
      (C1092MixedCornerSupports.negative_support C nx ny).1]
    exact neg_le_neg sep
  have all := CongruentSAT.faceSeparation_of_disjoint C B same apart
  change pairRadius C B≤|C.c*(centerX B-centerX C)+C.s*(centerY B-centerY C)| ∨
    pairRadius C B≤|-C.s*(centerX B-centerX C)+C.c*(centerY B-centerY C)| ∨
    pairRadius B C≤|B.c*(centerX B-centerX C)+B.s*(centerY B-centerY C)| ∨
    pairRadius B C≤|-B.s*(centerX B-centerX C)+B.c*(centerY B-centerY C)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius B nx ny=radius)
      (sep : radius≤|nx*(centerX B-centerX C)+ny*(centerY B-centerY C)|) :=
    separated C B nx ny (by rwa [identity])
  rcases all with cu | cv | bu | bv
  · have sep := split C.c C.s _ (parallel_radius C B) cu
    rcases sep with forward | reverse
    · have direction := (cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (flip _ _ forward)).1
      linarith only [direction,sp]
    · have direction := (cone C.c C.s C.unit_normal reverse).2
      linarith only [direction,shallow,sp]
  · have sep := split (-C.s) C.c _ (transverse_radius C B) cv
    rcases sep with forward | reverse
    · have direction := (cone C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using flip _ _ forward)).1
      linarith only [direction,cp]
    · exact central reverse
  · have identity : supportRadius C B.c B.s+supportRadius B B.c B.s=pairRadius B C := by
      rw [add_comm]
      exact parallel_radius B C
    have sep := split B.c B.s _ identity bu
    rcases sep with forward | reverse
    · exact boundary (-B.c) (-B.s) (by nlinarith only [B.unit_normal])
        (Or.inr (Or.inl ⟨rfl,rfl⟩)) (flip _ _ forward)
    · exact boundary B.c B.s B.unit_normal (Or.inl ⟨rfl,rfl⟩) reverse
  · have identity : supportRadius C (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B C := by
      rw [add_comm]
      exact transverse_radius B C
    have sep := split (-B.s) B.c _ identity bv
    rcases sep with forward | reverse
    · exact boundary B.s (-B.c) (by nlinarith only [B.unit_normal])
        (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))) (by simpa only [neg_neg] using flip _ _ forward)
    · exact boundary (-B.s) B.c (by nlinarith only [B.unit_normal])
        (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))) reverse

#print axioms bottom_order
end N12Compact.C1092ShallowWallOrder
