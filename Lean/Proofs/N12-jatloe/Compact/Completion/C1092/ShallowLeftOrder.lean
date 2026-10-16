import Compact.Completion.C1092.ShallowBottomOrder
import Compact.Completion.C1092.ShallowLeftMargin

/-! The complete actual left comparison and shallow-positive wall order.
The same central K from the bottom envelope is retained through the
strict actual origin cap in every northwest boundary source. -/
namespace N12Compact.C1092ShallowWallOrder
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowPositiveScalars C1092ShallowCentralScalars
open C1092ShallowBoundarySupport
set_option Elab.async false

theorem left_order (C L : OpenSquare) (x : ℝ) (side : 1<C.side)
    (same : C.side=L.side) (data : Data C x)
    (marker : L.Inside (-543/500) 0) (origin : L.Inside (-1) 0)
    (wall : ∀ u v, L.Inside u v → -2≤u)
    (apart : ∀ u v, ¬(C.Inside u v ∧ L.Inside u v)) :
    -b C.side C.c C.s (C.loV+C.side)<centerY L := by
  classical
  apply lt_of_not_ge
  intro below
  have cp : 0<C.c := by
    rw [data.cosine]
    exact half_cos_pos x data.positive.le (by linarith only [data.shallow])
  have sp : 0<C.s := by rw [data.sine]; exact half_sin_pos x data.positive
  have shallow : 7/17≤C.c-C.s := by
    simpa only [←data.cosine,←data.sine] using
      (C1092ShallowCentralScalars.bounds x data.positive data.shallow).2.2
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower L nx ny) : 0<ny ∧ nx<(175/368)*ny := by
    have a := (strict_bounds C _ _ nx ny unit data.outer).2
    have b := (strict_bounds L _ _ nx ny unit origin).1
    have c := (strict_bounds C _ _ nx ny unit data.marker).2
    have d := (strict_bounds L _ _ nx ny unit marker).1
    constructor <;> linarith only [a,b,c,d,sep]
  have central : ¬upper C (-C.s) C.c≤lower L (-C.s) C.c := by
    intro sep
    have sum := same_face_sum side data.normal sp data.upperV
    have height : centerY L<ell C.side C.c C.s (C.loV+C.side) := by
      linarith only [sum,below]
    have horizontal := left_center L wall
    have width := (width_bounds L data.normal).2
    rw [←same] at horizontal width
    have horizontalWeight := mul_nonneg sp.le (sub_nonneg.mpr horizontal)
    have widthGap := sub_nonneg.mpr width
    have strict := mul_pos cp (sub_pos.mpr height)
    have coordinate : C.c*ell C.side C.c C.s (C.loV+C.side)=
        (C.loV+C.side)-2*C.s+(C.side/2)*(1+C.s*(C.c+C.s)) := by
      dsimp [ell]
      field_simp [cp.ne']
    have identity : (C.loV+C.side)-lower L (-C.s) C.c=
        C.c*(ell C.side C.c C.s (C.loV+C.side)-centerY L)+
        C.s*(centerX L+2-C.side*width0 L/2)+
        (C.s*(C.side*width0 L/2)+supportRadius L (-C.s) C.c-
          C.side*(1+C.s*(C.c+C.s))/2) := by
      dsimp [lower]
      linear_combination -coordinate
    have horizontalGap : 0≤C.s*(centerX L+2-C.side*width0 L/2) := by
      convert horizontalWeight using 1 <;> ring
    have positive : 0<(C.loV+C.side)-lower L (-C.s) C.c := by
      rw [identity]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg strict horizontalGap) widthGap
    rw [(ownV C).2] at sep
    exact (not_lt_of_ge (sub_nonpos.mpr sep)) positive
  have northeast (nx ny : ℝ) (unit : nx^2+ny^2=1) (east : 0≤nx)
      (sep : upper C nx ny≤lower L nx ny) : False := by
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
    have support := C1092MixedCornerSupports.upper_nn C nx ny lambda mu
      (by dsimp [lambda]; ring) (by dsimp [mu]; ring) lp.le mp.le
    have uWeight := mul_le_mul_of_nonneg_left
      (show C.side-C.c-C.s≤C.loU+C.side by linarith only [data.lowerU]) lp.le
    have vWeight := mul_le_mul_of_nonneg_left
      (show C.side+(14/25)*C.s-C.c≤C.loV+C.side by linarith only [data.lowerV]) mp.le
    have extra := mul_pos (sub_pos.mpr side) (add_pos lp mp)
    have bound : lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)<upper C nx ny := by
      calc
        _ < lambda*(C.side-C.c-C.s)+mu*(C.side+(14/25)*C.s-C.c) := by
          apply sub_pos.mp
          convert extra using 1 <;> ring
        _ ≤ lambda*(C.loU+C.side)+mu*(C.loV+C.side) := add_le_add uWeight vWeight
        _ = upper C nx ny := support.symm
    have brackets := C1092ShallowCentralScalars.brackets x data.positive data.shallow
      (by simpa only [←data.cosine,←data.sine] using data.normal)
    have f : 0<C.c-C.s+(11/25)*C.s^2 := by
      simpa only [←data.cosine,←data.sine] using brackets.2.2.1
    have g : 0<C.c+C.s-1-(11/25)*C.c*C.s := by
      simpa only [←data.cosine,←data.sine] using brackets.2.2.2
    have first := mul_nonneg east f.le
    have last := mul_pos direction.1 g
    have margin : 0<lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)+nx := by
      have identity : lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)+nx=
          nx*(C.c-C.s+(11/25)*C.s^2)+ny*(C.c+C.s-1-(11/25)*C.c*C.s) := by
        dsimp [lambda,mu]
        linear_combination -(nx+ny)*C.unit_normal
      rw [identity]
      exact add_pos_of_nonneg_of_pos first last
    have point := (strict_bounds L _ _ nx ny unit origin).1
    have comparison : nx*(-1)+ny*0<lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c) := by
      linarith only [margin]
    exact (not_lt_of_ge sep) (point.trans (comparison.trans bound))
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal L nx ny)
      (sep : upper C nx ny≤lower L nx ny) : False := by
    by_cases east : 0≤nx
    · exact northeast nx ny unit east sep
    · have direction := cone nx ny unit sep
      let h := -nx
      have hp : 0<h := by dsimp [h]; linarith only [east]
      have unit' : ny^2+h^2=1 := by dsimp [h]; nlinarith only [unit]
      have face' : FaceNormal L (-h) ny := by simpa only [h,neg_neg] using face
      have sep' : upper C (-h) ny≤lower L (-h) ny := by simpa only [h,neg_neg] using sep
      have point : lower L (-h) ny<h := by
        have raw := (strict_bounds L _ _ (-h) ny
          (by nlinarith only [unit']) origin).1
        linarith only [raw]
      let delta := C.s*ny-C.c*h
      let kappa := C.s*h+C.c*ny
      have kp : 0<kappa := add_pos_of_nonneg_of_pos (mul_nonneg sp.le hp.le)
        (mul_pos cp direction.1)
      by_cases small : ny≤h
      · have sign : delta≤0 := by
          have first := mul_pos (show 0<C.c-C.s by linarith only [shallow]) hp
          have last := mul_nonneg sp.le (sub_nonneg.mpr small)
          dsimp [delta]
          nlinarith only [first,last]
        have support := upper_np C (-h) ny delta kappa (by dsimp [delta]; ring)
          (by dsimp [kappa]; ring) sign kp.le
        have uWeight := mul_le_mul_of_nonpos_left
          (show C.loU≤-C.side-C.s/2 by linarith only [data.upperU]) sign
        have vWeight := mul_le_mul_of_nonneg_left
          (show C.side+(14/25)*C.s-C.c≤C.loV+C.side by linarith only [data.lowerV]) kp.le
        have lower : delta*(-C.side-C.s/2)+kappa*(C.side+(14/25)*C.s-C.c)≤upper C (-h) ny := by
          rw [support]
          exact add_le_add uWeight vWeight
        have scalars := C1092ShallowCentralScalars.small_left C.side x side data.positive data.shallow
          (by simpa only [←data.cosine,←data.sine] using data.normal)
        let P0 := C.side*(C.c+C.s)-(1/2)*C.c*C.s+(14/25)*C.s^2-1
        let Zy := C.side*(C.c-C.s)+(14/25)*C.c*C.s-C.s^2/2-C.c^2
        have p : 0<P0 := by simpa only [P0,←data.cosine,←data.sine] using scalars.1
        have both : 0<P0+Zy := by
          simpa only [P0,Zy,←data.cosine,←data.sine] using scalars.2
        have first := mul_nonneg (sub_nonneg.mpr small) p.le
        have last := mul_pos direction.1 both
        have identity : delta*(-C.side-C.s/2)+kappa*(C.side+(14/25)*C.s-C.c)-h=
            (h-ny)*P0+ny*(P0+Zy) := by dsimp [delta,kappa,P0,Zy]; ring
        have strict : h<delta*(-C.side-C.s/2)+kappa*(C.side+(14/25)*C.s-C.c) := by
          apply sub_pos.mp
          rw [identity]
          exact add_pos_of_nonneg_of_pos first last
        exact (not_lt_of_ge sep') (point.trans (strict.trans_le lower))
      · let k := C.c*ny+C.s*h
        let tau := C.c*h-C.s*ny
        have kpos : 0<k := by simpa only [k,kappa,add_comm] using kp
        have normal : Normal ny h := ⟨hp.le,by linarith only [small],unit'⟩
        have upperFormula : upper C (-h) ny=
            -tau*(C.loU+C.side)+k*(C.loV+C.side)+C.side*max tau 0 := by
          by_cases sign : 0≤tau
          · rw [upper_np C (-h) ny (-tau) k (by dsimp [tau]; ring)
              (by dsimp [k]; ring) (by linarith only [sign]) kpos.le,max_eq_left sign]
            ring
          · have sign' : tau≤0 := (lt_of_not_ge sign).le
            rw [C1092MixedCornerSupports.upper_nn C (-h) ny (-tau) k
              (by dsimp [tau]; ring) (by dsimp [k]; ring)
              (by linarith only [sign']) kpos.le,max_eq_right sign']
            ring
        have coupled : -tau*(C.loU+C.side)+k*(C.loV+C.side)+C.side*max tau 0<h := by
          rw [←upperFormula]
          exact sep'.trans_lt point
        have margin := C1092ShallowLeftMargin.margin C.side C.c C.s (C.loU+C.side)
          (C.loV+C.side) h ny x side data.positive data.shallow data.cosine data.sine
          data.normal normal (by linarith only [data.lowerU]) data.upperU coupled
        have wallBound := left_face L h ny hp.le direction.1.le wall face'
        rw [←same] at wallBound
        have height := mul_le_mul_of_nonneg_left below direction.1.le
        have outerBound : lower L (-h) ny≤2*h-ny*b C.side C.c C.s (C.loV+C.side)-
            (C.side/2)*(1+h^2+h*ny) := by
          apply wallBound.trans
          have weighted := add_le_add_left height
            (2*h-(C.side/2)*(1+h^2+h*ny))
          convert weighted using 1 <;> ring
        have strict : 2*h-ny*b C.side C.c C.s (C.loV+C.side)-
            (C.side/2)*(1+h^2+h*ny)<upper C (-h) ny := by
          rw [upperFormula]
          exact sub_pos.mp margin
        exact (not_lt_of_ge sep') (outerBound.trans_lt strict)
  have flip (nx ny : ℝ) (sep : upper L nx ny≤lower C nx ny) :
      upper C (-nx) (-ny)≤lower L (-nx) (-ny) := by
    rw [(C1092MixedCornerSupports.negative_support C nx ny).2,
      (C1092MixedCornerSupports.negative_support L nx ny).1]
    exact neg_le_neg sep
  have all := CongruentSAT.faceSeparation_of_disjoint C L same apart
  change pairRadius C L≤|C.c*(centerX L-centerX C)+C.s*(centerY L-centerY C)| ∨
    pairRadius C L≤|-C.s*(centerX L-centerX C)+C.c*(centerY L-centerY C)| ∨
    pairRadius L C≤|L.c*(centerX L-centerX C)+L.s*(centerY L-centerY C)| ∨
    pairRadius L C≤|-L.s*(centerX L-centerX C)+L.c*(centerY L-centerY C)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius L nx ny=radius)
      (sep : radius≤|nx*(centerX L-centerX C)+ny*(centerY L-centerY C)|) :=
    separated C L nx ny (by rwa [identity])
  rcases all with cu | cv | lu | lv
  · have sep := split C.c C.s _ (parallel_radius C L) cu
    rcases sep with forward | reverse
    · have direction := (cone C.c C.s C.unit_normal forward).2
      linarith only [direction,shallow,sp]
    · have direction := (cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (flip _ _ reverse)).1
      linarith only [direction,sp]
  · have sep := split (-C.s) C.c _ (transverse_radius C L) cv
    rcases sep with forward | reverse
    · exact central forward
    · have direction := (cone C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using flip _ _ reverse)).1
      linarith only [direction,cp]
  · have identity : supportRadius C L.c L.s+supportRadius L L.c L.s=pairRadius L C := by
      rw [add_comm]
      exact parallel_radius L C
    have sep := split L.c L.s _ identity lu
    rcases sep with forward | reverse
    · exact boundary L.c L.s L.unit_normal (Or.inl ⟨rfl,rfl⟩) forward
    · exact boundary (-L.c) (-L.s) (by nlinarith only [L.unit_normal])
        (Or.inr (Or.inl ⟨rfl,rfl⟩)) (flip _ _ reverse)
  · have identity : supportRadius C (-L.s) L.c+supportRadius L (-L.s) L.c=pairRadius L C := by
      rw [add_comm]
      exact transverse_radius L C
    have sep := split (-L.s) L.c _ identity lv
    rcases sep with forward | reverse
    · exact boundary (-L.s) L.c (by nlinarith only [L.unit_normal])
        (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))) forward
    · exact boundary L.s (-L.c) (by nlinarith only [L.unit_normal])
        (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))) (by simpa only [neg_neg] using flip _ _ reverse)

/-- The local same-face order theorem. Every point and real wall belongs
to its actual square; no boundary center-sign premise is imposed. -/
theorem order (C B L : OpenSquare) (x : ℝ) (side : 1<C.side)
    (sameB : C.side=B.side) (sameL : C.side=L.side) (data : Data C x)
    (bottomMarker : B.Inside 0 (-543/500)) (bottomOuter : B.Inside (-2/5) (-1))
    (bottomWall : ∀ u v, B.Inside u v → -2≤v)
    (leftMarker : L.Inside (-543/500) 0) (leftOrigin : L.Inside (-1) 0)
    (leftWall : ∀ u v, L.Inside u v → -2≤u)
    (apartB : ∀ u v, ¬(C.Inside u v ∧ B.Inside u v))
    (apartL : ∀ u v, ¬(C.Inside u v ∧ L.Inside u v)) :
    0<centerX B+centerY L := by
  have bottom := bottom_order C B x side sameB data bottomMarker bottomOuter bottomWall apartB
  have left := left_order C L x side sameL data leftMarker leftOrigin leftWall apartL
  linarith only [bottom,left]

#print axioms order
end N12Compact.C1092ShallowWallOrder
