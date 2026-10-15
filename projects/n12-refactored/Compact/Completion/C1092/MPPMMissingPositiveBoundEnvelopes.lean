import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesBottom

/-! The second actual boundary envelope and the strict same-face center
sum, completing MISSING-POSITIVE-BOUNDARIES Theorem 2 and Corollary 3.
The preceding origin is strict in its actual left square. Both real walls
and all actual square normals are retained, including weak contact.
Written source only; compilation remains separate. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowBoundarySupport C1092ShallowCentralScalars
set_option Elab.async false

theorem left_order (C L : OpenSquare) (side : 1<C.side) (cap : C.side≤1001/1000)
    (same : C.side=L.side) (d : Data C)
    (marker : L.Inside (-543/500) 0) (origin : L.Inside (-1) 0)
    (wall : ∀ x y,L.Inside x y→-2≤x)
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    ell C.side C.c C.s (C.loV+C.side)≤centerY L := by
  classical
  apply le_of_not_gt
  intro below
  have p := profile C side d
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp := p.positive
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower L nx ny) : 0<ny ∧ nx<(175/368)*ny := by
    have a := (strict_bounds C _ _ nx ny unit d.ordinaryP).2
    have b := (strict_bounds L _ _ nx ny unit origin).1
    have c := (strict_bounds C _ _ nx ny unit d.marker).2
    have e := (strict_bounds L _ _ nx ny unit marker).1
    constructor <;> linarith only [a,b,c,e,sep]
  have central : ¬upper C (-C.s) C.c≤lower L (-C.s) C.c := by
    intro sep
    have horizontal := left_center L wall
    have width := (width_bounds L d.normal).2
    rw [←same] at horizontal width
    have horizontalWeight := mul_nonneg sp.le (sub_nonneg.mpr horizontal)
    have widthGap := sub_nonneg.mpr width
    have strict := mul_pos cp (sub_pos.mpr below)
    have coordinate : C.c*ell C.side C.c C.s (C.loV+C.side)=
        (C.loV+C.side)-2*C.s+(C.side/2)*(1+C.s*(C.c+C.s)) := by
      dsimp [ell]; field_simp [cp.ne']
    have identity : (C.loV+C.side)-lower L (-C.s) C.c=
        C.c*(ell C.side C.c C.s (C.loV+C.side)-centerY L)+
        C.s*(centerX L+2-C.side*width0 L/2)+
        (C.s*(C.side*width0 L/2)+supportRadius L (-C.s) C.c-
          C.side*(1+C.s*(C.c+C.s))/2) := by
      dsimp [lower]; linear_combination -coordinate
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
    have lp : 0<lambda := add_pos_of_nonneg_of_pos (mul_nonneg cp.le east) (mul_pos sp direction.1)
    have mp : 0<mu := by
      have first := mul_nonneg (sub_nonneg.mpr d.normal.2.1) direction.1.le
      have last := mul_pos sp (show 0<ny-nx by linarith only [direction.1,direction.2])
      dsimp [mu]; nlinarith only [first,last]
    have support := C1092MixedCornerSupports.upper_nn C nx ny lambda mu
      (by dsimp [lambda]; ring) (by dsimp [mu]; ring) lp.le mp.le
    have uWeight := mul_le_mul_of_nonneg_left
      (show C.side-C.c-C.s≤C.loU+C.side by linarith only [p.lowerU]) lp.le
    have vWeight := mul_le_mul_of_nonneg_left
      (show C.side+(14/25)*C.s-C.c≤C.loV+C.side by linarith only [p.lowerV]) mp.le
    have extra := mul_pos (sub_pos.mpr side) (add_pos lp mp)
    have bound : lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)<upper C nx ny := by
      calc
        _ < lambda*(C.side-C.c-C.s)+mu*(C.side+(14/25)*C.s-C.c) := by
          apply sub_pos.mp; convert extra using 1 <;> ring
        _ ≤ lambda*(C.loU+C.side)+mu*(C.loV+C.side) := add_le_add uWeight vWeight
        _ = upper C nx ny := support.symm
    have coefficients := Envelopes.northeast_coefficients C side d
    have first := mul_nonneg east coefficients.2.2.1.le
    have last := mul_pos direction.1 coefficients.2.2.2
    have margin : 0<lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)+nx := by
      have identity : lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c)+nx=
          nx*(C.c-C.s+(11/25)*C.s^2)+ny*(C.c+C.s-1-(11/25)*C.c*C.s) := by
        dsimp [lambda,mu]; linear_combination -(nx+ny)*C.unit_normal
      rw [identity]; exact add_pos_of_nonneg_of_pos first last
    have point := (strict_bounds L _ _ nx ny unit origin).1
    have comparison : nx*(-1)+ny*0<lambda*(1-C.c-C.s)+mu*(1+(14/25)*C.s-C.c) := by
      convert sub_pos.mp margin using 1 <;> ring
    exact (not_lt_of_ge sep) (point.trans (comparison.trans bound))
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal L nx ny)
      (sep : upper C nx ny≤lower L nx ny) : False := by
    by_cases east : 0≤nx
    · exact northeast nx ny unit east sep
    have direction := cone nx ny unit sep
    let h := -nx
    have hp : 0<h := by dsimp [h]; linarith only [east]
    have face' : FaceNormal L (-h) ny := by simpa only [h,neg_neg] using face
    have wallBound := left_face L h ny hp.le direction.1.le wall face'
    rw [←same] at wallBound
    let delta := C.s*ny-C.c*h
    let kappa := C.s*h+C.c*ny
    have kp : 0<kappa := add_pos_of_nonneg_of_pos (mul_nonneg sp.le hp.le) (mul_pos cp direction.1)
    have formula : upper C (-h) ny=delta*(C.loU+C.side)+kappa*(C.loV+C.side)+
        C.side*max (-delta) 0 := by
      by_cases sign : 0≤delta
      · rw [C1092MixedCornerSupports.upper_nn C (-h) ny delta kappa
          (by dsimp [delta]; ring) (by dsimp [kappa]; ring) sign kp.le,
          max_eq_right (by linarith only [sign] : -delta≤0)]; ring
      · have sign' : delta≤0 := (lt_of_not_ge sign).le
        rw [upper_np C (-h) ny delta kappa (by dsimp [delta]; ring)
          (by dsimp [kappa]; ring) sign' kp.le,
          max_eq_left (by linarith only [sign'] : 0≤-delta)]; ring
    have margin := (Envelopes.margins C side cap d h ny hp.le direction.1.le
      (by dsimp [h]; nlinarith only [unit])).2
    have strict := mul_pos direction.1 (sub_pos.mpr below)
    have physical : Envelopes.leftGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h ny+
        ny*(ell C.side C.c C.s (C.loV+C.side)-centerY L)≤upper C (-h) ny-lower L (-h) ny := by
      calc
        _ = upper C (-h) ny-(2*h+ny*centerY L-(C.side/2)*(1+h^2+h*ny)) := by
          rw [formula]
          dsimp [Envelopes.leftGap,delta,kappa]
          rw [show -(C.s*ny-C.c*h)=C.c*h-C.s*ny by ring]
          ring
        _ ≤ _ := sub_le_sub_left wallBound _
    have positive := (add_pos_of_nonneg_of_pos margin strict).trans_le physical
    have sep' : upper C (-h) ny≤lower L (-h) ny := by simpa only [h,neg_neg] using sep
    exact (not_lt_of_ge (sub_nonpos.mpr sep')) positive
  obtain ⟨nx,ny,unit,face,sep⟩ := Envelopes.directed_faces C L same apart
  rcases face with own|foreign
  · rcases own with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,d.normal.2.1,sp]
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,sp]
    · exact central sep
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,cp]
  · exact boundary nx ny unit foreign sep

/-- The local conclusion uses the two envelopes of one and the same
upper-v face K. All literal missing points remain in Data C. -/
theorem order (C B L : OpenSquare) (side : 1<C.side) (cap : C.side≤1001/1000)
    (sameB : C.side=B.side) (sameL : C.side=L.side) (data : Data C)
    (bottomMarker : B.Inside 0 (-543/500)) (bottomOuter : B.Inside (-2/5) (-1))
    (bottomWall : ∀ x y,B.Inside x y→-2≤y)
    (leftMarker : L.Inside (-543/500) 0) (leftOrigin : L.Inside (-1) 0)
    (leftWall : ∀ x y,L.Inside x y→-2≤x)
    (apartB : ∀ x y,¬(C.Inside x y ∧ B.Inside x y))
    (apartL : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    0<centerX B+centerY L := by
  have bottom := bottom_order C B side cap sameB data bottomMarker bottomOuter bottomWall apartB
  have left := left_order C L side cap sameL data leftMarker leftOrigin leftWall apartL
  have p := profile C side data
  have strict := same_face_sum side data.normal p.positive p.upperV
  linarith only [bottom,left,strict]

#print axioms left_order
#print axioms order
end N12Compact.C1092MPPMMissingPositiveBoundaries
